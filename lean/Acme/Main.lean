import Acme.Auth
import Acme.Repo
import Acme.Service
import Lentil
import Grpc
import Pg

/-!
The Acme Widgets server: PostgreSQL through the generated lean-pgx contract
over pg-lean (`ACME_DATABASE_URL`, default the docker-compose instance) + the
gRPC WidgetService (`ACME_LISTEN_PORT`, default 50061) with reflection enabled.
Response compression is opt-in through `ACME_RESPONSE_COMPRESSION`; request
gzip support remains enabled independently.

Composition is Lentil beans: `@[lentil_config]` loads `AcmeConfig` from the
`ACME_` environment prefix, `@[lentil]` recipes build the connection,
repository, token table, and registry, and `make_context` checks the graph at
elaboration time and generates `AcmeContext.build`. Beans construct in
registration order (dependencies first), so the TLS invariant below is
validated before postgres is dialed.

Authentication: WidgetService methods require an `authorization: Bearer
<token>` header, resolved against a token table BEFORE any request body is
read (grpc-lean request-header authorizer). The table comes from
`ACME_BEARER_TOKENS` (`token:id:role_level,...`) or defaults to the built-in
demo table mirroring the e2e principals.

TLS termination: if `ACME_TLS_CERTIFICATE` (DER leaf certificate path) and
`ACME_TLS_SIGNING_KEY` (32-byte raw Ed25519 signing-key path) are set, the
listener serves gRPC over TLS 1.3 (ALPN "h2"); otherwise plaintext h2c. A
partial TLS pair is rejected as a configuration error.

Graceful listener termination: a line on stdin (or EOF) triggers
`Grpc.Server.shutdown`, after which `wait` drains in-flight RPCs and returns.
-/

open Lentil EnvConfig

def defaultDatabaseUrl : String := "postgres://acme@localhost:54398/acme"

/-- Parse the listener port without `UInt16.ofNat`'s modulo wraparound. -/
instance : EnvValue UInt16 where
  parse raw := do
    let value ← EnvValue.parse (α := Nat) raw
    if h : value < UInt16.size then
      return UInt16.ofNatLT value h
    else
      throw s!"expected a TCP port from 0 through 65535, got {repr raw}"

/-- Parse and validate the bearer-token table at the configuration boundary. -/
instance : EnvValue Acme.Auth.TokenTable where
  parse := Acme.Auth.TokenTable.parse

/-- All process-level Acme settings. Field names derive the `ACME_*` keys. -/
@[lentil_config "ACME_"]
structure AcmeConfig where
  databaseUrl : String := defaultDatabaseUrl
  listenPort : UInt16 := 50061
  responseCompression : Bool := false
  bearerTokens : Option Acme.Auth.TokenTable
  tlsCertificate : Option System.FilePath
  tlsSigningKey : Option System.FilePath

/-- Validate the cross-field TLS invariant before any startup side effects. -/
def AcmeConfig.tlsFiles (cfg : AcmeConfig) :
    Validated (Option (System.FilePath × System.FilePath)) :=
  match cfg.tlsCertificate, cfg.tlsSigningKey with
  | none, none => .ok none
  | some certificate, some signingKey => .ok (some (certificate, signingKey))
  | some _, none =>
    .errors #["ACME_TLS_SIGNING_KEY: must be set when ACME_TLS_CERTIFICATE is set"]
  | none, some _ =>
    .errors #["ACME_TLS_CERTIFICATE: must be set when ACME_TLS_SIGNING_KEY is set"]

/-- The TLS listener material once the pair invariant holds: both files, or
plaintext. `deriving FromEnv` cannot express cross-field validation, so this
is a bean derived from `AcmeConfig` rather than part of it. -/
structure TlsFiles where
  files : Option (System.FilePath × System.FilePath)

@[lentil] def tlsFiles (cfg : AcmeConfig) : IO TlsFiles :=
  TlsFiles.mk <$> cfg.tlsFiles.toIO

@[lentil] def connection (cfg : AcmeConfig) : IO Pg.Connection := do
  let conn ← (Pg.connectUri cfg.databaseUrl).block
  IO.println s!"connected to postgres ({(← (conn.parameter? "server_version").block).getD "?"})"
  pure conn

@[lentil] def repository (conn : Pg.Connection) : IO Acme.Repo.Repo := do
  match ← Acme.Repo.open' conn with
  | .ok repo => pure repo
  | .error e => throw (IO.userError s!"repository init: {e}")

/-- The effective bearer-token table: configured, or the built-in demo one. -/
@[lentil] def tokenTable (cfg : AcmeConfig) : IO Acme.Auth.TokenTable := do
  match cfg.bearerTokens with
  | some table =>
    IO.println "auth: bearer-token table from ACME_BEARER_TOKENS"
    pure table
  | none =>
    IO.println "auth: built-in demo bearer-token table"
    pure Acme.Auth.demoTable

@[lentil] def registry (cfg : AcmeConfig) (repo : Acme.Repo.Repo)
    (table : Acme.Auth.TokenTable) : Grpc.Registry :=
  Acme.Service.registry repo table
    |>.withResponseCompression cfg.responseCompression

@[lentil] def serverConfig (cfg : AcmeConfig) : Grpc.Server.Config :=
  { address := Grpc.Server.anyIPv4 cfg.listenPort }

validate_beans
make_context AcmeContext

/-- Wait for a shutdown trigger (a stdin line or EOF), then stop the listener
and drain. Runs in its own task so the main thread can `wait`. -/
def shutdownOnStdin (server : Grpc.Server.Instance) : IO Unit := do
  let stdin ← IO.getStdin
  let _ ← stdin.getLine   -- returns "" on EOF
  IO.eprintln "acme-widgets: shutting down listener"
  Grpc.Server.shutdown server

def main : IO Unit := do
  let context ← AcmeContext.build
  let server ← match context.tlsFiles.files with
    | some (certificatePath, signingKeyPath) =>
      let certDer ← IO.FS.readBinFile certificatePath
      let signingKey ← IO.FS.readBinFile signingKeyPath
      IO.println "transport: TLS 1.3 (ALPN h2)"
      Grpc.Server.serveTls context.registry
        { certificateChain := #[certDer], signingKey } context.serverConfig
    | none =>
      IO.println "transport: plaintext h2c"
      Grpc.Server.serve context.registry context.serverConfig
  IO.println s!"acme-widgets listening on {server.localAddress}"
  (← IO.getStdout).flush
  let shutdownTask ← IO.asTask (shutdownOnStdin server)
  Grpc.Server.wait server
  -- If the accept loop ended on its own, make sure the stdin watcher is not
  -- left blocking a clean exit.
  IO.cancel shutdownTask
  IO.println "acme-widgets: listener shut down cleanly"
