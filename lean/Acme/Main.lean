import Acme.Auth
import Acme.Repo
import Acme.Service
import Config.Config
import Grpc
import Pg

/-!
The Acme Widgets server: PostgreSQL through the generated lean-pgx contract
over pg-lean (`ACME_DATABASE_URL`, default the docker-compose instance) + the
gRPC WidgetService (`ACME_LISTEN_PORT`, default 50061) with reflection enabled.

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

open EnvConfig

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
structure AcmeConfig where
  databaseUrl : String := defaultDatabaseUrl
  listenPort : UInt16 := 50061
  bearerTokens : Option Acme.Auth.TokenTable
  tlsCertificate : Option System.FilePath
  tlsSigningKey : Option System.FilePath
  deriving FromEnv

instance : EnvPrefix AcmeConfig := ⟨"ACME_"⟩

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

/-- Wait for a shutdown trigger (a stdin line or EOF), then stop the listener
and drain. Runs in its own task so the main thread can `wait`. -/
def shutdownOnStdin (server : Grpc.Server.Instance) : IO Unit := do
  let stdin ← IO.getStdin
  let _ ← stdin.getLine   -- returns "" on EOF
  IO.eprintln "acme-widgets: shutting down listener"
  Grpc.Server.shutdown server

def main : IO Unit := do
  let cfg ← loadConfig AcmeConfig
  let tlsFiles ← cfg.tlsFiles.toIO
  let conn ← (Pg.connectUri cfg.databaseUrl).block
  let repo ← match ← Acme.Repo.open' conn with
    | .ok repo => pure repo
    | .error e => throw (IO.userError s!"repository init: {e}")
  IO.println s!"connected to postgres ({(← (conn.parameter? "server_version").block).getD "?"})"
  let table ← match cfg.bearerTokens with
    | some table =>
      IO.println "auth: bearer-token table from ACME_BEARER_TOKENS"
      pure table
    | none =>
      IO.println "auth: built-in demo bearer-token table"
      pure Acme.Auth.demoTable
  let registry := Acme.Service.registry repo table
  let serverConfig : Grpc.Server.Config := { address := Grpc.Server.anyIPv4 cfg.listenPort }

  let server ← match tlsFiles with
    | some (certificatePath, signingKeyPath) =>
      let certDer ← IO.FS.readBinFile certificatePath
      let signingKey ← IO.FS.readBinFile signingKeyPath
      IO.println "transport: TLS 1.3 (ALPN h2)"
      Grpc.Server.serveTls registry
        { certificateChain := #[certDer], signingKey } serverConfig
    | none =>
      IO.println "transport: plaintext h2c"
      Grpc.Server.serve registry serverConfig

  IO.println s!"acme-widgets listening on {server.localAddress}"
  (← IO.getStdout).flush
  let shutdownTask ← IO.asTask (shutdownOnStdin server)
  Grpc.Server.wait server
  -- If the accept loop ended on its own, make sure the stdin watcher is not
  -- left blocking a clean exit.
  IO.cancel shutdownTask
  IO.println "acme-widgets: listener shut down cleanly"
