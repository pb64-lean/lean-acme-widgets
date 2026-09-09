import Acme.Auth
import Acme.Repo
import Acme.Service
import Acme.Lifecycle
import Lentil
import Lentil.Signals
import Grpc
import Grpc.Services.Health
import Grpc.Services.StandardDescriptors
import Pg

/-!
The Acme Widgets server: PostgreSQL through the generated lean-pgx contract
over pg-lean (`ACME_DATABASE_URL`, default the docker-compose instance) + the
gRPC WidgetService (`ACME_LISTEN_PORT`, default 50061) with reflection enabled.
Response compression is opt-in through `ACME_RESPONSE_COMPRESSION`; request
gzip support remains enabled independently.

Composition is Lentil beans: `@[lentil_config]` loads `AcmeConfig` from the
`ACME_` environment prefix; `@[lentil]` recipes build the connection,
repository, token table, request authenticator, WidgetService, registry,
server configuration, and terminal server instance; `make_managed_context`
checks the graph and generates an owned `AcmeContext.build`. The
connection's explicit `TlsFiles` dependency keeps the TLS invariant below
validated before postgres is dialed even though component recipes arrive
through transitive imports.

Authentication: WidgetService methods require an `authorization: Bearer
<token>` header, resolved against a token table BEFORE any request body is
read (the generated method-local request authenticator). The table comes from
`ACME_BEARER_TOKENS` (`token:id:[role[+role...]],...`) or defaults to the built-in
demo table mirroring the e2e principals.

TLS termination: if `ACME_TLS_CERTIFICATE` (DER leaf certificate path) and
`ACME_TLS_SIGNING_KEY` (32-byte raw Ed25519 signing-key path) are set, the
listener serves gRPC over TLS 1.3 (ALPN "h2"); otherwise plaintext h2c. A
partial TLS pair is rejected as a configuration error.

Graceful listener termination: SIGINT or SIGTERM drops readiness, stops
admission, joins the server wait task, and releases PostgreSQL last. Stdin
is not watched: cancelling a blocking stdin read cannot provide joined cleanup.
-/

open Lentil EnvConfig

/- Register the imported application factories at the executable composition
root. `Acme.Auth` and `Acme.Service` are `module` libraries and therefore
cannot import Lentil's non-module elaboration facade themselves. -/
attribute [lentil] Acme.Auth.requestAuthenticator
attribute [lentil] Acme.Service.widgetService
attribute [lentil] Acme.Service.registryCore

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

@[lentil_managed] def terminationSignals : IO (Resource TerminationSignals) :=
  TerminationSignals.acquire

@[lentil_managed] def connection (_tlsFiles : TlsFiles) (_signals : TerminationSignals)
    (cfg : AcmeConfig) : IO (Resource Pg.Connection) := do
  let conn ← (Pg.connectUri cfg.databaseUrl).block
  try
    IO.println s!"connected to postgres ({(← (conn.parameter? "server_version").block).getD "?"})"
    return { value := conn, hooks := { release := conn.close.block } }
  catch error =>
    try conn.close.block catch cleanup =>
      throw <| IO.userError s!"{error}; connection cleanup: {cleanup}"
    throw error

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

@[lentil] def serverConfig (cfg : AcmeConfig) : Grpc.Server.Config :=
  { address := Grpc.Server.anyIPv4 cfg.listenPort }

/-- Liveness stays serving while requests drain; readiness is withdrawn before
listener shutdown. Empty-name health follows readiness for standard probes. -/
@[lentil_managed] def health : IO (Resource Grpc.Services.Health.Service) := do
  Acme.Lifecycle.healthResource

/-- Resources are registered dependency-first and cleaned in reversed phases. -/
@[lentil_managed] def server (cfg : AcmeConfig) (tlsFiles : TlsFiles)
    (registry : Grpc.Registry) (serverConfig : Grpc.Server.Config)
    (health : Grpc.Services.Health.Service) : IO (Resource Grpc.Server.Instance) := do
  let registry := health.registerWith (registry.withResponseCompression cfg.responseCompression)
    |> Grpc.Services.Reflection.registerWith { files := Grpc.Services.Health.fileDescriptors }
  let listener ← match tlsFiles.files with
  | some (certificatePath, signingKeyPath) =>
    let certDer ← IO.FS.readBinFile certificatePath
    let signingKey ← IO.FS.readBinFile signingKeyPath
    IO.println "transport: TLS 1.3 (ALPN h2)"
    Grpc.Server.serveTls registry
      { certificateChain := #[certDer], signingKey } serverConfig
  | none =>
    IO.println "transport: plaintext h2c"
    Grpc.Server.serve registry serverConfig
  return { value := listener, hooks := {
    quiesce := Acme.Lifecycle.quiesce health (Grpc.Server.shutdown listener)
    drain := Grpc.Server.wait listener none } }

validate_beans
make_managed_context AcmeContext

def main : IO Unit := do
  let app ← AcmeContext.build
  app.use fun context => do
    let server := context.server
    let waiter ← app.scope.spawn "server wait" (Grpc.Server.wait server none) (pure ())
    Acme.Lifecycle.markReady context.health
    app.scope.markReady
    IO.println s!"acme-widgets listening on {server.localAddress}"
    (← IO.getStdout).flush
    while !(← IO.hasFinished waiter) && (← context.terminationSignals.poll).isNone do
      IO.sleep 20
    IO.eprintln "acme-widgets: shutting down listener"
  IO.println "acme-widgets: listener shut down cleanly"
