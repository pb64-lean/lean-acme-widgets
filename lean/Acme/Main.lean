import Acme.Auth
import Acme.Repo
import Acme.Service
import Grpc
import Pg

/-!
The Acme Widgets server: PostgreSQL through the generated lean-pgx contract
over pg-lean (`PG_URL`, default the docker-compose instance) + the gRPC
WidgetService (port from argv, default 50061) with reflection enabled.

Authentication: WidgetService methods require an `authorization: Bearer
<token>` header, resolved against a token table BEFORE any request body is
read (grpc-lean request-header authorizer). The table comes from
`ACME_AUTH_TOKENS` (`token:id:role_level,...`) or defaults to the built-in
demo table mirroring the e2e principals.

TLS termination: if `ACME_TLS_CERT` (DER leaf certificate) and `ACME_TLS_KEY`
(32-byte raw Ed25519 signing key) are set, the listener serves gRPC over
TLS 1.3 (ALPN "h2"); otherwise plaintext h2c.

Graceful listener termination: a line on stdin (or EOF) triggers
`Grpc.Server.shutdown`, after which `wait` drains in-flight RPCs and returns.
-/

def defaultPgUrl : String := "postgres://acme@localhost:54398/acme"

/-- Wait for a shutdown trigger (a stdin line or EOF), then stop the listener
and drain. Runs in its own task so the main thread can `wait`. -/
def shutdownOnStdin (server : Grpc.Server.Instance) : IO Unit := do
  let stdin ← IO.getStdin
  let _ ← stdin.getLine   -- returns "" on EOF
  IO.eprintln "acme-widgets: shutting down listener"
  Grpc.Server.shutdown server

def main (args : List String) : IO Unit := do
  let pgUrl := (← IO.getEnv "PG_URL").getD defaultPgUrl
  let port := match args with
    | p :: _ => UInt16.ofNat (p.toNat?.getD 50061)
    | [] => 50061
  let conn ← (Pg.connectUri pgUrl).block
  let repo ← match ← Acme.Repo.open' conn with
    | .ok repo => pure repo
    | .error e => throw (IO.userError s!"repository init: {e}")
  IO.println s!"connected to postgres ({(← (conn.parameter? "server_version").block).getD "?"})"
  let table ← match ← IO.getEnv "ACME_AUTH_TOKENS" with
    | some spec =>
      match Acme.Auth.TokenTable.parse spec with
      | .ok table =>
        IO.println "auth: bearer-token table from ACME_AUTH_TOKENS"
        pure table
      | .error e => throw (IO.userError s!"ACME_AUTH_TOKENS: {e}")
    | none =>
      IO.println "auth: built-in demo bearer-token table"
      pure Acme.Auth.demoTable
  let registry := Acme.Service.registry repo table
  let config : Grpc.Server.Config := { address := Grpc.Server.anyIPv4 port }

  let tlsCert? ← IO.getEnv "ACME_TLS_CERT"
  let tlsKey? ← IO.getEnv "ACME_TLS_KEY"
  let server ← match tlsCert?, tlsKey? with
    | some certPath, some keyPath =>
      let certDer ← IO.FS.readBinFile certPath
      let signingKey ← IO.FS.readBinFile keyPath
      IO.println "transport: TLS 1.3 (ALPN h2)"
      Grpc.Server.serveTls registry
        { certificateChain := #[certDer], signingKey } config
    | _, _ =>
      IO.println "transport: plaintext h2c"
      Grpc.Server.serve registry config

  IO.println s!"acme-widgets listening on {server.localAddress}"
  (← IO.getStdout).flush
  let shutdownTask ← IO.asTask (shutdownOnStdin server)
  Grpc.Server.wait server
  -- If the accept loop ended on its own, make sure the stdin watcher is not
  -- left blocking a clean exit.
  IO.cancel shutdownTask
  IO.println "acme-widgets: listener shut down cleanly"
