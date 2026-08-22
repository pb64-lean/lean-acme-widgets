import Acme.Auth
import Acme.Repo
import Acme.Service
import AcmeLean.widgets
import Grpc
import Pg

/-!
End-to-end over TLS 1.3, in one process: our WidgetService served via
`Grpc.Server.serveTls` and called by the grpc-lean Lean client via
`Client.connectTls`. Proves the full path — Lean gRPC client → TLS →
Lean gRPC server → bearer authentication (pre-body request-header
authenticator) → request validation → generated method-level authorization →
proof-carrying lean-pgx repository over pg-lean — plus graceful listener
termination. The authenticated Principal is never supplied on the wire.

Env: ACME_DATABASE_URL, ACME_TLS_CERTIFICATE (DER leaf), ACME_TLS_SIGNING_KEY
(32-byte Ed25519 seed), ACME_TLS_PEM (leaf PEM, the client's trust anchor).
-/

open acme.v1
open Std.Async

def expect (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

def env! (name : String) : IO String := do
  match ← IO.getEnv name with
  | some v => pure v
  | none => throw (IO.userError s!"{name} not set")

def encode! (r : Except Protobuf.Encoding.ProtoError ByteArray) : IO ByteArray := do
  match r with
  | .ok bytes => pure bytes
  | .error e => throw (IO.userError s!"encode: {e.toString}")

def widget (ownerId : UInt64) : Widget :=
  { id := 0, owner_id := ownerId, name := "TLS widget", sku := "wgt-7000",
    quantity := 3, description := "" }

def createRequest (userId : UInt64) : CreateWidgetRequest :=
  { user_id := userId, widget := some (widget userId) }

def main : IO Unit := do
  let pgUrl := (← IO.getEnv "ACME_DATABASE_URL").getD
    "postgres://acme@localhost:54398/acme"
  let conn ← (Pg.connectUri pgUrl).block
  let repo ← match ← Acme.Repo.open' conn with
    | .ok repo => pure repo
    | .error e => throw (IO.userError s!"repo: {e}")

  let certDer ← IO.FS.readBinFile (← env! "ACME_TLS_CERTIFICATE")
  let signingKey ← IO.FS.readBinFile (← env! "ACME_TLS_SIGNING_KEY")
  let certPem ← IO.FS.readFile (← env! "ACME_TLS_PEM")

  let registry ← Acme.Service.registry
    (Acme.Auth.requestAuthenticator Acme.Auth.demoTable)
    (Acme.Service.widgetService repo)
  let server ← Grpc.Server.serveTls registry
    { certificateChain := #[certDer], signingKey }
    { address := Grpc.Server.loopback 0 }
  let port := match server.localAddress with
    | .v4 a => a.port
    | .v6 a => a.port
  IO.println s!"acme-widgets serving TLS on 127.0.0.1:{port}"

  let client ← Grpc.Client.connectTls
    { address := Grpc.Server.loopback port }
    { serverName := some "localhost", trustAnchorsPEM := some certPem }

  let path := "/acme.v1.WidgetService/CreateWidget"
  let bearer (token : String) : Grpc.Client.CallOptions :=
    { metadata := Grpc.Metadata.empty.insert "authorization" s!"Bearer {token}" }

  -- editor creating its own widget: authenticated + authorized, persisted
  let okBytes ← encode! (createRequest 7).encode
  match ← Async.block (Grpc.Client.call client path okBytes (bearer "acme-editor-7")) with
  | .error status => throw (IO.userError s!"authorized create failed: {status.messageD}")
  | .ok (_, respBytes) =>
    match WidgetResponse.decode respBytes with
    | .ok resp =>
      match resp.widget with
      | some w =>
        expect (w.id > 0) "server assigned a widget id over TLS"
        expect (w.sku == "wgt-7000") "widget roundtripped over TLS"
        IO.println s!"TLS create ok: widget id {w.id}"
      | none => throw (IO.userError "response had no widget")
    | .error e => throw (IO.userError s!"decode response: {e.toString}")

  -- no bearer token: rejected UNAUTHENTICATED at request headers (pre-body)
  match ← Async.block (Grpc.Client.call client path okBytes) with
  | .ok _ => throw (IO.userError "unauthenticated create should have been rejected")
  | .error status =>
    expect (status.code == Grpc.Code.unauthenticated)
      s!"expected Unauthenticated, got {repr status.code}"
    IO.println s!"TLS unauthenticated rejection ok: {status.messageD}"

  -- Viewer: role-membership policy denied, surfaced as PERMISSION_DENIED.
  match ← Async.block (Grpc.Client.call client path okBytes (bearer "acme-viewer-7")) with
  | .ok _ => throw (IO.userError "viewer create should have been denied over TLS")
  | .error status =>
    expect (status.code == Grpc.Code.permissionDenied)
      s!"expected PermissionDenied, got {repr status.code}"
    IO.println s!"TLS authz denial ok: {status.messageD}"

  -- Principal 8 asks to create for user 7. Only the token determines the
  -- principal, so the generated authz.create.self policy must deny the call.
  match ← Async.block (Grpc.Client.call client path okBytes (bearer "acme-editor-8")) with
  | .ok _ => throw (IO.userError "cross-principal create should have been denied")
  | .error status =>
    expect (status.code == Grpc.Code.permissionDenied) "cross-principal PermissionDenied"
    IO.println "TLS cross-principal denial ok"

  (Grpc.Client.close client).block
  -- graceful listener termination
  Grpc.Server.shutdown server
  Grpc.Server.wait server
  IO.println "TLS gRPC end-to-end + graceful shutdown: all assertions passed"
