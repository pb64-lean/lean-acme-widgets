import AcmeValid.service
import Acme.Auth
import Grpc

/-!
End-to-end coverage of the generated protected-service boundary without a
database or network transport. The request body is the ordinary protobuf
message. Authentication resolves a shared Principal from headers, generated
code validates the request and method CEL policy, and only then calls a
handler with the private proof-carrying `CreateWidgetCall` capability.
-/

open acme.v1

private def expect (condition : Bool) (failure : String) : IO Unit := do
  unless condition do throw (IO.userError failure)

private def fail (failure : String) : IO α :=
  throw (IO.userError failure)

private def metadata (token : String) : _root_.Http2.Headers :=
  _root_.Http2.Headers.empty.insert "authorization" s!"Bearer {token}"

private def encodeCreate (request : CreateWidgetRequest) : IO ByteArray :=
  match request.encode with
  | .ok bytes => pure bytes
  | .error error => fail s!"request encode failed: {error}"

private def syntheticService : Valid.WidgetService := {
  handleCreateWidget := fun call =>
    pure { widget := some {
      call.request.widget.toBase with
      -- Echo values that can only have come from the server-injected shared
      -- Principal, not from the ordinary CreateWidgetRequest wire message.
      id := call.principal.toBase.id
      description := String.intercalate "+" call.principal.toBase.roles.toList
    } }
  handleGetWidget := fun _ => pure {}
  handleListWidgets := fun _ => pure {}
  handleUpdateWidget := fun _ => pure {}
  handleDeleteWidget := fun _ => pure {}
}

private def expectUnaryHandler (entry : Grpc.MethodEntry)
    (decision : Grpc.AuthorizationResult entry) (description : String) :
    IO Grpc.UnaryHandler := do
  match decision with
  | .reject status =>
      fail s!"{description}: {status.code}: {status.messageD}"
  | .accept handler =>
      let resolved := { entry with handler := handler }
      match resolved.handlerFor? .unary with
      | some unary => pure unary
      | none => fail s!"{description}: resolved handler was not unary"

private def expectHeaderRejection (entry : Grpc.MethodEntry)
    (decision : Grpc.AuthorizationResult entry) (fragment : String)
    (description : String) : IO Unit := do
  match decision with
  | .reject status =>
      expect (status.code == .unauthenticated)
        s!"{description}: expected UNAUTHENTICATED, got {status.code}"
      expect (status.messageD.contains fragment)
        s!"{description}: missing status detail {fragment}"
  | .accept _ => fail s!"{description}: unexpectedly accepted"

private def expectCallError (result : Except Grpc.Status Grpc.UnaryResponse)
    (code : Grpc.Code) (fragment : String) (description : String) :
    IO Unit := do
  match result with
  | .ok _ => fail s!"{description}: unexpectedly succeeded"
  | .error status =>
      expect (status.code == code)
        s!"{description}: expected {code}, got {status.code}"
      expect (status.messageD.contains fragment)
        s!"{description}: missing status detail {fragment}"

private def goodRequest : CreateWidgetRequest := {
  user_id := 7
  widget := some {
    owner_id := 7
    name := "Boundary widget"
    sku := "wgt-7000"
    quantity := 1
  }
}

def main : IO Unit := do
  let authenticator := Acme.Auth.requestAuthenticator Acme.Auth.demoTable
  let registry ← match Valid.WidgetService.register Grpc.Registry.empty
      authenticator syntheticService with
    | .ok registry => pure registry
    | .error duplicate =>
        fail s!"generated registration rejected {duplicate.name.path}"

  -- Full-service preflight is atomic: a conflict at the final method rejects
  -- the batch before any earlier WidgetService entry can be appended.
  let occupied := Grpc.Registry.empty.registerUnary
    WidgetService.DeleteWidgetMethod (fun _ => pure {})
  match Valid.WidgetService.register occupied authenticator syntheticService with
  | .ok _ => fail "duplicate WidgetService registration unexpectedly succeeded"
  | .error duplicate =>
      expect (duplicate.name == WidgetService.DeleteWidgetMethod)
        "duplicate registration reported the wrong method"
      expect (occupied.entries.size == 1)
        "duplicate preflight mutated the input registry"
      expect (occupied.findEntry? WidgetService.CreateWidgetMethod).isNone
        "duplicate preflight partially registered an earlier method"

  let some entry := registry.findEntry? WidgetService.CreateWidgetMethod
    | fail "generated CreateWidget method was not registered"
  let some resolve := registry.pureRequestHeaderAuthorizerFor? entry
    | fail "generated registration did not expose its pure pre-body resolver"

  -- Authentication is a header-stage decision: no request bytes are needed.
  expectHeaderRejection entry (resolve _root_.Http2.Headers.empty)
    "missing authorization" "missing token"
  expectHeaderRejection entry (resolve (metadata "unknown"))
    "unknown bearer token" "unknown token"

  let goodBytes ← encodeCreate goodRequest
  let editorMetadata := metadata "acme-editor-7"
  let editorHandler ← expectUnaryHandler entry (resolve editorMetadata)
    "editor authentication"
  let goodResult ← (editorHandler {
      method := WidgetService.CreateWidgetMethod
      metadata := editorMetadata
      data := goodBytes
    }).run
  let response ← match goodResult with
    | .error status => fail s!"authorized request failed: {status.code}: {status.messageD}"
    | .ok response => pure response
  expect (response.status == Grpc.Status.ok) "authorized response status was not OK"
  let decoded ← match WidgetResponse.decode response.data with
    | .error error => fail s!"response decode failed: {error}"
    | .ok decoded => pure decoded
  expect (decoded.widgetD.id == 7) "handler did not receive authenticated principal id"
  expect (decoded.widgetD.description == "editor")
    "handler did not receive authenticated principal roles"

  -- A known token authenticates at headers, but the generated body handler
  -- evaluates method CEL and rejects missing role or principal/request skew.
  let viewerMetadata := metadata "acme-viewer-7"
  let viewerHandler ← expectUnaryHandler entry (resolve viewerMetadata)
    "viewer authentication"
  expectCallError
    (← (viewerHandler {
      method := WidgetService.CreateWidgetMethod
      metadata := viewerMetadata
      data := goodBytes
    }).run)
    .permissionDenied "authz.create.editor" "viewer method policy"

  let otherMetadata := metadata "acme-editor-8"
  let otherHandler ← expectUnaryHandler entry (resolve otherMetadata)
    "other editor authentication"
  expectCallError
    (← (otherHandler {
      method := WidgetService.CreateWidgetMethod
      metadata := otherMetadata
      data := goodBytes
    }).run)
    .permissionDenied "authz.create.self" "principal/request binding policy"

  -- Message validation remains INVALID_ARGUMENT and precedes method policy.
  let invalidBytes ← encodeCreate { goodRequest with widget := none }
  expectCallError
    (← (editorHandler {
      method := WidgetService.CreateWidgetMethod
      metadata := editorMetadata
      data := invalidBytes
    }).run)
    .invalidArgument "required" "request validation"

  -- Bypassing header resolution cannot reach a protected handler, even with
  -- otherwise valid metadata and body bytes.
  let some rawHandler := entry.handlerFor? .unary
    | fail "generated CreateWidget entry was not unary"
  expectCallError
    (← (rawHandler {
      method := WidgetService.CreateWidgetMethod
      metadata := editorMetadata
      data := goodBytes
    }).run)
    .unauthenticated "without resolving request headers" "raw handler fail-closed"

  IO.println "generated authz boundary: authentication, validation, policy, and capability passed"
