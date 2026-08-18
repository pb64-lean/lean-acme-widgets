import Acme.Service

/-!
Regression coverage for startup-bound authenticated dispatch.  The synthetic
service uses the generated five-method `WidgetService` registration but never
opens PostgreSQL.  Its responses identify the principal and method whose
handler the installed production authorizer selected.
-/

open acme.v1

private def markerWidget (principal : Acme.Auth.AuthenticatedPrincipal)
    (method : String) : Widget := {
  id := principal.id
  owner_id := principal.id
  name := method
  sku := "dispatch-cache"
  quantity := principal.roleLevel
  description := "synthetic"
}

@[noinline] private def syntheticService
    (principal : Acme.Auth.AuthenticatedPrincipal) : WidgetService := {
  handleCreateWidget := fun _ =>
    pure { widget := some (markerWidget principal "CreateWidget") }
  handleGetWidget := fun _ =>
    pure { widget := some (markerWidget principal "GetWidget") }
  handleListWidgets := fun _ =>
    pure { widgets := #[markerWidget principal "ListWidgets"] }
  handleUpdateWidget := fun _ =>
    pure { widget := some (markerWidget principal "UpdateWidget") }
  handleDeleteWidget := fun _ =>
    pure { deleted := principal.roleLevel == 3 }
}

private def syntheticRegistry
    (principal : Acme.Auth.AuthenticatedPrincipal) : Grpc.Registry :=
  WidgetService.register Grpc.Registry.empty (syntheticService principal)

@[noinline] private def authorizeFromDispatches
    (dispatches : Acme.Auth.TokenTable.Bound Grpc.Registry) :
    Grpc.PureRequestHeaderAuthorizer :=
  fun entry metadata =>
    if entry.name.service != Acme.Service.widgetServiceName then
      .acceptRegistered entry
    else
      match dispatches.authenticate metadata with
      | .error status => .reject status
      | .ok dispatch =>
        match dispatch.findEntry? entry.name with
        | none => .reject (Grpc.Status.internal
            "method missing from authenticated registry")
        | some entry' =>
          match entry'.handlerFor? entry.shape with
          | some handler => .accept handler
          | none => .reject (Grpc.Status.internal "authorizer shape mismatch")

/-- The exact former request shape: rebuild every principal registry before
authenticating each header block.  `noinline` keeps this an honest regression
reference in optimized builds. -/
@[noinline] private def referenceAuthorizer
    (table : Acme.Auth.TokenTable) : Grpc.PureRequestHeaderAuthorizer :=
  fun entry metadata =>
    authorizeFromDispatches (table.bind syntheticRegistry) entry metadata

private def authorizationValues (values : Array String) : Grpc.Metadata :=
  values.foldl (fun metadata value => metadata.insert "authorization" value)
    Grpc.Metadata.empty

private def sameOutcome {entry : Grpc.MethodEntry}
    (left right : Grpc.AuthorizationResult entry) : Bool :=
  match left, right with
  | .accept _, .accept _ => true
  | .reject l, .reject r => l == r
  | _, _ => false

/-- Stable handler identity is the runtime regression gate for the cache:
the installed callback must return the same startup-registered closure, while
the former rebuild reference must return a fresh registered closure. -/
private unsafe def sameAcceptedHandler {entry : Grpc.MethodEntry}
    (left right : Grpc.AuthorizationResult entry) : Bool :=
  match left, right with
  | .accept leftHandler, .accept rightHandler => ptrEq leftHandler rightHandler
  | _, _ => false

private def acceptedData {entry : Grpc.MethodEntry} (metadata : Grpc.Metadata)
    (result : Grpc.AuthorizationResult entry) : IO ByteArray := do
  match result with
  | .reject status =>
      throw (IO.userError s!"{entry.name.method}: unexpectedly rejected: {repr status}")
  | .accept handler =>
      if hshape : entry.shape = .unary then
        let unary : Grpc.UnaryHandler :=
          cast (congrArg Grpc.Handler hshape) handler
        match ← (unary {
            method := entry.name
            metadata := metadata
            data := ByteArray.empty
          }).run with
        | .ok response =>
          unless response.status == Grpc.Status.ok do
            throw (IO.userError s!"{entry.name.method}: handler returned {repr response.status}")
          pure response.data
        | .error status =>
          throw (IO.userError s!"{entry.name.method}: handler failed: {repr status}")
      else
        throw (IO.userError s!"{entry.name.method}: expected unary handler")

private structure ExpectedPrincipal where
  token : String
  id : UInt64
  roleLevel : UInt32

private def expectedData (principal : ExpectedPrincipal) (method : String) :
    IO ByteArray := do
  let marker : Widget := {
    id := principal.id
    owner_id := principal.id
    name := method
    sku := "dispatch-cache"
    quantity := principal.roleLevel
    description := "synthetic"
  }
  let encoded := match method with
    | "CreateWidget" | "GetWidget" | "UpdateWidget" =>
      WidgetResponse.encode { widget := some marker }
    | "ListWidgets" => ListWidgetsResponse.encode { widgets := #[marker] }
    | "DeleteWidget" =>
      DeleteWidgetResponse.encode { deleted := principal.roleLevel == 3 }
    | _ => WidgetResponse.encode {}
  match encoded with
  | .ok data => pure data
  | .error error => throw (IO.userError s!"{method}: fixture encode failed: {error}")

private structure FailureFixture where
  label : String
  metadata : Grpc.Metadata
  detail : String

private def checkFailure (fixture : FailureFixture) (entry : Grpc.MethodEntry)
    (result : Grpc.AuthorizationResult entry) : IO Unit := do
  match result with
  | .reject status =>
      unless status.code == .unauthenticated && status.messageD == fixture.detail do
        throw (IO.userError s!"{fixture.label}/{entry.name.method}: wrong status {repr status}")
  | .accept _ =>
      throw (IO.userError s!"{fixture.label}/{entry.name.method}: unexpectedly accepted")

unsafe def main : IO Unit := do
  let table := Acme.Auth.demoTable
  let registry := Acme.Service.registryWithServiceFactory table syntheticService
  let some candidate := registry.pureRequestHeaderAuthorizer?
    | throw (IO.userError "synthetic registry has no pure authorizer")
  let reference := referenceAuthorizer table
  let widgetEntries := registry.entries.filter fun entry =>
    entry.name.service == Acme.Service.widgetServiceName
  unless widgetEntries.size == 5 do
    throw (IO.userError s!"expected 5 WidgetService entries, got {widgetEntries.size}")
  let expectedMethods :=
    #["CreateWidget", "GetWidget", "ListWidgets", "UpdateWidget", "DeleteWidget"]
  let actualMethods := widgetEntries.map (·.name.method)
  unless expectedMethods.all actualMethods.contains &&
      actualMethods.all expectedMethods.contains do
    throw (IO.userError "WidgetService method set changed")

  let principals : Array ExpectedPrincipal := #[
    { token := "acme-editor-7", id := 7, roleLevel := 2 },
    { token := "acme-viewer-7", id := 7, roleLevel := 1 },
    { token := "acme-admin-99", id := 99, roleLevel := 3 },
    { token := "acme-editor-8", id := 8, roleLevel := 2 }]
  for principal in principals do
    let metadata := authorizationValues #["Bearer " ++ principal.token]
    let probeMetadata := metadata.insert "x-dispatch-cache-probe" "1"
    for entry in widgetEntries do
      let expected := reference entry metadata
      let actual := candidate entry metadata
      unless sameOutcome expected actual do
        throw (IO.userError s!"{principal.token}/{entry.name.method}: differs from rebuild reference")
      unless sameAcceptedHandler actual (candidate entry probeMetadata) do
        throw (IO.userError s!"{principal.token}/{entry.name.method}: cached handler identity changed")
      if sameAcceptedHandler expected (reference entry probeMetadata) then
        throw (IO.userError s!"{principal.token}/{entry.name.method}: rebuild reference reused a handler")
      let data ← acceptedData metadata actual
      let wanted ← expectedData principal entry.name.method
      unless data == wanted do
        throw (IO.userError s!"{principal.token}/{entry.name.method}: wrong bound handler")

  -- Metadata is multi-valued and authentication deliberately uses the last
  -- authorization value.  Exercise valid, malformed, and unknown tails.
  let duplicateValid := authorizationValues
    #["Bearer acme-editor-7", "Bearer acme-admin-99"]
  let admin : ExpectedPrincipal :=
    { token := "acme-admin-99", id := 99, roleLevel := 3 }
  for entry in widgetEntries do
    let expected := reference entry duplicateValid
    let actual := candidate entry duplicateValid
    unless sameOutcome expected actual do
      throw (IO.userError s!"duplicate-valid/{entry.name.method}: differs from reference")
    let data ← acceptedData duplicateValid actual
    let wanted ← expectedData admin entry.name.method
    unless data == wanted do
      throw (IO.userError s!"duplicate-valid/{entry.name.method}: did not select last header")

  let failures : Array FailureFixture := #[
    { label := "missing", metadata := Grpc.Metadata.empty,
      detail := "missing authorization bearer token" },
    { label := "unknown", metadata := authorizationValues #["Bearer absent"],
      detail := "unknown bearer token" },
    { label := "malformed", metadata := authorizationValues #["Basic acme-admin-99"],
      detail := "missing authorization bearer token" },
    { label := "duplicate-last-malformed",
      metadata := authorizationValues #["Bearer acme-admin-99", "Basic absent"],
      detail := "missing authorization bearer token" },
    { label := "duplicate-last-unknown",
      metadata := authorizationValues #["Bearer acme-admin-99", "Bearer absent"],
      detail := "unknown bearer token" }]
  for fixture in failures do
    for entry in widgetEntries do
      let expected := reference entry fixture.metadata
      let actual := candidate entry fixture.metadata
      unless sameOutcome expected actual do
        throw (IO.userError s!"{fixture.label}/{entry.name.method}: differs from rebuild reference")
      checkFailure fixture entry actual

  -- Non-Widget methods retain the handler already registered for them and
  -- stay open even when no authorization header is present.
  let passthrough : Grpc.MethodEntry := {
    name := { service := "test.open.Service", method := "Ping" }
    shape := .unary
    handler := fun _ => pure { data := ByteArray.empty }
  }
  let expected := reference passthrough Grpc.Metadata.empty
  let actual := candidate passthrough Grpc.Metadata.empty
  unless sameOutcome expected actual do
    throw (IO.userError "non-widget passthrough differs from reference")
  let data ← acceptedData Grpc.Metadata.empty actual
  unless data.isEmpty do
    throw (IO.userError "non-widget passthrough selected the wrong handler")

  -- Cover the actual open registrations as well: both reflection protocols
  -- are bidirectional-streaming entries, and authorization must return each
  -- entry's already-registered handler unchanged.
  let reflectionEntries := registry.entries.filter fun entry =>
    entry.name.service != Acme.Service.widgetServiceName
  unless reflectionEntries.size == 2 do
    throw (IO.userError s!"expected 2 reflection entries, got {reflectionEntries.size}")
  for methodName in #[Grpc.Services.Reflection.v1MethodName,
      Grpc.Services.Reflection.v1alphaMethodName] do
    let some entry := registry.findEntry? methodName
      | throw (IO.userError s!"missing reflection method {methodName.service}/{methodName.method}")
    unless entry.shape == .bidirectionalStreamingStream do
      throw (IO.userError s!"{methodName.service}/{methodName.method}: wrong reflection shape")
    match candidate entry Grpc.Metadata.empty with
    | .reject status =>
      throw (IO.userError s!"{entry.name.service}/{entry.name.method}: reflection rejected: {repr status}")
    | .accept handler =>
      unless ptrEq handler entry.handler do
        throw (IO.userError s!"{entry.name.service}/{entry.name.method}: reflection handler changed")

  IO.println "startup-bound dispatch: 4 tokens × 5 methods plus auth failures passed"
