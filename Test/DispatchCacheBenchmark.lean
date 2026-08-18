import Acme.Service

/-!
Deterministic no-Pg comparison of the former per-request dispatch rebuild and
the installed startup-bound callback.  Select one generated WidgetService
method per process and run the resulting callback under an instruction
counter.  The prebound registry is assembled before the measured loop.
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

@[noinline] private def syntheticRegistry
    (principal : Acme.Auth.AuthenticatedPrincipal) : Grpc.Registry :=
  WidgetService.register Grpc.Registry.empty (syntheticService principal)

/-- Exact former request shape.  This function's optimized C must retain one
`TokenTable.bind` call, making every invocation rebuild all four registries. -/
@[noinline] private def rebuildAuthorize (table : Acme.Auth.TokenTable)
    (entry : Grpc.MethodEntry) (metadata : Grpc.Metadata) :
    Grpc.AuthorizationResult entry :=
  let dispatches := table.bind syntheticRegistry
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

private def authorizationMetadata : Grpc.Metadata :=
  Grpc.Metadata.empty.insert "authorization" "Bearer acme-editor-8"

private def methodName? : String → Option String
  | "create" => some "CreateWidget"
  | "get" => some "GetWidget"
  | "list" => some "ListWidgets"
  | "update" => some "UpdateWidget"
  | "delete" => some "DeleteWidget"
  | _ => none

private def parsePositive (value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError "iterations must be a positive decimal integer")
  unless parsed > 0 do
    throw (IO.userError "iterations must be positive")
  pure parsed

@[noinline] private def runIterations
    (authorize : Grpc.PureRequestHeaderAuthorizer)
    (entry : Grpc.MethodEntry) (metadata : Grpc.Metadata)
    (iterations : Nat) : IO UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    match authorize entry metadata with
    | .accept _ =>
      checksum := checksum + UInt64.ofNat (entry.name.method.utf8ByteSize + 1)
    | .reject status =>
      throw (IO.userError s!"benchmark authorization failed: {repr status}")
  pure checksum

def main (args : List String) : IO Unit := do
  let (mode, methodArg, iterations) ← match args with
    | [mode, methodArg, iterations] =>
      pure (mode, methodArg, ← parsePositive iterations)
    | _ => throw (IO.userError
        "usage: dispatch_cache_benchmark (rebuild|prebound) (create|get|list|update|delete) iterations")
  unless mode == "rebuild" || mode == "prebound" do
    throw (IO.userError "mode must be rebuild or prebound")
  let some methodName := methodName? methodArg
    | throw (IO.userError "unknown method; expected create|get|list|update|delete")

  let table := Acme.Auth.demoTable
  -- Candidate construction is deliberately outside `runIterations`.
  let candidateRegistry :=
    Acme.Service.registryWithServiceFactory table syntheticService
  let some prebound := candidateRegistry.pureRequestHeaderAuthorizer?
    | throw (IO.userError "candidate registry has no pure authorizer")
  let some entry := candidateRegistry.entries.find? fun entry =>
      entry.name.service == Acme.Service.widgetServiceName &&
        entry.name.method == methodName
    | throw (IO.userError s!"candidate registry missing {methodName}")
  let metadata := authorizationMetadata

  -- Untimed semantic control for the selected method.
  match rebuildAuthorize table entry metadata, prebound entry metadata with
  | .accept _, .accept _ => pure ()
  | .reject left, .reject right =>
    unless left == right do
      throw (IO.userError "rebuild and prebound controls returned different statuses")
  | _, _ => throw (IO.userError "rebuild and prebound controls disagree")

  let authorize : Grpc.PureRequestHeaderAuthorizer :=
    if mode == "rebuild" then rebuildAuthorize table else prebound
  let checksum ← runIterations authorize entry metadata iterations
  IO.println s!"mode={mode} method={methodArg} iterations={iterations} checksum={checksum}"
