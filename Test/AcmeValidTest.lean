import AcmeLean.user
import AcmeLean.widgets
import AcmeValid.user
import AcmeValid.widgets
import AcmeValid.service
import Acme.Auth
import Acme.Repo
import Acme.Service
import Grpc

/-!
Validation and generated method authorization, hermetically: field/message
rules on ordinary requests, method CEL over the shared authenticated Principal,
exact violation/status mapping, startup token validation, and checked database
numeric conversions. There are no wire Principal or Checked* request messages.
-/

open acme.v1

def expect (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

def expectId (r : Except Protovalidate.Violation α) (id : String) (label : String) : IO Unit := do
  let ok := match r with
    | .error e => e.ruleId == id
    | .ok _ => id == ""
  unless ok do
    let got := match r with
      | .error e => toString e
      | .ok _ => "ok"
    let want := if id == "" then "ok" else id
    throw (IO.userError s!"{label}: expected {want}, got {got}")

def goodUser : User :=
  { id := 7, username := "bill_w", email := "bill@acme.example", role := .ROLE_EDITOR }

def goodWidget : Widget :=
  { id := 0, owner_id := 7, name := "Left-handed flange", sku := "wgt-1024",
    quantity := 12, description := "" }

def createReq : CreateWidgetRequest := { user_id := 7, widget := some goodWidget }

/-- Generated policy failures intrinsically map to PERMISSION_DENIED. -/
def expectPolicyStatus (decision : Protovalidate.Decision policy)
    (id : String) (label : String) : IO Unit := do
  match ← (Protovalidate.Authz.authorize decision (fun _ => ())).run with
  | .ok _ => throw (IO.userError s!"{label}: expected {id}, got ok")
  | .error status =>
    expect (status.code == .permissionDenied) s!"{label}: wrong status code"
    expect (status.messageD.contains id) s!"{label}: missing rule id in status"

def main : IO Unit := do
  -- ── field rules ─────────────────────────────────────────────────────────
  expectId (Valid.User.validate goodUser) "" "good user"
  expectId (Valid.User.validate { goodUser with id := 0 }) "uint64.gt" "user id"
  expectId (Valid.User.validate { goodUser with username := "Ab" }) "string.min_len" "short username"
  expectId (Valid.User.validate { goodUser with username := "Bill" }) "string.pattern" "username pattern"
  expectId (Valid.User.validate { goodUser with email := "nope" }) "string.email" "email"
  expectId (Valid.User.validate { goodUser with role := .ROLE_UNSPECIFIED }) "enum.not_in" "unspecified role"
  expectId (Valid.User.validate { goodUser with role := .«Unknown.Value» 9 }) "enum.defined_only" "unknown role"

  expectId (Valid.Widget.validate goodWidget) "" "good widget"
  expectId (Valid.Widget.validate { goodWidget with sku := "wgt-99" }) "string.pattern" "short sku"
  expectId (Valid.Widget.validate { goodWidget with quantity := 2000000 }) "uint32.lte" "quantity cap"
  expectId (Valid.Widget.validate { goodWidget with owner_id := 0 }) "uint64.gt" "ownerless widget"

  -- ── message-level CEL on the plain request ──────────────────────────────
  expectId (Valid.CreateWidgetRequest.validate createReq) "" "good create"
  expectId (Valid.CreateWidgetRequest.validate { createReq with widget := none })
    "required" "create requires widget"
  expectId (Valid.CreateWidgetRequest.validate
      { createReq with widget := some { goodWidget with owner_id := 8 } })
    "create.owner_matches" "owner mismatch"

  -- Request validation remains independent of authentication/authorization.
  let listReq : ListWidgetsRequest := { user_id := 7, page_size := 20 }
  expectId (Valid.ListWidgetsRequest.validate listReq) "" "valid list request"
  expectId (Valid.ListWidgetsRequest.validate { listReq with page_size := 0 })
    "uint32.gt_lt" "page_size floor"
  let updReq : UpdateWidgetRequest :=
    { user_id := 7, widget := some { goodWidget with id := 41 } }
  expectId (Valid.UpdateWidgetRequest.validate updReq) "" "valid update request"
  expectId (Valid.UpdateWidgetRequest.validate
      { updReq with widget := some goodWidget })
    "update.has_id" "update requires widget id"

  -- encode → decodeValid roundtrip through the wire
  match createReq.encode with
  | .error e => throw (IO.userError s!"encode: {e}")
  | .ok bytes =>
    match Valid.CreateWidgetRequest.decodeValid bytes with
    | .ok v => expect (v.toBase.user_id == 7) "decodeValid roundtrip"
    | .error e => throw (IO.userError s!"decodeValid: {e}")

  -- ── authentication: bearer-token table ─────────────────────────────────
  let table := Acme.Auth.demoTable
  let headers (auth? : Option String) : Grpc.Metadata :=
    match auth? with
    | some v => Grpc.Metadata.empty.insert "authorization" v
    | none => Grpc.Metadata.empty
  let authEditor7 ← match Acme.Auth.authenticate table (headers (some "Bearer acme-editor-7")) with
    | .ok p => pure p
    | .error s => throw (IO.userError s!"editor-7 token rejected: {s.messageD}")
  expect (authEditor7.id.val == 7 && authEditor7.roles.val == #["editor"])
    "editor-7 identity"
  let authViewer7 ← match Acme.Auth.authenticate table (headers (some "Bearer acme-viewer-7")) with
    | .ok p => pure p
    | .error s => throw (IO.userError s!"viewer-7 token rejected: {s.messageD}")
  let authEditor8 ← match Acme.Auth.authenticate table (headers (some "Bearer acme-editor-8")) with
    | .ok p => pure p
    | .error s => throw (IO.userError s!"editor-8 token rejected: {s.messageD}")
  let authAdmin99 ← match Acme.Auth.authenticate table (headers (some "Bearer acme-admin-99")) with
    | .ok p => pure p
    | .error s => throw (IO.userError s!"admin-99 token rejected: {s.messageD}")
  let expectUnauthenticated (auth? : Option String) (label : String) : IO Unit := do
    match Acme.Auth.authenticate table (headers auth?) with
    | .ok p => throw (IO.userError
        s!"{label}: unexpectedly authenticated principal {p.id.val}")
    | .error s => expect (s.code == .unauthenticated) s!"{label}: wrong code"
  expectUnauthenticated none "missing header"
  expectUnauthenticated (some "Bearer bogus") "unknown token"
  expectUnauthenticated (some "Basic acme-editor-7") "wrong scheme"

  -- The common generated Principal rules validate server configuration once.
  expect (Acme.Auth.TokenTable.parse "t:7:editor+auditor,u:8:viewer" |>.isOk)
    "valid role-set spec parses"
  expect (!(Acme.Auth.TokenTable.parse "t:0:editor" |>.isOk)) "id 0 rejected"
  expect (!(Acme.Auth.TokenTable.parse "t:7:editor+editor" |>.isOk))
    "duplicate role rejected"
  let noRoleTable ← match Acme.Auth.TokenTable.parse "unprivileged:7:" with
    | .ok parsed => pure parsed
    | .error error => throw (IO.userError s!"empty role set rejected: {error}")
  let noRolePrincipal ← match Acme.Auth.authenticate noRoleTable
      (headers (some "Bearer unprivileged")) with
    | .ok principal => pure principal
    | .error status => throw (IO.userError s!"empty-role token rejected: {status.messageD}")
  expect noRolePrincipal.roles.val.isEmpty "empty role field did not map to #[]"
  expect (!(Acme.Auth.TokenTable.parse "gibberish" |>.isOk)) "malformed spec rejected"

  -- ── generated method policies over (server principal, plain request) ───
  let createV ← match Valid.CreateWidgetRequest.validate createReq with
    | .ok request => pure request
    | .error violation => throw (IO.userError s!"create fixture: {violation}")
  let listV ← match Valid.ListWidgetsRequest.validate listReq with
    | .ok request => pure request
    | .error violation => throw (IO.userError s!"list fixture: {violation}")
  let updateV ← match Valid.UpdateWidgetRequest.validate updReq with
    | .ok request => pure request
    | .error violation => throw (IO.userError s!"update fixture: {violation}")
  let deleteV ← match Valid.DeleteWidgetRequest.validate
      { user_id := 7, widget_id := 41 } with
    | .ok request => pure request
    | .error violation => throw (IO.userError s!"delete fixture: {violation}")

  expectId (Valid.WidgetService.CreateWidgetValidatePolicy authEditor7 createV)
    "" "editor creates for self"
  expectId (Valid.WidgetService.CreateWidgetValidatePolicy authViewer7 createV)
    "authz.create.editor" "viewer cannot create"
  expectId (Valid.WidgetService.CreateWidgetValidatePolicy authEditor8 createV)
    "authz.create.self" "principal 8 cannot create for user 7"
  expectId (Valid.WidgetService.ListWidgetsValidatePolicy authViewer7 listV)
    "" "viewer lists self"
  expectId (Valid.WidgetService.ListWidgetsValidatePolicy authAdmin99 listV)
    "" "admin lists another user"
  expectId (Valid.WidgetService.ListWidgetsValidatePolicy authEditor8 listV)
    "authz.list.self_or_admin" "editor 8 cannot list user 7"
  expectId (Valid.WidgetService.UpdateWidgetValidatePolicy authEditor7 updateV)
    "" "editor updates self"
  expectId (Valid.WidgetService.UpdateWidgetValidatePolicy authViewer7 updateV)
    "authz.update.editor" "viewer cannot update"
  expectId (Valid.WidgetService.UpdateWidgetValidatePolicy authEditor8 updateV)
    "authz.update.self" "editor 8 cannot update for user 7"
  expectId (Valid.WidgetService.DeleteWidgetValidatePolicy authViewer7 deleteV)
    "" "viewer deletes own widget"
  expectId (Valid.WidgetService.DeleteWidgetValidatePolicy authAdmin99 deleteV)
    "" "admin deletes another user's widget"
  expectId (Valid.WidgetService.DeleteWidgetValidatePolicy authEditor8 deleteV)
    "authz.delete.self_or_admin" "editor 8 cannot delete user 7's widget"

  -- Successful policy validation carries proofs that handlers/repositories
  -- can use; failures map directly to PERMISSION_DENIED by the common runtime.
  match Valid.WidgetService.CreateWidgetValidatePolicy authEditor7 createV with
  | .error violation => throw (IO.userError s!"create proof: {violation}")
  | .ok evidence =>
    let _ : authEditor7.toBase.id = createV.toBase.user_id :=
      evidence.proof.authz_create_self
    let _ : "editor" ∈ authEditor7.toBase.roles ∨
        "admin" ∈ authEditor7.toBase.roles :=
      evidence.proof.authz_create_editor
    pure ()
  expectPolicyStatus
    (Valid.WidgetService.CreateWidgetCheckPolicy authEditor8 createV)
    "authz.create.self" "create policy status"
  expectPolicyStatus
    (Valid.WidgetService.CreateWidgetCheckPolicy authViewer7 createV)
    "authz.create.editor" "role policy status"
  expectPolicyStatus
    (Valid.WidgetService.DeleteWidgetCheckPolicy authEditor8 deleteV)
    "authz.delete.self_or_admin" "delete policy status"

  match ← (Protovalidate.Authz.validateRequest Valid.Widget.validate
      { goodWidget with sku := "bogus" }).run with
  | .ok _ => throw (IO.userError "invalid request unexpectedly passed")
  | .error status =>
    expect (status.code == .invalidArgument) "field rule did not map to INVALID_ARGUMENT"
    expect (status.messageD.contains "string.pattern") "field status lost rule id"

  -- ── checked DB conversions ─────────────────────────────────────────────
  expect (Acme.Repo.uint64OfInt "c" (-1) |>.isOk |> not) "negative rejected (uint64)"
  expect (Acme.Repo.uint64OfInt "c" ((2 : Int) ^ 64) |>.isOk |> not) "2^64 rejected"
  expect (Acme.Repo.uint32OfInt "c" ((2 : Int) ^ 32) |>.isOk |> not) "2^32 rejected"
  expect (match Acme.Repo.uint64OfInt "c" 42 with
    | .ok v => v == 42
    | .error _ => false) "in-range uint64 accepted"
  expect (match Acme.Repo.int64OfUInt64 "c" (UInt64.ofNat (2 ^ 63 - 1)) with
    | .ok v => v == Int64.maxValue
    | .error _ => false) "PostgreSQL bigint maximum accepted"
  expect (Acme.Repo.int64OfUInt64 "c" (UInt64.ofNat (2 ^ 63)) |>.isOk |> not)
    "protobuf uint64 above PostgreSQL bigint rejected"
  match Acme.Repo.widgetOfRow 1 7 "Left-handed flange" "wgt-1024" 5 "" with
  | .error e => throw (IO.userError s!"widgetOfRow: {e}")
  | .ok w =>
    expect (w.id == 1 && w.owner_id == 7 && w.quantity == 5) "widgetOfRow fields"
  expect (Acme.Repo.widgetOfRow 1 (-7) "n" "s" 5 "" |>.isOk |> not)
    "negative owner_id rejected"

  -- UPDATE/DELETE avoid a RETURNING row, but their wire completion tags are
  -- accepted only for the exact zero-or-one outcomes promised by the key
  -- predicates. Unexpected verbs, malformed counts, and multi-row results
  -- fail closed as cardinality errors.
  expect (match Acme.Repo.updateAffected { tag := "UPDATE 0" } with
    | .ok affected => !affected
    | .error _ => false) "UPDATE 0 maps to false"
  expect (match Acme.Repo.updateAffected { tag := "UPDATE 1" } with
    | .ok affected => affected
    | .error _ => false) "UPDATE 1 maps to true"
  expect (match Acme.Repo.updateAffected { tag := "UPDATE 2" } with
    | .error (.database (.cardinality expected actual)) =>
      expected == "UPDATE 0 or UPDATE 1" && actual == "UPDATE 2"
    | _ => false) "multi-row UPDATE fails closed"
  expect (match Acme.Repo.updateAffected { tag := "DELETE 1" } with
    | .error (.database (.cardinality _ _)) => true
    | _ => false) "wrong UPDATE verb fails closed"
  expect (match Acme.Repo.deleteAffected { tag := "DELETE 0" } with
    | .ok affected => !affected
    | .error _ => false) "DELETE 0 maps to false"
  expect (match Acme.Repo.deleteAffected { tag := "DELETE 1" } with
    | .ok affected => affected
    | .error _ => false) "DELETE 1 maps to true"
  expect (match Acme.Repo.deleteAffected { tag := "DELETE many" } with
    | .error (.database (.cardinality expected actual)) =>
      expected == "DELETE 0 or DELETE 1" && actual == "DELETE many"
    | _ => false) "malformed DELETE count fails closed"

  -- Generated query rows carry the SQL CHECK proofs needed by the hot-path
  -- mappers. Boundary values are projected exactly, without a second
  -- `Int` range decision in the repository.
  let getRowData : AcmeDb.Queries.GetWidget.RowData :=
    { id := Int64.maxValue
      ownerId := Int64.maxValue
      name := "Get boundary"
      sku := "wgt-9223372036854775807"
      quantity := 4294967295
      description := "proof-projected" }
  match AcmeDb.Queries.GetWidget.validate getRowData with
  | .error e => throw (IO.userError s!"valid GetWidget row rejected: {e}")
  | .ok row =>
    let w := Acme.Repo.Repo.widgetFromGetRow row
    expect (w.id == 9223372036854775807) "GetWidget id projection"
    expect (w.owner_id == 9223372036854775807) "GetWidget owner projection"
    expect (w.quantity == 4294967295) "GetWidget quantity projection"
    expect (w.name == getRowData.name && w.sku == getRowData.sku &&
      w.description == getRowData.description) "GetWidget text projection"
  expect (AcmeDb.Queries.GetWidget.validate { getRowData with id := 0 } |>.isOk |> not)
    "GetWidget zero id rejected before mapping"
  expect (AcmeDb.Queries.GetWidget.validate { getRowData with ownerId := -1 } |>.isOk |> not)
    "GetWidget negative owner rejected before mapping"
  expect (AcmeDb.Queries.GetWidget.validate
      { getRowData with quantity := 4294967296 } |>.isOk |> not)
    "GetWidget overflowing quantity rejected before mapping"

  let listRowData : AcmeDb.Queries.ListWidgets.RowData :=
    { id := 41
      ownerId := 7
      name := "List row"
      sku := "wgt-0041"
      quantity := 0
      description := "proof-projected" }
  match AcmeDb.Queries.ListWidgets.validate listRowData with
  | .error e => throw (IO.userError s!"valid ListWidgets row rejected: {e}")
  | .ok row =>
    let w := Acme.Repo.Repo.widgetFromListRow row
    expect (w.id == 41 && w.owner_id == 7 && w.quantity == 0)
      "ListWidgets numeric projection"
    expect (w.name == listRowData.name && w.sku == listRowData.sku &&
      w.description == listRowData.description) "ListWidgets text projection"
  expect (AcmeDb.Queries.ListWidgets.validate
      { listRowData with quantity := -1 } |>.isOk |> not)
    "ListWidgets negative quantity rejected before mapping"

  IO.println "all acme validation, authorization, and authentication assertions passed"
