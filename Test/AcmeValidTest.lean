import AcmeLean.user
import AcmeLean.widgets
import AcmeLean.authz
import AcmeValid.user
import AcmeValid.widgets
import AcmeValid.authz

/-!
Validation + authorization refinement types, hermetically: field rules on
User/Widget, the message-level ownership rule on CreateWidgetRequest, and the
(Principal, request) authorization products whose CEL policies are dependent
propositions in `AcmeValid` structures. Every rejection is asserted by rule
id; the accepted cases demonstrate handlers can *use* the carried proofs.
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

def editor : Principal := { id := 7, role_level := 2 }
def admin : Principal := { id := 99, role_level := 3 }
def viewer : Principal := { id := 7, role_level := 1 }

def createReq : CreateWidgetRequest := { user_id := 7, widget := some goodWidget }

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

  -- ── authorization products: policy as propositions ──────────────────────
  let checkedCreate (p : Principal) (r : CreateWidgetRequest) : CheckedCreateWidgetRequest :=
    { principal := some p, request := some r }
  expectId (Valid.CheckedCreateWidgetRequest.validate (checkedCreate editor createReq))
    "" "editor creates own widget"
  expectId (Valid.CheckedCreateWidgetRequest.validate (checkedCreate viewer createReq))
    "authz.create.editor" "viewer cannot create"
  expectId (Valid.CheckedCreateWidgetRequest.validate
      (checkedCreate { editor with id := 8 }
        { user_id := 8, widget := some { goodWidget with owner_id := 8 } }))
    "" "other editor creates for itself"
  expectId (Valid.CheckedCreateWidgetRequest.validate
      (checkedCreate { editor with id := 8 } createReq))
    "authz.create.self" "cannot create for someone else"
  expectId (Valid.CheckedCreateWidgetRequest.validate
      { principal := none, request := some createReq })
    "required" "principal required"
  expectId (Valid.CheckedCreateWidgetRequest.validate
      (checkedCreate { id := 7, role_level := 9 } createReq))
    "uint32.gt_lt" "role_level out of range"

  -- list: self or admin
  let listReq : ListWidgetsRequest := { user_id := 7, page_size := 20 }
  expectId (Valid.CheckedListWidgetsRequest.validate
      { principal := some viewer, request := some listReq }) "" "viewer lists own"
  expectId (Valid.CheckedListWidgetsRequest.validate
      { principal := some admin, request := some listReq }) "" "admin lists anyone"
  expectId (Valid.CheckedListWidgetsRequest.validate
      { principal := some { viewer with id := 8 }, request := some listReq })
    "authz.list.self_or_admin" "stranger cannot list"
  expectId (Valid.CheckedListWidgetsRequest.validate
      { principal := some viewer, request := some { listReq with page_size := 0 } })
    "uint32.gt_lt" "page_size floor"

  -- update: self + editor + deep widget-owner rule (three-hop traversal)
  let updReq : UpdateWidgetRequest :=
    { user_id := 7, widget := some { goodWidget with id := 41 } }
  expectId (Valid.CheckedUpdateWidgetRequest.validate
      { principal := some editor, request := some updReq }) "" "editor updates own"
  expectId (Valid.CheckedUpdateWidgetRequest.validate
      { principal := some editor, request := some { updReq with widget := some goodWidget } })
    "update.has_id" "update requires widget id"
  expectId (Valid.CheckedUpdateWidgetRequest.validate
      { principal := some viewer, request := some updReq })
    "authz.update.editor" "viewer cannot update"

  -- delete: self or admin
  let delReq : DeleteWidgetRequest := { user_id := 7, widget_id := 41 }
  expectId (Valid.CheckedDeleteWidgetRequest.validate
      { principal := some viewer, request := some delReq }) "" "owner deletes own"
  expectId (Valid.CheckedDeleteWidgetRequest.validate
      { principal := some admin, request := some delReq }) "" "admin deletes anyone's"
  expectId (Valid.CheckedDeleteWidgetRequest.validate
      { principal := some { viewer with id := 8 }, request := some delReq })
    "authz.delete.self_or_admin" "stranger cannot delete"

  -- ── the proofs are usable ───────────────────────────────────────────────
  match Valid.CheckedCreateWidgetRequest.validate (checkedCreate editor createReq) with
  | .error e => throw (IO.userError s!"proof demo: {e}")
  | .ok checked =>
    -- The ownership equation is a hypothesis, not a runtime re-check: a
    -- handler can rewrite along it.
    let _ : checked.principal.toBase.id = checked.request.toBase.user_id :=
      checked.authz_create_self
    let _ : checked.principal.toBase.role_level ≥ 2 := checked.authz_create_editor
    expect (checked.toBase.principal.isSome) "toBase roundtrip"

  -- encode → decodeValid roundtrip through the wire
  match createReq.encode with
  | .error e => throw (IO.userError s!"encode: {e}")
  | .ok bytes =>
    match Valid.CreateWidgetRequest.decodeValid bytes with
    | .ok v => expect (v.toBase.user_id == 7) "decodeValid roundtrip"
    | .error e => throw (IO.userError s!"decodeValid: {e}")

  IO.println "all acme validation and authorization assertions passed"
