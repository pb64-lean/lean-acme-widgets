import AcmeLean.user
import AcmeLean.widgets
import AcmeLean.authz
import AcmeValid.user
import AcmeValid.widgets
import AcmeValid.authz
import Acme.Auth
import Acme.Repo
import Acme.Service
import Grpc

/-!
Validation + authorization refinement types, hermetically: field rules on
User/Widget, the message-level ownership rule on CreateWidgetRequest, and the
(Principal, request) authorization products whose CEL policies are dependent
propositions in `AcmeValid` structures. Every rejection is asserted by rule
id; the accepted cases demonstrate handlers can *use* the carried proofs.

Phase 7 additions: the bearer-token authentication layer (`Acme.Auth`), the
wire-principal binding and capability smart constructors (`Acme.Repo`), the
typed violation classification (`Acme.Service.ruleKind`), and the checked
Int → UIntN row conversions.
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

/-- Expect a violation with rule id `id` whose typed classification maps to
gRPC status `code`. -/
def expectStatus (r : Except Protovalidate.Violation α) (id : String)
    (code : Grpc.Code) (label : String) : IO Unit := do
  match r with
  | .ok _ => throw (IO.userError s!"{label}: expected violation {id}, got ok")
  | .error e =>
    expect (e.ruleId == id) s!"{label}: expected {id}, got {e.ruleId}"
    expect ((Acme.Service.statusOfViolation e).code == code) s!"{label}: wrong status code"

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

  -- ── authentication: bearer-token table ─────────────────────────────────
  let table := Acme.Auth.demoTable
  let headers (auth? : Option String) : Grpc.Metadata :=
    match auth? with
    | some v => Grpc.Metadata.empty.insert "authorization" v
    | none => Grpc.Metadata.empty
  let authEditor7 ← match Acme.Auth.authenticate table (headers (some "Bearer acme-editor-7")) with
    | .ok p => pure p
    | .error s => throw (IO.userError s!"editor-7 token rejected: {s.messageD}")
  expect (authEditor7.id == 7 && authEditor7.roleLevel == 2) "editor-7 identity"
  let authViewer7 ← match Acme.Auth.authenticate table (headers (some "Bearer acme-viewer-7")) with
    | .ok p => pure p
    | .error s => throw (IO.userError s!"viewer-7 token rejected: {s.messageD}")
  let authEditor8 ← match Acme.Auth.authenticate table (headers (some "Bearer acme-editor-8")) with
    | .ok p => pure p
    | .error s => throw (IO.userError s!"editor-8 token rejected: {s.messageD}")
  let expectUnauthenticated (auth? : Option String) (label : String) : IO Unit := do
    match Acme.Auth.authenticate table (headers auth?) with
    | .ok p => throw (IO.userError s!"{label}: unexpectedly authenticated {p}")
    | .error s => expect (s.code == .unauthenticated) s!"{label}: wrong code"
  expectUnauthenticated none "missing header"
  expectUnauthenticated (some "Bearer bogus") "unknown token"
  expectUnauthenticated (some "Basic acme-editor-7") "wrong scheme"

  -- misconfigured tables fail at construction
  expect (Acme.Auth.TokenTable.parse "t:7:2,u:8:1" |>.isOk) "valid spec parses"
  expect (!(Acme.Auth.TokenTable.parse "t:0:2" |>.isOk)) "id 0 rejected"
  expect (!(Acme.Auth.TokenTable.parse "t:7:4" |>.isOk)) "role 4 rejected"
  expect (!(Acme.Auth.TokenTable.parse "gibberish" |>.isOk)) "malformed spec rejected"

  -- ── binding: wire principal must equal the authenticated caller ────────
  match Valid.CheckedCreateWidgetRequest.validate (checkedCreate editor createReq) with
  | .error e => throw (IO.userError s!"binding demo validate: {e}")
  | .ok v =>
    match Acme.Repo.authorizeCreate authEditor7 v with
    | none => throw (IO.userError "bound create was refused")
    | some cap =>
      -- the capability carries the policy relative to the AUTHENTICATED principal
      let _ : cap.request.widget.toBase.owner_id = cap.principal.id := cap.owner_eq
      let _ : 2 ≤ cap.principal.roleLevel := cap.editor
      expect (cap.principal.id == 7) "capability principal"
    -- same wire request, different authenticated identities: refused
    expect (Acme.Repo.authorizeCreate authViewer7 v |>.isNone) "role mismatch refused"
    expect (Acme.Repo.authorizeCreate authEditor8 v |>.isNone) "id mismatch refused"

  -- ── typed violation classification ─────────────────────────────────────
  -- all runtime-reachable authz.* rules map to PERMISSION_DENIED...
  expectStatus (Valid.CheckedCreateWidgetRequest.validate
      (checkedCreate { editor with id := 8 } createReq))
    "authz.create.self" .permissionDenied "classify create.self"
  expectStatus (Valid.CheckedCreateWidgetRequest.validate (checkedCreate viewer createReq))
    "authz.create.editor" .permissionDenied "classify create.editor"
  expectStatus (Valid.CheckedListWidgetsRequest.validate
      { principal := some { viewer with id := 8 },
        request := some { user_id := 7, page_size := 20 } })
    "authz.list.self_or_admin" .permissionDenied "classify list.self_or_admin"
  let updReq : UpdateWidgetRequest :=
    { user_id := 7, widget := some { goodWidget with id := 41 } }
  expectStatus (Valid.CheckedUpdateWidgetRequest.validate
      { principal := some { editor with id := 8 }, request := some updReq })
    "authz.update.self" .permissionDenied "classify update.self"
  expectStatus (Valid.CheckedUpdateWidgetRequest.validate
      { principal := some viewer, request := some updReq })
    "authz.update.editor" .permissionDenied "classify update.editor"
  expectStatus (Valid.CheckedDeleteWidgetRequest.validate
      { principal := some { viewer with id := 8 },
        request := some { user_id := 7, widget_id := 41 } })
    "authz.delete.self_or_admin" .permissionDenied "classify delete.self_or_admin"
  -- (authz.update.widget_owner is unreachable at runtime — it is implied by
  -- update.owner_matches + authz.update.self — but classified by the same
  -- #guard-checked mapping in Acme.Service.)
  -- ... and field rules to INVALID_ARGUMENT
  expectStatus (Valid.Widget.validate { goodWidget with sku := "bogus" })
    "string.pattern" .invalidArgument "classify field rule"
  expectStatus (Valid.CheckedCreateWidgetRequest.validate
      { principal := none, request := some createReq })
    "required" .invalidArgument "classify required"
  expect (Acme.Service.authzRuleIds.all
      (fun id => (Acme.Service.statusOfViolation ⟨"", id, ""⟩).code == .permissionDenied))
    "every declared authz rule id classifies as PERMISSION_DENIED"

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

  IO.println "all acme validation, authorization, and authentication assertions passed"
