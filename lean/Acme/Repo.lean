module

public import Pg
public import AcmeLean.widgets
public import AcmeLean.authz
public import AcmeValid.widgets
public import AcmeValid.authz
public import Acme.Auth
import all AcmeValid.widgets
import all AcmeValid.authz

public section

namespace Acme
namespace Repo

open Pg
open acme.v1

/-!
Widget persistence over pg-lean, behind a capability-typed boundary.

Every mutating/reading repository function takes a per-operation
`Authorized*` capability: a structure carrying the validated request, the
`Auth.AuthenticatedPrincipal`, and the policy propositions — extracted from
the generated `AcmeValid.Checked*` proofs plus the `Auth.Bound` binding
check by the `authorize*` smart constructors below. Evidence therefore
crosses the repository boundary intact and is erased only at SQL parameter
serialization (`textParam`).

One `Pg.Connection` per repository; statements are prepared once at startup
and executed by name (extended protocol, text parameters). pg-lean
serializes operations on a connection, so the repository is safe to share
across handler tasks.
-/

structure Repo where
  conn : Connection

-- ── capabilities ──────────────────────────────────────────────────────────

/-- Capability to create `request.widget` on behalf of `principal`:
the widget is owned by the *authenticated* caller, who is at least editor. -/
structure AuthorizedCreate where
  principal : Auth.AuthenticatedPrincipal
  request : Valid.CreateWidgetRequest
  owner_eq : request.widget.toBase.owner_id = principal.id
  editor : 2 ≤ principal.roleLevel

/-- Capability to read a widget: any authenticated principal may read
(`principal.role_ge` already certifies role_level ≥ 1). -/
structure AuthorizedGet where
  principal : Auth.AuthenticatedPrincipal
  request : Valid.GetWidgetRequest

/-- Capability to list `request.user_id`'s widgets: the authenticated caller
is that user, or an admin. -/
structure AuthorizedList where
  principal : Auth.AuthenticatedPrincipal
  request : Valid.ListWidgetsRequest
  self_or_admin : principal.roleLevel = 3 ∨ principal.id = request.user_id.val

/-- Capability to update `request.widget`: the widget is owned by the
authenticated caller, who is at least editor, and carries its id. -/
structure AuthorizedUpdate where
  principal : Auth.AuthenticatedPrincipal
  request : Valid.UpdateWidgetRequest
  owner_eq : request.widget.toBase.owner_id = principal.id
  editor : 2 ≤ principal.roleLevel
  has_id : 0 < request.widget.toBase.id

/-- Capability to delete widget `request.widget_id` of owner
`request.user_id`: the authenticated caller is that owner, or an admin. -/
structure AuthorizedDelete where
  principal : Auth.AuthenticatedPrincipal
  request : Valid.DeleteWidgetRequest
  self_or_admin : principal.roleLevel = 3 ∨ principal.id = request.user_id.val

-- ── proposition transport: generated Checked* proofs + Bound ⇒ capability ──

private theorem create_owner_eq (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedCreateWidgetRequest) (hb : Auth.Bound p v.principal) :
    v.request.widget.toBase.owner_id = p.id :=
  calc v.request.widget.toBase.owner_id
      = v.request.user_id.val := v.request.create_owner_matches.resolve_left (fun hc => hc rfl)
    _ = v.request.toBase.user_id := rfl
    _ = v.principal.toBase.id := v.authz_create_self.symm
    _ = p.id := hb.1

private theorem create_editor (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedCreateWidgetRequest) (hb : Auth.Bound p v.principal) :
    2 ≤ p.roleLevel :=
  hb.2 ▸ v.authz_create_editor

private theorem list_self_or_admin (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedListWidgetsRequest) (hb : Auth.Bound p v.principal) :
    p.roleLevel = 3 ∨ p.id = v.request.user_id.val := by
  cases v.authz_list_self_or_admin with
  | inl hrole => rw [hb.2] at hrole; exact .inl hrole
  | inr hid =>
    rw [hb.1] at hid
    exact .inr (hid.trans (rfl : v.request.toBase.user_id = v.request.user_id.val))

private theorem update_owner_eq (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedUpdateWidgetRequest) (hb : Auth.Bound p v.principal) :
    v.request.widget.toBase.owner_id = p.id :=
  calc v.request.widget.toBase.owner_id
      = v.request.user_id.val := v.request.update_owner_matches.resolve_left (fun hc => hc rfl)
    _ = v.request.toBase.user_id := rfl
    _ = v.principal.toBase.id := v.authz_update_self.symm
    _ = p.id := hb.1

private theorem update_editor (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedUpdateWidgetRequest) (hb : Auth.Bound p v.principal) :
    2 ≤ p.roleLevel :=
  hb.2 ▸ v.authz_update_editor

private theorem update_has_id (v : Valid.CheckedUpdateWidgetRequest) :
    0 < v.request.widget.toBase.id :=
  v.request.update_has_id.resolve_left (fun hc => hc rfl)

private theorem delete_self_or_admin (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedDeleteWidgetRequest) (hb : Auth.Bound p v.principal) :
    p.roleLevel = 3 ∨ p.id = v.request.user_id.val := by
  cases v.authz_delete_self_or_admin with
  | inl hrole => rw [hb.2] at hrole; exact .inl hrole
  | inr hid =>
    rw [hb.1] at hid
    exact .inr (hid.trans (rfl : v.request.toBase.user_id = v.request.user_id.val))

-- ── smart constructors: the only runtime check is the binding decision ─────

/-- Authorize a create for the authenticated `p`: succeeds iff the wire
principal is bound to `p`; the policy propositions are *transported*, not
re-checked. -/
def authorizeCreate (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedCreateWidgetRequest) : Option AuthorizedCreate :=
  if hb : Auth.Bound p v.principal then
    some { principal := p, request := v.request,
           owner_eq := create_owner_eq p v hb, editor := create_editor p v hb }
  else none

def authorizeGet (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedGetWidgetRequest) : Option AuthorizedGet :=
  if _hb : Auth.Bound p v.principal then
    some { principal := p, request := v.request }
  else none

def authorizeList (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedListWidgetsRequest) : Option AuthorizedList :=
  if hb : Auth.Bound p v.principal then
    some { principal := p, request := v.request,
           self_or_admin := list_self_or_admin p v hb }
  else none

def authorizeUpdate (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedUpdateWidgetRequest) : Option AuthorizedUpdate :=
  if hb : Auth.Bound p v.principal then
    some { principal := p, request := v.request,
           owner_eq := update_owner_eq p v hb, editor := update_editor p v hb,
           has_id := update_has_id v }
  else none

def authorizeDelete (p : Auth.AuthenticatedPrincipal)
    (v : Valid.CheckedDeleteWidgetRequest) : Option AuthorizedDelete :=
  if hb : Auth.Bound p v.principal then
    some { principal := p, request := v.request,
           self_or_admin := delete_self_or_admin p v hb }
  else none

-- ── soundness: authorization success carries exactly the claimed evidence ──

/-- Possessing an `AuthorizedCreate` *is* possession of the policy: the
created widget belongs to the authenticated principal, who is an editor. -/
theorem AuthorizedCreate.sound (cap : AuthorizedCreate) :
    cap.request.widget.toBase.owner_id = cap.principal.id ∧
      2 ≤ cap.principal.roleLevel :=
  ⟨cap.owner_eq, cap.editor⟩

/-- `authorizeCreate` succeeding yields a capability for exactly the
authenticated principal and the validated request, whose propositions hold
for that principal — authorization by construction. -/
theorem authorizeCreate_sound {p : Auth.AuthenticatedPrincipal}
    {v : Valid.CheckedCreateWidgetRequest} {cap : AuthorizedCreate}
    (h : authorizeCreate p v = some cap) :
    cap.principal = p ∧ cap.request = v.request ∧
      v.request.widget.toBase.owner_id = p.id ∧ 2 ≤ p.roleLevel := by
  unfold authorizeCreate at h
  split at h
  next hb =>
    injection h with h
    subst h
    exact ⟨rfl, rfl, create_owner_eq p v hb, create_editor p v hb⟩
  next => simp at h

/-- `authorizeCreate` fails only on a genuine binding mismatch. -/
theorem authorizeCreate_none {p : Auth.AuthenticatedPrincipal}
    {v : Valid.CheckedCreateWidgetRequest}
    (h : authorizeCreate p v = none) : ¬ Auth.Bound p v.principal := by
  unfold authorizeCreate at h
  split at h
  next => simp at h
  next hb => exact hb

-- ── checked SQL row decoding (no silent Int.toNat collapse) ───────────────

/-- Typed decode failure for values postgres returned outside the proto
numeric ranges (possible only if the CHECK constraints were bypassed). -/
inductive DecodeError where
  | outOfRange (column : String) (value : Int) (target : String)
  deriving Repr

def DecodeError.render : DecodeError → String
  | .outOfRange column value target =>
    s!"column {column}: value {value} outside {target} range"

instance : ToString DecodeError := ⟨DecodeError.render⟩

/-- Checked `Int → UInt64`: out-of-range is an error, never a wrap/collapse. -/
def uint64OfInt (column : String) (i : Int) : Except DecodeError UInt64 :=
  if 0 ≤ i ∧ i < (2 : Int) ^ 64 then .ok (UInt64.ofNat i.toNat)
  else .error (.outOfRange column i "uint64")

/-- Checked `Int → UInt32`. -/
def uint32OfInt (column : String) (i : Int) : Except DecodeError UInt32 :=
  if 0 ≤ i ∧ i < (2 : Int) ^ 32 then .ok (UInt32.ofNat i.toNat)
  else .error (.outOfRange column i "uint32")

/-- Pure column-tuple → `Widget` decoder used for every row. -/
def widgetOfRow (id ownerId : Int) (name sku : String) (quantity : Int)
    (description : String) : Except DecodeError Widget := do
  let id ← uint64OfInt "widgets.id" id
  let ownerId ← uint64OfInt "widgets.owner_id" ownerId
  let quantity ← uint32OfInt "widgets.quantity" quantity
  pure { id, owner_id := ownerId, name, sku, quantity, description }

private theorem except_bind_ok {α β ε : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl

theorem uint64OfInt_roundtrip (column : String) (u : UInt64) :
    uint64OfInt column (u.toNat : Int) = .ok u := by
  have hlt : u.toNat < 2 ^ 64 := UInt64.toNat_lt u
  rw [uint64OfInt,
    if_pos (show 0 ≤ (u.toNat : Int) ∧ (u.toNat : Int) < 2 ^ 64 by omega)]
  simp [Int.toNat_natCast, UInt64.ofNat_toNat]

theorem uint32OfInt_roundtrip (column : String) (u : UInt32) :
    uint32OfInt column (u.toNat : Int) = .ok u := by
  have hlt : u.toNat < 2 ^ 32 := UInt32.toNat_lt u
  rw [uint32OfInt,
    if_pos (show 0 ≤ (u.toNat : Int) ∧ (u.toNat : Int) < 2 ^ 32 by omega)]
  simp [Int.toNat_natCast, UInt32.ofNat_toNat]

/-- Row roundtrip: decoding exactly the column values the repository
serializes yields exactly the widget with those fields (the six columns are
the whole persisted state; wire-level unknown fields are never stored). -/
theorem widgetOfRow_roundtrip (id owner : UInt64) (name sku : String)
    (quantity : UInt32) (description : String) :
    widgetOfRow (id.toNat : Int) (owner.toNat : Int) name sku
      (quantity.toNat : Int) description =
      .ok { id, owner_id := owner, name, sku, quantity, description } := by
  unfold widgetOfRow
  rw [uint64OfInt_roundtrip, uint64OfInt_roundtrip, uint32OfInt_roundtrip,
    except_bind_ok, except_bind_ok, except_bind_ok]
  rfl

-- ── SQL ───────────────────────────────────────────────────────────────────

def migrate (conn : Connection) : IO (Except Error Unit) := do
  pure ((← (conn.exec "CREATE TABLE IF NOT EXISTS widgets (
      id BIGSERIAL PRIMARY KEY CHECK (id > 0),
      owner_id BIGINT NOT NULL CHECK (owner_id >= 0),
      name TEXT NOT NULL,
      sku TEXT NOT NULL,
      quantity BIGINT NOT NULL CHECK (quantity >= 0 AND quantity < 4294967296),
      description TEXT NOT NULL DEFAULT '')").block).map (fun _ => ()))

private def prepared : Array (String × String) := #[
  ("w_insert",
   "INSERT INTO widgets (owner_id, name, sku, quantity, description)
    VALUES ($1, $2, $3, $4, $5) RETURNING id"),
  ("w_get",
   "SELECT id, owner_id, name, sku, quantity, description FROM widgets
    WHERE id = $1"),
  ("w_list",
   "SELECT id, owner_id, name, sku, quantity, description FROM widgets
    WHERE owner_id = $1 ORDER BY id LIMIT $2"),
  ("w_update",
   "UPDATE widgets SET name = $3, sku = $4, quantity = $5, description = $6
    WHERE id = $1 AND owner_id = $2 RETURNING id"),
  ("w_delete",
   "DELETE FROM widgets WHERE id = $1 AND owner_id = $2 RETURNING id")]

def open' (conn : Connection) : IO (Except Error Repo) := do
  if let .error e := ← migrate conn then
    return .error e
  for (name, sql) in prepared do
    if let .error e := ← (conn.prepare name sql).block then
      return .error e
  pure (.ok { conn })

namespace Repo

/-- Serialization boundary: this is the only place evidence is erased. -/
private def textParam (s : String) : Option ByteArray := some s.toUTF8

private def rowToWidget (rs : Rows) (row : Nat) : Except String Widget := do
  let id ← rs.get (α := Int) row 0
  let ownerId ← rs.get (α := Int) row 1
  let name ← rs.get (α := String) row 2
  let sku ← rs.get (α := String) row 3
  let quantity ← rs.get (α := Int) row 4
  let description ← rs.get (α := String) row 5
  (widgetOfRow id ownerId name sku quantity description).mapError DecodeError.render

private def decodeError (what e : String) : Error :=
  .rejected (.rejectedInvalid s!"{what}: {e}")

/-- Insert the capability's widget; returns the database-assigned id.
`cap.owner_eq` proves the serialized owner is the authenticated principal. -/
def insertWidget (repo : Repo) (cap : AuthorizedCreate) : IO (Except Error UInt64) := do
  let w := cap.request.widget.toBase
  match ← (repo.conn.execute "w_insert" #[
      textParam (toString w.owner_id.toNat),
      textParam w.name,
      textParam w.sku,
      textParam (toString w.quantity.toNat),
      textParam w.description]).block with
  | .error e => pure (.error e)
  | .ok rows =>
    match rows.get (α := Int) 0 0 with
    | .ok id =>
      match uint64OfInt "widgets.id" id with
      | .ok id => pure (.ok id)
      | .error e => pure (.error (decodeError "insert returning" e.render))
    | .error e => pure (.error (decodeError "insert returning" e))

def getWidget (repo : Repo) (cap : AuthorizedGet) : IO (Except Error (Option Widget)) := do
  match ← (repo.conn.execute "w_get" #[
      textParam (toString cap.request.widget_id.val.toNat)]).block with
  | .error e => pure (.error e)
  | .ok rows =>
    if rows.rows.isEmpty then
      pure (.ok none)
    else
      match rowToWidget rows 0 with
      | .ok w => pure (.ok (some w))
      | .error e => pure (.error (decodeError "widget row" e))

/-- List the capability's user's widgets; `cap.self_or_admin` proves the
listed owner is the authenticated principal, or the principal is admin. -/
def listWidgets (repo : Repo) (cap : AuthorizedList) : IO (Except Error (Array Widget)) := do
  match ← (repo.conn.execute "w_list" #[
      textParam (toString cap.request.user_id.val.toNat),
      textParam (toString cap.request.page_size.val.toNat)]).block with
  | .error e => pure (.error e)
  | .ok rows => Id.run do
    let mut out := #[]
    for i in [0:rows.rows.size] do
      match rowToWidget rows i with
      | .ok w => out := out.push w
      | .error e => return pure (.error (decodeError "widget row" e))
    return pure (.ok out)

/-- Update by (id, owner); `false` when no such widget belongs to the owner.
`cap.owner_eq` proves the owner in the WHERE clause is the authenticated
principal, `cap.has_id` that the id predicate is non-degenerate. -/
def updateWidget (repo : Repo) (cap : AuthorizedUpdate) : IO (Except Error Bool) := do
  let w := cap.request.widget.toBase
  match ← (repo.conn.execute "w_update" #[
      textParam (toString w.id.toNat),
      textParam (toString w.owner_id.toNat),
      textParam w.name,
      textParam w.sku,
      textParam (toString w.quantity.toNat),
      textParam w.description]).block with
  | .error e => pure (.error e)
  | .ok rows => pure (.ok (rows.rows.size == 1))

/-- Delete by (id, owner); `false` when nothing matched. `cap.self_or_admin`
proves the named owner is the authenticated principal, or admin override. -/
def deleteWidget (repo : Repo) (cap : AuthorizedDelete) : IO (Except Error Bool) := do
  match ← (repo.conn.execute "w_delete" #[
      textParam (toString cap.request.widget_id.val.toNat),
      textParam (toString cap.request.user_id.val.toNat)]).block with
  | .error e => pure (.error e)
  | .ok rows => pure (.ok (rows.rows.size == 1))

end Repo
end Repo
end Acme
