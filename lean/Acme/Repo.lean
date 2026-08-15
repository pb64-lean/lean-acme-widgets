module

public import AcmeDb
public import AcmeLean.widgets
public import AcmeLean.authz
public import AcmeValid.widgets
public import AcmeValid.authz
public import Acme.Auth
import all AcmeValid.widgets
import all AcmeValid.authz
import Pg

public section

namespace Acme
namespace Repo

open acme.v1

/-!
Widget persistence through lean-pgx generated checked runners over pg-lean,
behind a capability-typed boundary.

Every mutating/reading repository function takes a per-operation
`Authorized*` capability: a structure carrying the validated request, the
`Auth.AuthenticatedPrincipal`, and the policy propositions — extracted from
the generated `AcmeValid.Checked*` proofs plus the `Auth.Bound` binding
check by the `authorize*` smart constructors below. Evidence therefore
crosses the repository boundary intact and is erased only when a capability
is projected into a generated query's typed `Params` value.

One checked lean-pgx connection per repository. `open'` attaches the generated
database contract to a raw `Pg.Connection`; generated runners then prepare,
verify, encode, execute, and decode each declared query. pg-lean serializes
operations on the underlying connection, so the repository is safe to share
across handler tasks.
-/

structure Repo where
  conn : Pgx.Typed.CheckedConnection AcmeDb.database

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

-- ── checked PostgreSQL/protobuf numeric conversions ──────────────────────

/-- Typed numeric conversion failure at the PostgreSQL/protobuf boundary. -/
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

/-- Checked conversion at the service/database boundary. Protobuf `uint64`
admits values above PostgreSQL `BIGINT`; reject those values instead of using
the wrapping `UInt64.toInt64` conversion. -/
def int64OfUInt64 (column : String) (u : UInt64) : Except DecodeError Int64 :=
  let value : Int := (u.toNat : Int)
  if value ≤ Int64.maxValue.toInt then .ok (Int64.ofInt value)
  else .error (.outOfRange column value "int64")

/-- Repository failures distinguish generated database-contract/query errors
from explicit numeric conversion failures at the protobuf/SQL boundary. -/
inductive Error where
  | database (error : Pgx.Typed.Error)
  | conversion (error : DecodeError)
  deriving Repr

def Error.render : Error → String
  | .database error => toString error
  | .conversion error => error.render

instance : ToString Error := ⟨Error.render⟩

/-- Generic pure column-tuple → `Widget` decoder for non-proof-bearing
callers and roundtrip assurance. Generated Get/List rows use their
query-specific proof projections below. -/
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

/-- Protobuf-range row roundtrip: the pure unsigned decoder preserves all six
persisted widget fields. Query parameters are narrowed separately by
`int64OfUInt64` before crossing PostgreSQL's signed `BIGINT` boundary. -/
theorem widgetOfRow_roundtrip (id owner : UInt64) (name sku : String)
    (quantity : UInt32) (description : String) :
    widgetOfRow (id.toNat : Int) (owner.toNat : Int) name sku
      (quantity.toNat : Int) description =
      .ok { id, owner_id := owner, name, sku, quantity, description } := by
  unfold widgetOfRow
  rw [uint64OfInt_roundtrip, uint64OfInt_roundtrip, uint32OfInt_roundtrip,
    except_bind_ok, except_bind_ok, except_bind_ok]
  rfl

-- ── generated database attachment and queries ────────────────────────────

/-- Attach the generated schema/query contract to the application's raw
connection. Database creation and migrations are deployment concerns; this
function never mutates the schema. -/
def open' (conn : Pg.Connection) : IO (Except Error Repo) := do
  match ← (AcmeDb.attach conn).block with
  | .ok checked => pure (.ok { conn := checked })
  | .error error => pure (.error (.database error))

namespace Repo

private def inputInt64 (column : String) (value : UInt64) : Except Error Int64 :=
  (int64OfUInt64 column value).mapError .conversion

private def quantityInt64 (value : UInt32) : Int64 :=
  Int64.ofInt (value.toNat : Int)

/-- Project a validated `GetWidget` row into protobuf form. The generated row
proof discharges every result-side numeric range obligation, so this mapper
contains no repeated range decisions. -/
@[inline] def widgetFromGetRow (row : AcmeDb.Queries.GetWidget.Row) : Widget :=
  { id := AcmeDb.Queries.GetWidget.idUInt64 row
    owner_id := AcmeDb.Queries.GetWidget.ownerIdUInt64 row
    name := row.val.name
    sku := row.val.sku
    quantity := AcmeDb.Queries.GetWidget.quantityUInt32 row
    description := row.val.description }

/-- Project a validated `ListWidgets` row into protobuf form. This deliberately
uses the list query's own proof accessors rather than widening back to `Int`. -/
@[inline] def widgetFromListRow (row : AcmeDb.Queries.ListWidgets.Row) : Widget :=
  { id := AcmeDb.Queries.ListWidgets.idUInt64 row
    owner_id := AcmeDb.Queries.ListWidgets.ownerIdUInt64 row
    name := row.val.name
    sku := row.val.sku
    quantity := AcmeDb.Queries.ListWidgets.quantityUInt32 row
    description := row.val.description }

/-- Insert the capability's widget; returns the database-assigned id.
`cap.owner_eq` proves the serialized owner is the authenticated principal. -/
def insertWidget (repo : Repo) (cap : AuthorizedCreate) : IO (Except Error UInt64) := do
  let w := cap.request.widget.toBase
  let ownerId ← match inputInt64 "widgets.owner_id" w.owner_id with
    | .ok value => pure value
    | .error error => return .error error
  match ← (AcmeDb.Queries.InsertWidget.run repo.conn {
      ownerId,
      name := w.name,
      sku := w.sku,
      quantity := quantityInt64 w.quantity,
      description := w.description
    }).block with
  | .error error => pure (.error (.database error))
  | .ok row =>
    pure <| (uint64OfInt "widgets.id" row.val.id.toInt).mapError .conversion

def getWidget (repo : Repo) (cap : AuthorizedGet) : IO (Except Error (Option Widget)) := do
  let widgetId ← match inputInt64 "widgets.id" cap.request.widget_id.val with
    | .ok value => pure value
    | .error error => return .error error
  match ← (AcmeDb.Queries.GetWidget.run repo.conn { widgetId }).block with
  | .error error => pure (.error (.database error))
  | .ok none => pure (.ok none)
  | .ok (some row) => pure (.ok (some (widgetFromGetRow row)))

/-- List the capability's user's widgets; `cap.self_or_admin` proves the
listed owner is the authenticated principal, or the principal is admin. -/
def listWidgets (repo : Repo) (cap : AuthorizedList) : IO (Except Error (Array Widget)) := do
  let ownerId ← match inputInt64 "widgets.owner_id" cap.request.user_id.val with
    | .ok value => pure value
    | .error error => return .error error
  let pageSize := quantityInt64 cap.request.page_size.val
  match ← (AcmeDb.Queries.ListWidgets.run repo.conn { ownerId, pageSize }).block with
  | .error error => pure (.error (.database error))
  | .ok rows => pure (.ok (rows.map widgetFromListRow))

/-- Update by (id, owner); `false` when no such widget belongs to the owner.
`cap.owner_eq` proves the owner in the WHERE clause is the authenticated
principal, `cap.has_id` that the id predicate is non-degenerate. -/
def updateWidget (repo : Repo) (cap : AuthorizedUpdate) : IO (Except Error Bool) := do
  let w := cap.request.widget.toBase
  let widgetId ← match inputInt64 "widgets.id" w.id with
    | .ok value => pure value
    | .error error => return .error error
  let ownerId ← match inputInt64 "widgets.owner_id" w.owner_id with
    | .ok value => pure value
    | .error error => return .error error
  match ← (AcmeDb.Queries.UpdateWidget.run repo.conn {
      widgetId,
      ownerId,
      name := w.name,
      sku := w.sku,
      quantity := quantityInt64 w.quantity,
      description := w.description
    }).block with
  | .error error => pure (.error (.database error))
  | .ok row? => pure (.ok row?.isSome)

/-- Delete by (id, owner); `false` when nothing matched. `cap.self_or_admin`
proves the named owner is the authenticated principal, or admin override. -/
def deleteWidget (repo : Repo) (cap : AuthorizedDelete) : IO (Except Error Bool) := do
  let widgetId ← match inputInt64 "widgets.id" cap.request.widget_id.val with
    | .ok value => pure value
    | .error error => return .error error
  let ownerId ← match inputInt64 "widgets.owner_id" cap.request.user_id.val with
    | .ok value => pure value
    | .error error => return .error error
  match ← (AcmeDb.Queries.DeleteWidget.run repo.conn { widgetId, ownerId }).block with
  | .error error => pure (.error (.database error))
  | .ok row? => pure (.ok row?.isSome)

end Repo
end Repo
end Acme
