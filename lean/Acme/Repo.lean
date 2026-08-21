module

public import AcmeDb
public import AcmeLean.widgets
public import AcmeValid.widgets
public import AcmeValid.service
import all AcmeValid.widgets
import all Pb64AuthzValid.principal
import Pg

public section

namespace Acme
namespace Repo

open acme.v1

/-!
Widget persistence through lean-pgx generated checked runners over pg-lean,
behind a capability-typed boundary.

Every repository function takes the generated per-method `WidgetService.*Call`
capability. Its private constructor is reached only through generated service
registration after pre-body authentication, request validation, and method
policy validation. Evidence therefore crosses the repository boundary without
a consumer-defined authorization wrapper or binding check and is erased only
when projected into a generated query's typed `Params` value.

One checked lean-pgx connection per repository. `open'` attaches the generated
database contract to a raw `Pg.Connection`; generated runners then prepare,
verify, encode, execute, and decode each declared query. pg-lean serializes
operations on the underlying connection, so the repository is safe to share
across handler tasks.
-/

structure Repo where
  conn : Pgx.Typed.CheckedConnection AcmeDb.database

-- ── generated capability consequences ─────────────────────────────────────

/-- The shared validated Principal's positive-id refinement, projected through
its generated base-message view. -/
theorem principalIdPositive (principal : pb64.authz.v1.Valid.Principal) :
    0 < principal.toBase.id := by
  change 0 < principal.id.val
  exact principal.id.property

/-- The plain request's ownership rule and the generated method policy combine
to tie the inserted widget to the authenticated principal. -/
theorem createOwnerEq
    (call : Valid.WidgetService.CreateWidgetCall) :
    call.request.widget.toBase.owner_id = call.principal.toBase.id :=
  calc call.request.widget.toBase.owner_id
      = call.request.user_id.val :=
        call.request.create_owner_matches.resolve_left (fun hc => hc rfl)
    _ = call.request.toBase.user_id := rfl
    _ = call.principal.toBase.id := call.policy.authz_create_self.symm

/-- The corresponding ownership consequence for updates. -/
theorem updateOwnerEq
    (call : Valid.WidgetService.UpdateWidgetCall) :
    call.request.widget.toBase.owner_id = call.principal.toBase.id :=
  calc call.request.widget.toBase.owner_id
      = call.request.user_id.val :=
        call.request.update_owner_matches.resolve_left (fun hc => hc rfl)
    _ = call.request.toBase.user_id := rfl
    _ = call.principal.toBase.id := call.policy.authz_update_self.symm

theorem updateHasId
    (call : Valid.WidgetService.UpdateWidgetCall) :
    0 < call.request.widget.toBase.id :=
  call.request.update_has_id.resolve_left (fun hc => hc rfl)

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

@[inline] private def affectedAtMostOne (zeroTag oneTag expected : String)
    (result : Pgx.Typed.CommandResult) : Except Error Bool :=
  if result.tag == zeroTag then .ok false
  else if result.tag == oneTag then .ok true
  else .error (.database (.cardinality expected result.tag))

/-- Interpret PostgreSQL's exact UPDATE completion tag without accepting an
unexpected verb, malformed count, or impossible multi-row result. -/
@[inline] def updateAffected (result : Pgx.Typed.CommandResult) : Except Error Bool :=
  affectedAtMostOne "UPDATE 0" "UPDATE 1" "UPDATE 0 or UPDATE 1" result

/-- Interpret PostgreSQL's exact DELETE completion tag without accepting an
unexpected verb, malformed count, or impossible multi-row result. -/
@[inline] def deleteAffected (result : Pgx.Typed.CommandResult) : Except Error Bool :=
  affectedAtMostOne "DELETE 0" "DELETE 1" "DELETE 0 or DELETE 1" result

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

/-- Insert the generated call's widget; returns the database-assigned id.
`createOwnerEq` proves the serialized owner is the authenticated principal. -/
def insertWidget (repo : Repo) (cap : Valid.WidgetService.CreateWidgetCall) :
    IO (Except Error UInt64) := do
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

def getWidget (repo : Repo) (cap : Valid.WidgetService.GetWidgetCall) :
    IO (Except Error (Option Widget)) := do
  let widgetId ← match inputInt64 "widgets.id" cap.request.widget_id.val with
    | .ok value => pure value
    | .error error => return .error error
  match ← (AcmeDb.Queries.GetWidget.run repo.conn { widgetId }).block with
  | .error error => pure (.error (.database error))
  | .ok none => pure (.ok none)
  | .ok (some row) => pure (.ok (some (widgetFromGetRow row)))

/-- List the capability's user's widgets;
`cap.policy.authz_list_self_or_admin` proves the listed owner is the
authenticated principal, or the principal is admin. -/
def listWidgets (repo : Repo) (cap : Valid.WidgetService.ListWidgetsCall) :
    IO (Except Error (Array Widget)) := do
  let ownerId ← match inputInt64 "widgets.owner_id" cap.request.user_id.val with
    | .ok value => pure value
    | .error error => return .error error
  let pageSize := quantityInt64 cap.request.page_size.val
  match ← (AcmeDb.Queries.ListWidgets.run repo.conn { ownerId, pageSize }).block with
  | .error error => pure (.error (.database error))
  | .ok rows => pure (.ok (rows.map widgetFromListRow))

/-- Update by (id, owner); `false` when no such widget belongs to the owner.
`updateOwnerEq` proves the owner in the WHERE clause is the authenticated
principal, `updateHasId` that the id predicate is non-degenerate. -/
def updateWidget (repo : Repo) (cap : Valid.WidgetService.UpdateWidgetCall) :
    IO (Except Error Bool) := do
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
  | .ok result => pure (updateAffected result)

/-- Delete by (id, owner); `false` when nothing matched.
`cap.policy.authz_delete_self_or_admin` proves the named owner is the
authenticated principal, or admin override. -/
def deleteWidget (repo : Repo) (cap : Valid.WidgetService.DeleteWidgetCall) :
    IO (Except Error Bool) := do
  let widgetId ← match inputInt64 "widgets.id" cap.request.widget_id.val with
    | .ok value => pure value
    | .error error => return .error error
  let ownerId ← match inputInt64 "widgets.owner_id" cap.request.user_id.val with
    | .ok value => pure value
    | .error error => return .error error
  match ← (AcmeDb.Queries.DeleteWidget.run repo.conn { widgetId, ownerId }).block with
  | .error error => pure (.error (.database error))
  | .ok result => pure (deleteAffected result)

end Repo
end Repo
end Acme
