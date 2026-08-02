module

public import Pg
public import AcmeLean.widgets

public section

namespace Acme
namespace Repo

open Pg

/-!
Widget persistence over pg-lean. One `Pg.Connection` per repository;
statements are prepared once at startup and executed by name (extended
protocol, text parameters). pg-lean serializes operations on a connection, so
the repository is safe to share across handler tasks.
-/

structure Repo where
  conn : Connection

def migrate (conn : Connection) : IO (Except Error Unit) := do
  pure ((← conn.exec "CREATE TABLE IF NOT EXISTS widgets (
      id BIGSERIAL PRIMARY KEY,
      owner_id BIGINT NOT NULL,
      name TEXT NOT NULL,
      sku TEXT NOT NULL,
      quantity INT NOT NULL,
      description TEXT NOT NULL DEFAULT '')").map (fun _ => ()))

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
    if let .error e := ← conn.prepare name sql then
      return .error e
  pure (.ok { conn })

namespace Repo

private def textParam (s : String) : Option ByteArray := some s.toUTF8

private def rowToWidget (rs : Rows) (row : Nat) : Except String acme.v1.Widget := do
  let id ← rs.get (α := Int) row 0
  let ownerId ← rs.get (α := Int) row 1
  let name ← rs.get (α := String) row 2
  let sku ← rs.get (α := String) row 3
  let quantity ← rs.get (α := Int) row 4
  let description ← rs.get (α := String) row 5
  pure {
    id := UInt64.ofNat id.toNat
    owner_id := UInt64.ofNat ownerId.toNat
    name, sku
    quantity := UInt32.ofNat quantity.toNat
    description }

private def decodeError (what e : String) : Error :=
  .rejected (.rejectedInvalid s!"{what}: {e}")

/-- Insert; returns the database-assigned id. -/
def insertWidget (repo : Repo) (w : acme.v1.Widget) : IO (Except Error UInt64) := do
  match ← repo.conn.execute "w_insert" #[
      textParam (toString w.owner_id.toNat),
      textParam w.name,
      textParam w.sku,
      textParam (toString w.quantity.toNat),
      textParam w.description] with
  | .error e => pure (.error e)
  | .ok rows =>
    match rows.get (α := Int) 0 0 with
    | .ok id => pure (.ok (UInt64.ofNat id.toNat))
    | .error e => pure (.error (decodeError "insert returning" e))

def getWidget (repo : Repo) (id : UInt64) : IO (Except Error (Option acme.v1.Widget)) := do
  match ← repo.conn.execute "w_get" #[textParam (toString id.toNat)] with
  | .error e => pure (.error e)
  | .ok rows =>
    if rows.rows.isEmpty then
      pure (.ok none)
    else
      match rowToWidget rows 0 with
      | .ok w => pure (.ok (some w))
      | .error e => pure (.error (decodeError "widget row" e))

def listWidgets (repo : Repo) (ownerId : UInt64) (limit : UInt32) :
    IO (Except Error (Array acme.v1.Widget)) := do
  match ← repo.conn.execute "w_list" #[
      textParam (toString ownerId.toNat),
      textParam (toString limit.toNat)] with
  | .error e => pure (.error e)
  | .ok rows => Id.run do
    let mut out := #[]
    for i in [0:rows.rows.size] do
      match rowToWidget rows i with
      | .ok w => out := out.push w
      | .error e => return pure (.error (decodeError "widget row" e))
    return pure (.ok out)

/-- Update by (id, owner); `false` when no such widget belongs to the owner. -/
def updateWidget (repo : Repo) (w : acme.v1.Widget) : IO (Except Error Bool) := do
  match ← repo.conn.execute "w_update" #[
      textParam (toString w.id.toNat),
      textParam (toString w.owner_id.toNat),
      textParam w.name,
      textParam w.sku,
      textParam (toString w.quantity.toNat),
      textParam w.description] with
  | .error e => pure (.error e)
  | .ok rows => pure (.ok (rows.rows.size == 1))

/-- Delete by (id, owner); `false` when nothing matched. -/
def deleteWidget (repo : Repo) (id ownerId : UInt64) : IO (Except Error Bool) := do
  match ← repo.conn.execute "w_delete" #[
      textParam (toString id.toNat),
      textParam (toString ownerId.toNat)] with
  | .error e => pure (.error e)
  | .ok rows => pure (.ok (rows.rows.size == 1))

end Repo
end Repo
end Acme
