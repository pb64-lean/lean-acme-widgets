import AcmeDb

/-!
# Live lean-pgx acceptance test

The `pg_live_test` rule owns the transient PostgreSQL cluster and passes its
URL plus the ordered DDL migrations to this executable.  This test deliberately
uses the generated runners directly: it verifies that the generated contract
can attach to a separately migrated database and that every CRUD query both
executes and decodes its declared result cardinality.
-/

namespace Acme.LeanPgxLiveTest

open Std.Async

private structure Options where
  url : String
  migrations : Array String

private def usage : String :=
  "usage: acme_lean_pgx_live_test --url URL --migration PATH [--migration PATH ...]"

private def parseMigrations (url : String) (paths : Array String) :
    List String → Except String Options
  | [] =>
    if paths.isEmpty then throw s!"at least one --migration is required\n{usage}"
    else pure { url, migrations := paths }
  | "--migration" :: path :: rest =>
    if path.isEmpty then throw s!"migration path must not be empty\n{usage}"
    else parseMigrations url (paths.push path) rest
  | _ => throw usage

private def parseOptions : List String → Except String Options
  | "--url" :: url :: rest =>
    if url.isEmpty then throw s!"URL must not be empty\n{usage}"
    else parseMigrations url #[] rest
  | _ => throw usage

private def fail (message : String) : Async α :=
  throw (IO.userError message)

private def pg! (context : String) (result : Except Pg.Error α) : Async α :=
  match result with
  | .ok value => pure value
  | .error error => fail s!"{context}: {error}"

private def typed! (context : String) (result : Except Pgx.Typed.Error α) : Async α :=
  match result with
  | .ok value => pure value
  | .error error => fail s!"{context}: {error}"

private def withConnection (config : Pg.ConnectConfig)
    (body : Pg.Connection → Async α) : Async α := do
  let conn ← Pg.connect config
  try
    let value ← body conn
    conn.close
    pure value
  catch error =>
    try conn.close catch _ => pure ()
    throw error

private def replayMigrations (conn : Pg.Connection) (paths : Array String) :
    Async Unit := do
  for path in paths do
    let sql ← try
      IO.FS.readFile path
    catch error =>
      fail s!"read migration {path}: {error}"
    let _ ← pg! s!"apply migration {path}" (← conn.exec sql)

private def expectWidget (context : String)
    (row : AcmeDb.Queries.GetWidget.Row)
    (expectedId expectedOwner : Int64)
    (expectedName expectedSku : String)
    (expectedQuantity : Int64)
    (expectedDescription : String) : Async Unit := do
  let value := row.val
  unless value.id == expectedId && value.ownerId == expectedOwner &&
      value.name == expectedName && value.sku == expectedSku &&
      value.quantity == expectedQuantity &&
      value.description == expectedDescription do
    fail s!"{context}: generated row decoded unexpected widget values"

private def exerciseCrud
    (conn : Pgx.Typed.CheckedConnection AcmeDb.database) : Async Unit := do
  let ownerId : Int64 := 7
  let initialName := "lean-pgx acceptance widget"
  let initialSku := "wgt-7001"
  let initialQuantity : Int64 := 12
  let initialDescription := "inserted through generated SQL"

  let inserted ← typed! "InsertWidget.exactlyOne" (←
    AcmeDb.Queries.InsertWidget.run conn {
      ownerId
      name := initialName
      sku := initialSku
      quantity := initialQuantity
      description := initialDescription
    })
  let widgetId := inserted.val.id
  unless widgetId > 0 do
    fail s!"InsertWidget.exactlyOne: expected a positive id, got {widgetId}"

  let fetched? ← typed! "GetWidget.zeroOrOne after insert" (←
    AcmeDb.Queries.GetWidget.run conn { widgetId })
  let some fetched := fetched?
    | fail "GetWidget.zeroOrOne after insert: returned none"
  expectWidget "GetWidget.zeroOrOne after insert" fetched widgetId ownerId
    initialName initialSku initialQuantity initialDescription

  let listed ← typed! "ListWidgets.many" (←
    AcmeDb.Queries.ListWidgets.run conn { ownerId, pageSize := 100 })
  let some listedWidget := listed.find? (fun row => row.val.id == widgetId)
    | fail s!"ListWidgets.many: inserted widget {widgetId} was absent"
  -- `ListWidgets.Row` and `GetWidget.Row` are distinct generated refinement
  -- types, so compare the list projection directly.
  unless listedWidget.val.ownerId == ownerId &&
      listedWidget.val.name == initialName && listedWidget.val.sku == initialSku &&
      listedWidget.val.quantity == initialQuantity &&
      listedWidget.val.description == initialDescription do
    fail "ListWidgets.many: generated row decoded unexpected widget values"

  let updatedName := "updated lean-pgx widget"
  let updatedSku := "wgt-7002"
  let updatedQuantity : Int64 := 23
  let updatedDescription := "updated through generated SQL"
  let updated ← typed! "UpdateWidget.execute" (←
    AcmeDb.Queries.UpdateWidget.run conn {
      widgetId
      ownerId
      name := updatedName
      sku := updatedSku
      quantity := updatedQuantity
      description := updatedDescription
    })
  unless updated.tag == "UPDATE 1" do
    fail s!"UpdateWidget.execute: expected UPDATE 1, got {updated.tag}"

  let notUpdated ← typed! "UpdateWidget.execute wrong owner" (←
    AcmeDb.Queries.UpdateWidget.run conn {
      widgetId
      ownerId := ownerId + 1
      name := "must not be stored"
      sku := "wgt-9999"
      quantity := 99
      description := "wrong owner"
    })
  unless notUpdated.tag == "UPDATE 0" do
    fail s!"UpdateWidget.execute wrong owner: expected UPDATE 0, got {notUpdated.tag}"

  let fetchedUpdated? ← typed! "GetWidget.zeroOrOne after update" (←
    AcmeDb.Queries.GetWidget.run conn { widgetId })
  let some fetchedUpdated := fetchedUpdated?
    | fail "GetWidget.zeroOrOne after update: returned none"
  expectWidget "GetWidget.zeroOrOne after update" fetchedUpdated widgetId ownerId
    updatedName updatedSku updatedQuantity updatedDescription

  let deleted ← typed! "DeleteWidget.execute" (←
    AcmeDb.Queries.DeleteWidget.run conn { widgetId, ownerId })
  unless deleted.tag == "DELETE 1" do
    fail s!"DeleteWidget.execute: expected DELETE 1, got {deleted.tag}"

  let notDeleted ← typed! "DeleteWidget.execute repeated delete" (←
    AcmeDb.Queries.DeleteWidget.run conn { widgetId, ownerId })
  unless notDeleted.tag == "DELETE 0" do
    fail s!"DeleteWidget.execute repeated delete: expected DELETE 0, got {notDeleted.tag}"

  let missing? ← typed! "GetWidget.zeroOrOne after delete" (←
    AcmeDb.Queries.GetWidget.run conn { widgetId })
  unless missing?.isNone do
    fail "GetWidget.zeroOrOne after delete: deleted widget was still returned"

private def runAcceptance (options : Options) : Async Unit := do
  let config ← match Pg.ConnectConfig.parseUri options.url with
    | .ok value => pure value
    | .error error => fail s!"invalid PostgreSQL URL: {error}"
  withConnection config fun raw => do
    replayMigrations raw options.migrations
    let checked ← typed! "attach generated AcmeDb contract" (← AcmeDb.attach raw)
    exerciseCrud checked

private def asyncMain (args : List String) : Async UInt32 := do
  try
    let options ← match parseOptions args with
      | .ok value => pure value
      | .error error => fail error
    runAcceptance options
    IO.println "PASS AcmeDb generated CRUD acceptance"
    pure 0
  catch error =>
    IO.eprintln s!"FAIL AcmeDb generated CRUD acceptance: {error}"
    pure 1

def main (args : List String) : IO UInt32 :=
  Async.block (asyncMain args)

end Acme.LeanPgxLiveTest

def main (args : List String) : IO UInt32 := Acme.LeanPgxLiveTest.main args
