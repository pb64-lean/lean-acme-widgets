import Acme.Repo

open acme.v1

/-!
Focused microbenchmark for APP-02's proof-directed `ListWidgets` row mapper.
Both cases reuse already-validated rows, matching the repository hot path after
the generated decoder has established the SQL CHECK propositions.
-/

private def checkedWidgetFromListRow (row : AcmeDb.Queries.ListWidgets.Row) :
    Except Acme.Repo.DecodeError Widget :=
  Acme.Repo.widgetOfRow row.val.id.toInt row.val.ownerId.toInt row.val.name
    row.val.sku row.val.quantity.toInt row.val.description

private def widgetChecksum (widgets : Array Widget) : Nat :=
  widgets.size + match widgets[0]? with
    | some widget => widget.id.toNat + widget.quantity.toNat
    | none => 0

private def mapDirectPages (rows : Array AcmeDb.Queries.ListWidgets.Row)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    let widgets := rows.map Acme.Repo.Repo.widgetFromListRow
    checksum := checksum + widgetChecksum widgets
  pure checksum

private def mapCheckedPages (rows : Array AcmeDb.Queries.ListWidgets.Row)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match rows.mapM checkedWidgetFromListRow with
    | .ok widgets => checksum := checksum + widgetChecksum widgets
    | .error error => throw (IO.userError s!"checked row mapping failed: {error}")
  pure checksum

private def measureMapping
    (mapPages : Array AcmeDb.Queries.ListWidgets.Row → Nat → IO Nat)
    (row : AcmeDb.Queries.ListWidgets.Row)
    (pageSize iterations : Nat) : IO (Nat × Nat) := do
  let rows := Array.replicate pageSize row
  let _ ← mapPages rows 100
  let started ← IO.monoNanosNow
  let checksum ← mapPages rows iterations
  pure ((← IO.monoNanosNow) - started, checksum)

private def formatHundredths (value : Nat) : String :=
  let fraction := value % 100
  let fractionText := if fraction < 10 then s!"0{fraction}" else toString fraction
  s!"{value / 100}.{fractionText}"

private def printMeasurement (label : String)
    (pageSize iterations elapsed checksum : Nat) : IO Unit := do
  let totalRows := pageSize * iterations
  let nanosPerRowTimes100 :=
    if totalRows = 0 then 0 else elapsed * 100 / totalRows
  IO.println <| s!"mapper={label} page_size={pageSize} iterations={iterations} rows={totalRows} " ++
    s!"elapsed_ns={elapsed} ns_per_row={formatHundredths nanosPerRowTimes100} " ++
    s!"checksum={checksum}"

private def parseIterations (args : List String) : Nat :=
  match args.head? >>= String.toNat? with
  | some iterations => iterations
  | none => 200000

def main (args : List String) : IO Unit := do
  let rowData : AcmeDb.Queries.ListWidgets.RowData :=
    { id := 41
      ownerId := 7
      name := "Benchmark widget"
      sku := "wgt-0041"
      quantity := 12
      description := "proof-directed mapping" }
  let row ← match AcmeDb.Queries.ListWidgets.validate rowData with
    | .ok row => pure row
    | .error error => throw (IO.userError s!"benchmark row validation failed: {error}")
  let iterations := parseIterations args
  let (checked10, checkedChecksum10) ← measureMapping mapCheckedPages row 10 iterations
  let (direct10, directChecksum10) ← measureMapping mapDirectPages row 10 iterations
  let (checked100, checkedChecksum100) ← measureMapping mapCheckedPages row 100 iterations
  let (direct100, directChecksum100) ← measureMapping mapDirectPages row 100 iterations
  printMeasurement "checked_int" 10 iterations checked10 checkedChecksum10
  printMeasurement "proof_direct" 10 iterations direct10 directChecksum10
  printMeasurement "checked_int" 100 iterations checked100 checkedChecksum100
  printMeasurement "proof_direct" 100 iterations direct100 directChecksum100
  let speedup10 := if direct10 = 0 then 0 else checked10 * 100 / direct10
  let speedup100 := if direct100 = 0 then 0 else checked100 * 100 / direct100
  let directScale := if direct10 = 0 then 0 else direct100 * 100 / direct10
  IO.println s!"proof_direct_speedup_page_10_x={formatHundredths speedup10}"
  IO.println s!"proof_direct_speedup_page_100_x={formatHundredths speedup100}"
  IO.println s!"proof_direct_page_100_vs_10_elapsed_x={formatHundredths directScale}"
