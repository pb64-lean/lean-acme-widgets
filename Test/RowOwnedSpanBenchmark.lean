import AcmeDb
import Pg.Protocol.Backend

/-!
Opt-in baseline for the PostgreSQL row-owned-span experiment.

The timed path deliberately starts at an already-framed `RawMessage`: the
experiment does not change the framer's payload copy.  Each iteration runs the
production `Backend.decode`, grows the same owned row-array shape as
`Pg.Connection.foldExecute`, and only then invokes the actual generated
`ListWidgets` prepared decoder retained in `spec.preparedDecode`.

All wire construction, decoder selection, exact-field equivalence checks, and
warmup happen outside the timed region.  The baseline materializes six owned
cell `ByteArray`s per row; that count is printed explicitly for comparison with
the row-owned-span candidate.
-/

private abbrev Values := Array (Option ByteArray)
private abbrev Row := AcmeDb.Queries.ListWidgets.Row
private abbrev RowData := AcmeDb.Queries.ListWidgets.RowData

private abbrev PreparedDecoder :=
  Pgx.Typed.TypeResolver → Array Pgx.Typed.ResolvedType →
    Array Pg.Protocol.ColumnDesc → Values → Except Pgx.Typed.Error Row

private inductive WireMode where
  | mixed
  | allText
  deriving BEq

private structure Fixture where
  label : String
  messages : Array Pg.Protocol.RawMessage
  columns : Array Pg.Protocol.ColumnDesc
  expected : Array RowData
  expectedFirstRowChecksum : UInt64
  expectedLastRowChecksum : UInt64
  expectedBatchChecksum : UInt64
  wirePayloadBytes : Nat

private def formats : WireMode → Array UInt16
  | .mixed => #[1, 1, 0, 0, 1, 0]
  | .allText => #[0, 0, 0, 0, 0, 0]

private def makeColumns (mode : WireMode) : Array Pg.Protocol.ColumnDesc :=
  let fs := formats mode
  #[
    { name := "id", tableOid := 0, attnum := 1, typeOid := Pg.Oid.int8,
      typeSize := 8, typeMod := -1, format := fs[0]! },
    { name := "owner_id", tableOid := 0, attnum := 2, typeOid := Pg.Oid.int8,
      typeSize := 8, typeMod := -1, format := fs[1]! },
    { name := "name", tableOid := 0, attnum := 3, typeOid := Pg.Oid.text,
      typeSize := -1, typeMod := -1, format := fs[2]! },
    { name := "sku", tableOid := 0, attnum := 4, typeOid := Pg.Oid.text,
      typeSize := -1, typeMod := -1, format := fs[3]! },
    { name := "quantity", tableOid := 0, attnum := 5, typeOid := Pg.Oid.int8,
      typeSize := 8, typeMod := -1, format := fs[4]! },
    { name := "description", tableOid := 0, attnum := 6, typeOid := Pg.Oid.text,
      typeSize := -1, typeMod := -1, format := fs[5]! }
  ]

private def makeRow (index : Nat) : RowData :=
  { id := Int64.ofInt (1001 + index)
    ownerId := 7
    name := s!"Widget {index + 1}"
    sku := s!"WGT-{1001 + index}"
    quantity := Int64.ofInt (11 + index % 41)
    description := s!"row-owned span benchmark widget {index + 1}" }

private def encodeInt64 (mode : WireMode) (value : Int64) : ByteArray :=
  match mode with
  | .mixed => Pg.putInt64BE value
  | .allText => (toString value).toUTF8

private def wireValues (mode : WireMode) (row : RowData) : Values :=
  #[
    some (encodeInt64 mode row.id),
    some (encodeInt64 mode row.ownerId),
    some row.name.toUTF8,
    some row.sku.toUTF8,
    some (encodeInt64 mode row.quantity),
    some row.description.toUTF8
  ]

private def makeDataRow (values : Values) : Pg.Protocol.RawMessage := Id.run do
  let mut payload := Pg.Protocol.putUInt16 ByteArray.empty (UInt16.ofNat values.size)
  for value? in values do
    match value? with
    | none => payload := Pg.Protocol.putInt32 payload (-1)
    | some value =>
      payload := Pg.Protocol.putUInt32 payload (UInt32.ofNat value.size) ++ value
  return { tag := Pg.Protocol.BackendTag.dataRow.toUInt8, payload }

@[inline] private def rowChecksum (row : RowData) : UInt64 :=
  row.id.toUInt64 * 1000003 + row.ownerId.toUInt64 * 10007 +
    row.quantity.toUInt64 * 101 + UInt64.ofNat row.name.utf8ByteSize * 17 +
    UInt64.ofNat row.sku.utf8ByteSize * 13 +
    UInt64.ofNat row.description.utf8ByteSize

private def batchChecksum (rows : Array RowData) : UInt64 :=
  rows.foldl (fun checksum row => checksum + rowChecksum row) 0

private def makeFixture (label : String) (mode : WireMode)
    (expected : Array RowData) : Fixture :=
  let messages := expected.map (makeDataRow <| wireValues mode ·)
  let firstChecksum := (expected[0]?).map rowChecksum |>.getD 0
  let lastChecksum := (expected[expected.size - 1]?).map rowChecksum |>.getD 0
  { label
    messages
    columns := makeColumns mode
    expected
    expectedFirstRowChecksum := firstChecksum
    expectedLastRowChecksum := lastChecksum
    expectedBatchChecksum := batchChecksum expected
    wirePayloadBytes := messages.foldl (fun total message => total + message.payload.size) 0 }

private def rowDataEq (left right : RowData) : Bool :=
  left.id == right.id && left.ownerId == right.ownerId &&
    left.name == right.name && left.sku == right.sku &&
    left.quantity == right.quantity && left.description == right.description

/-- This is intentionally the same initially-empty, push-grown result shape
used by `Pg.Connection.foldExecute`; preallocating it would hide part of the
production ownership path selected for this experiment. -/
@[noinline] private def materializeRows
    (messages : @& Array Pg.Protocol.RawMessage) : Except String (Array Values) := do
  let mut rows : Array Values := #[]
  for message in messages do
    match Pg.Protocol.Backend.decode message with
    | .ok (.dataRow values) => rows := rows.push values
    | .ok other => throw s!"expected DataRow, decoded {repr other}"
    | .error error => throw error
  pure rows

@[noinline] private def decodeMaterializedRows (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (columns : @& Array Pg.Protocol.ColumnDesc) (rows : @& Array Values) :
    Except Pgx.Typed.Error (Array Row) :=
  rows.mapM (decode resolve types columns)

private def materializeAndDecode (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixture : @& Fixture) : Except String (Array Row) := do
  let materialized ← materializeRows fixture.messages
  match decodeMaterializedRows decode resolve types fixture.columns materialized with
  | .ok rows => pure rows
  | .error error => throw error.toMessage

@[noinline] private def runIterations (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixture : @& Fixture) (iterations : Nat) : IO UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    let rows ← match materializeAndDecode decode resolve types fixture with
      | .ok rows => pure rows
      | .error error => throw (IO.userError error)
    for row in rows do
      checksum := checksum + rowChecksum row.val
  pure checksum

private def validateRows (label : String) (actual : Array Row)
    (expected : Array RowData) : IO Unit := do
  unless actual.size == expected.size do
    throw (IO.userError
      s!"{label}: decoded {actual.size} rows; expected {expected.size}")
  for (actualRow, expectedRow) in actual.zip expected do
    unless rowDataEq actualRow.val expectedRow do
      throw (IO.userError s!"{label}: decoded row differs from the logical fixture")

private def validateFixture (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixture : @& Fixture) : IO Unit := do
  let rows ← match materializeAndDecode decode resolve types fixture with
    | .ok rows => pure rows
    | .error error => throw (IO.userError s!"{fixture.label}: {error}")
  validateRows fixture.label rows fixture.expected
  let actualChecksum := rows.foldl (fun total row => total + rowChecksum row.val) 0
  unless actualChecksum == fixture.expectedBatchChecksum do
    throw (IO.userError
      s!"{fixture.label}: batch checksum {actualChecksum} != {fixture.expectedBatchChecksum}")

private def validateEquivalence (mixed text : @& Fixture) : IO Unit := do
  unless mixed.expected.size == text.expected.size do
    throw (IO.userError "mixed/text controls have different row counts")
  for (mixedRow, textRow) in mixed.expected.zip text.expected do
    unless rowDataEq mixedRow textRow do
      throw (IO.userError "mixed/text logical row differs")
  unless mixed.expectedBatchChecksum == text.expectedBatchChecksum do
    throw (IO.userError "mixed/text logical batch checksums differ")

private def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
    if value <= head then value :: head :: tail else head :: insertSorted value tail

private def median (samples : Array Nat) : Nat :=
  let sorted := samples.toList.foldl (fun values sample => insertSorted sample values) []
  sorted[sorted.length / 2]?.getD 0

private def formatSamples (samples : Array Nat) : String :=
  String.intercalate "," (samples.toList.map toString)

private def formatVector (columns : Array Pg.Protocol.ColumnDesc) : String :=
  "[" ++ String.intercalate "," (columns.toList.map (toString ·.format)) ++ "]"

private def formatHundredths (value : Nat) : String :=
  let fraction := value % 100
  let fractionText := if fraction < 10 then s!"0{fraction}" else toString fraction
  s!"{value / 100}.{fractionText}"

private def reportFixture (fixture : @& Fixture) (iterations : Nat)
    (samples : Array Nat) (checksum : UInt64) : IO Unit := do
  let elapsed := median samples
  let batches := iterations
  let rows := fixture.expected.size * iterations
  let perBatch100 := if batches == 0 then 0 else elapsed * 100 / batches
  let perRow100 := if rows == 0 then 0 else elapsed * 100 / rows
  IO.println <| s!"case={fixture.label} rows_per_iteration={fixture.expected.size} " ++
    s!"formats={formatVector fixture.columns} wire_payload_bytes={fixture.wirePayloadBytes} " ++
    s!"materialized_cells_per_row=6 " ++
    s!"materialized_cells_per_batch={fixture.expected.size * 6}"
  IO.println <| s!"case={fixture.label} first_row_checksum={fixture.expectedFirstRowChecksum} " ++
    s!"last_row_checksum={fixture.expectedLastRowChecksum} " ++
    s!"batch_checksum={fixture.expectedBatchChecksum} measured_checksum={checksum}"
  IO.println s!"case={fixture.label} samples_ns={formatSamples samples} median_ns={elapsed}"
  IO.println <| s!"case={fixture.label} median_ns_per_batch={formatHundredths perBatch100} " ++
    s!"median_ns_per_row={formatHundredths perRow100}"

private def measureFixture (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixture : @& Fixture) (iterations rounds : Nat) : IO Unit := do
  -- Warm the exact combined path, but do not include it in any reported sample.
  let warmupIterations := Nat.min iterations 100
  let warmupChecksum ← runIterations decode resolve types fixture warmupIterations
  unless warmupChecksum == fixture.expectedBatchChecksum * UInt64.ofNat warmupIterations do
    throw (IO.userError s!"{fixture.label}: warmup checksum mismatch")
  let mut samples := #[]
  let expectedChecksum := fixture.expectedBatchChecksum * UInt64.ofNat iterations
  let mut measuredChecksum : UInt64 := 0
  for _ in [0:rounds] do
    let started ← IO.monoNanosNow
    let checksum ← runIterations decode resolve types fixture iterations
    let elapsed := (← IO.monoNanosNow) - started
    unless checksum == expectedChecksum do
      throw (IO.userError
        s!"{fixture.label}: measured checksum {checksum} != {expectedChecksum}")
    measuredChecksum := checksum
    samples := samples.push elapsed
  reportFixture fixture iterations samples measuredChecksum

private def parsePositive (name value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{name} must be a positive decimal integer")
  unless parsed > 0 do
    throw (IO.userError s!"{name} must be positive")
  pure parsed

private def parseArgs (args : List String) : IO (Nat × Nat) := do
  let (iterations, rounds) ← match args with
    | [] => pure (2000, 7)
    | [iterations] => pure (← parsePositive "iterations" iterations, 7)
    | [iterations, rounds] =>
      pure (← parsePositive "iterations" iterations, ← parsePositive "rounds" rounds)
    | _ => throw (IO.userError "usage: row_owned_span_benchmark [iterations] [rounds]")
  unless rounds >= 3 && rounds % 2 == 1 do
    throw (IO.userError "rounds must be an odd integer of at least 3")
  pure (iterations, rounds)

private def benchmark (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixtures : @& Array Fixture) (iterations rounds : Nat) : IO Unit := do
  IO.println "benchmark=row_owned_span_baseline_v1 representation=owned_cell_bytearrays"
  IO.println s!"iterations={iterations} rounds={rounds}"
  for fixture in fixtures do
    measureFixture decode resolve types fixture iterations rounds
  IO.println "row-owned span baseline benchmark completed"

def main (args : List String) : IO Unit := do
  let (iterations, rounds) ← parseArgs args
  let expected55 := Array.ofFn (n := 55) (fun i => makeRow i)
  let mixed55 := makeFixture "mixed_55" .mixed expected55
  let mixed1 := makeFixture "mixed_1" .mixed (expected55.extract 0 1)
  let text55 := makeFixture "all_text_55" .allText expected55
  let decode ← match AcmeDb.Queries.ListWidgets.spec.preparedDecode with
    | some decode => pure decode
    | none => throw (IO.userError "ListWidgets has no generated prepared decoder")
  -- `ListWidgets` consists entirely of planned built-ins, so its generated
  -- decoder intentionally ignores the resolver/type array and dispatches from
  -- the already-validated physical ColumnDesc OID/format pair.  A fail-closed
  -- resolver makes any future generated dependency visible to this benchmark.
  let resolve : Pgx.Typed.TypeResolver := fun key =>
    throw (.queryDrift s!"benchmark did not resolve unexpected nested type {repr key}")
  let types : Array Pgx.Typed.ResolvedType := #[]
  validateEquivalence mixed55 text55
  validateFixture decode resolve types mixed55
  validateFixture decode resolve types mixed1
  validateFixture decode resolve types text55
  -- Crossing a task boundary matches the multi-threaded ownership regime of
  -- the service while keeping all fixture construction outside timed regions.
  let task ← IO.asTask (benchmark decode resolve types #[mixed55, mixed1, text55]
    iterations rounds)
  match ← IO.wait task with
  | .ok () => pure ()
  | .error error => throw error
