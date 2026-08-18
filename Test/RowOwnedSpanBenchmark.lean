import AcmeDb
import Pg.Protocol.Backend

/-!
Focused reference-versus-candidate harness for proof-bounded prepared-span
decoding.

The selected counter loop deliberately starts at an already-framed
`RawMessage`: the experiment does not change the framer's payload copy.  Each
iteration runs the production `Backend.decodeDataRowSpans`, grows the same
owned row-array shape as `Pg.Connection.foldExecute`, and only then invokes the
selected prepared decoder.

The `reference` mode reproduces the former generated six-built-in decoder:
ordered arity guards followed by checked column and span lookups.  The
`candidate` mode invokes the actual generated `ListWidgets` decoder, whose
arity proofs drive proof-indexed column and span access.  Untimed controls pin
exact fields, errors, and first-error order before the selected loop runs.

The executable is intended for whole-process deterministic counters.  Fixture
construction, semantic controls, one task boundary, and the requested warmup
are therefore part of process counters; only the fixed-iteration selected
`mixed_1` or `mixed_55` loop scales with `iterations`.
-/

private abbrev Values := Array (Option ByteArray)
private abbrev Row := AcmeDb.Queries.ListWidgets.Row
private abbrev RowData := AcmeDb.Queries.ListWidgets.RowData

private abbrev PreparedDecoder :=
  Pgx.Typed.TypeResolver → Array Pgx.Typed.ResolvedType →
    Array Pg.Protocol.ColumnDesc → Pg.Protocol.DataRowSpans → Except Pgx.Typed.Error Row

private inductive DecodeMode where
  | reference
  | candidate

private inductive FixtureMode where
  | mixed1
  | mixed55

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

/-- Exact pre-change generated `ListWidgets` prepared-span decoder.  Keep this
as the stable compatibility oracle for both semantic and counter comparisons. -/
@[noinline] private def referenceDecode : PreparedDecoder := fun resolve types columns values => do
  let _ := resolve
  let _ := types
  unless columns.size == 6 do
    throw (.queryDrift "generated decoder expected 6 column descriptors")
  unless values.size == 6 do
    throw (.queryDrift "generated decoder expected 6 row values")
  let id ← Pgx.Typed.decodePlannedBuiltinSpan (α := Int64)
    columns[0]!.typeOid columns[0]!.format values 0
  let ownerId ← Pgx.Typed.decodePlannedBuiltinSpan (α := Int64)
    columns[1]!.typeOid columns[1]!.format values 1
  let name ← Pgx.Typed.decodePlannedBuiltinSpan (α := String)
    columns[2]!.typeOid columns[2]!.format values 2
  let sku ← Pgx.Typed.decodePlannedBuiltinSpan (α := String)
    columns[3]!.typeOid columns[3]!.format values 3
  let quantity ← Pgx.Typed.decodePlannedBuiltinSpan (α := Int64)
    columns[4]!.typeOid columns[4]!.format values 4
  let description ← Pgx.Typed.decodePlannedBuiltinSpan (α := String)
    columns[5]!.typeOid columns[5]!.format values 5
  let rowData : RowData := { id, ownerId, name, sku, quantity, description }
  match AcmeDb.Queries.ListWidgets.validate rowData with
  | .ok refined => pure refined
  | .error violation => throw (Pgx.Typed.Error.constraintViolation violation)

private structure DecoderBox where
  decode : PreparedDecoder
  /-- Keep the selection result boxed across the opaque boundary. -/
  candidateSelected : Bool

/-- Select the decoder once without letting function-return eta expansion give
either mode a different per-row call shape inside the counter loop. -/
@[noinline] private opaque selectDecoderBox
    (mode : DecodeMode) (candidate : PreparedDecoder) : DecoderBox :=
  match mode with
  | .reference => { decode := referenceDecode, candidateSelected := false }
  | .candidate => { decode := candidate, candidateSelected := true }

/-- This is intentionally the same initially-empty, push-grown result shape
used by `Pg.Connection.foldExecute`; preallocating it would hide part of the
production ownership path selected for this experiment. -/
@[noinline] private def retainSpanRows
    (messages : @& Array Pg.Protocol.RawMessage) : Except String (Array Pg.Protocol.DataRowSpans) := do
  let mut rows : Array Pg.Protocol.DataRowSpans := #[]
  for message in messages do
    match Pg.Protocol.Backend.decodeDataRowSpans message with
    | .ok values => rows := rows.push values
    | .error error => throw error
  pure rows

@[noinline] private def decodeSpanRows (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (columns : @& Array Pg.Protocol.ColumnDesc) (rows : @& Array Pg.Protocol.DataRowSpans) :
    Except Pgx.Typed.Error (Array Row) :=
  rows.mapM (decode resolve types columns)

private def retainAndDecode (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixture : @& Fixture) : Except String (Array Row) := do
  let rows ← retainSpanRows fixture.messages
  match decodeSpanRows decode resolve types fixture.columns rows with
  | .ok rows => pure rows
  | .error error => throw error.toMessage

@[noinline] private def runIterations (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixture : @& Fixture) (iterations : Nat) : IO UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    let rows ← match retainAndDecode decode resolve types fixture with
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
  let rows ← match retainAndDecode decode resolve types fixture with
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

private structure RowSnapshot where
  id : Int64
  ownerId : Int64
  name : String
  sku : String
  quantity : Int64
  description : String
  deriving Repr, BEq

private def RowSnapshot.ofRowData (row : RowData) : RowSnapshot := {
  id := row.id
  ownerId := row.ownerId
  name := row.name
  sku := row.sku
  quantity := row.quantity
  description := row.description
}

private inductive DecodeSnapshot where
  | ok (row : RowSnapshot)
  | error (kind : Pgx.Typed.ErrorKind) (message : String)
  deriving Repr, BEq

private structure SemanticCase where
  label : String
  columns : Array Pg.Protocol.ColumnDesc
  message : Pg.Protocol.RawMessage
  expected : DecodeSnapshot

private def queryDrift (message : String) : DecodeSnapshot :=
  .error .queryDrift s!"query drift: {message}"

private def decodeError (message : String) : DecodeSnapshot :=
  .error .decode s!"row decoding failed: {message}"

private def snapshotDecode (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixture : @& SemanticCase) : Except String DecodeSnapshot := do
  let values ← Pg.Protocol.Backend.decodeDataRowSpans fixture.message
  match decode resolve types fixture.columns values with
  | .ok row => pure (.ok (.ofRowData row.val))
  | .error error => pure (.error error.kind error.toMessage)

private def semanticCases : Array SemanticCase :=
  let expected := makeRow 0
  let baseColumns := makeColumns .mixed
  let baseValues := wireValues .mixed expected
  let success := DecodeSnapshot.ok (.ofRowData expected)
  #[
    {
      label := "success"
      columns := baseColumns
      message := makeDataRow baseValues
      expected := success
    },
    {
      label := "short-columns"
      columns := baseColumns.extract 0 5
      message := makeDataRow baseValues
      expected := queryDrift "generated decoder expected 6 column descriptors"
    },
    {
      label := "long-columns"
      columns := baseColumns.push {
        name := "extra", tableOid := 0, attnum := 7, typeOid := Pg.Oid.text,
        typeSize := -1, typeMod := -1, format := 0
      }
      message := makeDataRow baseValues
      expected := queryDrift "generated decoder expected 6 column descriptors"
    },
    {
      label := "short-row"
      columns := baseColumns
      message := makeDataRow (baseValues.extract 0 5)
      expected := queryDrift "generated decoder expected 6 row values"
    },
    {
      label := "long-row"
      columns := baseColumns
      message := makeDataRow (baseValues.push (some "extra".toUTF8))
      expected := queryDrift "generated decoder expected 6 row values"
    },
    {
      label := "columns-precede-row"
      columns := baseColumns.extract 0 5
      message := makeDataRow (baseValues.extract 0 5)
      expected := queryDrift "generated decoder expected 6 column descriptors"
    },
    {
      label := "nonnull-null"
      columns := baseColumns
      message := makeDataRow (baseValues.set! 0 none)
      expected := decodeError "unexpected NULL"
    },
    {
      label := "malformed-binary"
      columns := baseColumns
      message := makeDataRow (baseValues.set! 0 (some (ByteArray.mk #[0xff])))
      expected := decodeError "unexpected integer width 1"
    },
    {
      label := "invalid-utf8"
      columns := baseColumns
      message := makeDataRow (baseValues.set! 2 (some (ByteArray.mk #[0xff])))
      expected := decodeError "text value is not valid UTF-8"
    },
    {
      label := "first-cell-error"
      columns := baseColumns
      message := makeDataRow <|
        (baseValues.set! 0 (some (ByteArray.mk #[0xff]))).set! 2
          (some (ByteArray.mk #[0xff]))
      expected := decodeError "unexpected integer width 1"
    }
  ]

private def validateSemanticParity (candidate : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver)
    (types : @& Array Pgx.Typed.ResolvedType) : IO Nat := do
  for fixture in semanticCases do
    let reference ← match snapshotDecode referenceDecode resolve types fixture with
      | .ok result => pure result
      | .error error => throw (IO.userError s!"{fixture.label}: reference setup: {error}")
    let candidate ← match snapshotDecode candidate resolve types fixture with
      | .ok result => pure result
      | .error error => throw (IO.userError s!"{fixture.label}: candidate setup: {error}")
    unless reference == fixture.expected do
      throw (IO.userError
        s!"{fixture.label}: reference differs from expected: {reprStr reference}")
    unless candidate == fixture.expected do
      throw (IO.userError
        s!"{fixture.label}: candidate differs from expected: {reprStr candidate}")
    unless reference == candidate do
      throw (IO.userError s!"{fixture.label}: reference and candidate differ")
  pure semanticCases.size

private def formatVector (columns : Array Pg.Protocol.ColumnDesc) : String :=
  "[" ++ String.intercalate "," (columns.toList.map (toString ·.format)) ++ "]"

private def runSelected (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixture : @& Fixture) (iterations warmup : Nat) : IO UInt64 := do
  let warmupChecksum ← runIterations decode resolve types fixture warmup
  unless warmupChecksum == fixture.expectedBatchChecksum * UInt64.ofNat warmup do
    throw (IO.userError s!"{fixture.label}: warmup checksum mismatch")
  let expectedChecksum := fixture.expectedBatchChecksum * UInt64.ofNat iterations
  let checksum ← runIterations decode resolve types fixture iterations
  unless checksum == expectedChecksum do
    throw (IO.userError
      s!"{fixture.label}: measured checksum {checksum} != {expectedChecksum}")
  pure checksum

private def parseNatural (name value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{name} must be a nonnegative decimal integer")
  pure parsed

private structure Options where
  mode : DecodeMode
  modeName : String
  fixture : FixtureMode
  fixtureName : String
  iterations : Nat
  warmup : Nat

private def parseArgs (args : List String) : IO Options := do
  let (modeName, fixtureName, iterations, warmup) ← match args with
    | [mode, fixture, iterations, warmup] =>
      pure (mode, fixture,
        ← parseNatural "iterations" iterations,
        ← parseNatural "warmup" warmup)
    | _ => throw (IO.userError <|
        "usage: row_owned_span_benchmark " ++
          "(reference|candidate) (mixed_1|mixed_55) iterations warmup")
  let mode ← match modeName with
    | "reference" => pure DecodeMode.reference
    | "candidate" => pure DecodeMode.candidate
    | _ => throw (IO.userError "mode must be reference or candidate")
  let fixture ← match fixtureName with
    | "mixed_1" => pure FixtureMode.mixed1
    | "mixed_55" => pure FixtureMode.mixed55
    | _ => throw (IO.userError "fixture must be mixed_1 or mixed_55")
  pure { mode, modeName, fixture, fixtureName, iterations, warmup }

def main (args : List String) : IO Unit := do
  let options ← parseArgs args
  let expected55 := Array.ofFn (n := 55) (fun i => makeRow i)
  let mixed55 := makeFixture "mixed_55" .mixed expected55
  let mixed1 := makeFixture "mixed_1" .mixed (expected55.extract 0 1)
  let text55 := makeFixture "all_text_55" .allText expected55
  let candidate ← match AcmeDb.Queries.ListWidgets.spec.preparedSpanDecode with
    | some decode => pure decode
    | none => throw (IO.userError "ListWidgets has no generated span decoder")
  -- `ListWidgets` consists entirely of planned built-ins, so its generated
  -- decoder intentionally ignores the resolver/type array and dispatches from
  -- the already-validated physical ColumnDesc OID/format pair.  A fail-closed
  -- resolver makes any future generated dependency visible to this benchmark.
  let resolve : Pgx.Typed.TypeResolver := fun key =>
    throw (.queryDrift s!"benchmark did not resolve unexpected nested type {repr key}")
  let types : Array Pgx.Typed.ResolvedType := #[]
  validateEquivalence mixed55 text55
  for fixture in #[mixed55, mixed1, text55] do
    validateFixture referenceDecode resolve types fixture
    validateFixture candidate resolve types fixture
  let semanticCaseCount ← validateSemanticParity candidate resolve types
  let decoderBox := selectDecoderBox options.mode candidate
  let decode := decoderBox.decode
  let fixture := match options.fixture with
    | .mixed1 => mixed1
    | .mixed55 => mixed55
  -- Crossing a task boundary matches the multi-threaded ownership regime of
  -- the service. Whole-process counters also include the fixed setup above.
  let task ← IO.asTask
    (runSelected decode resolve types fixture options.iterations options.warmup)
  let checksum ← match ← IO.wait task with
  | .ok checksum => pure checksum
  | .error error => throw error
  let materializedCellsPerRow := fixture.columns.foldl (fun count column =>
    if column.format == 1 then count else count + 1) 0
  IO.println <| s!"benchmark=row_owned_span_decode_v2 mode={options.modeName} " ++
    s!"case={options.fixtureName} iterations={options.iterations} warmup={options.warmup}"
  IO.println <| "counter_scope=whole_process " ++
    s!"semantic_cases={semanticCaseCount} success_controls=reference,candidate " ++
    "task_boundary=one measured_loop=retain_spans,decode_six_fields,validate,consume"
  IO.println <| s!"rows_per_iteration={fixture.expected.size} " ++
    s!"formats={formatVector fixture.columns} wire_payload_bytes={fixture.wirePayloadBytes} " ++
    s!"materialized_cells_per_row={materializedCellsPerRow} " ++
    s!"materialized_cells_per_batch={fixture.expected.size * materializedCellsPerRow}"
  IO.println <| s!"first_row_checksum={fixture.expectedFirstRowChecksum} " ++
    s!"last_row_checksum={fixture.expectedLastRowChecksum} " ++
    s!"batch_checksum={fixture.expectedBatchChecksum} measured_checksum={checksum}"
  IO.println "row-owned span decode benchmark completed"
