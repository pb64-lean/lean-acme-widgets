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

The `reference`/`candidate` pair retains the earlier checked-access comparison.
The generated-batch comparison invokes the exact production `bundle.many`
callback from separately frozen baseline and candidate binaries.  Matching,
all-text fallback, and late-mismatch vectors at 0/1/55 rows distinguish fixed
batch-selection work from row-scaled decoding.  Untimed controls pin exact
fields, runtime formats/OIDs, errors, and first-error order before the selected
loop runs.

The executable is intended for whole-process deterministic counters.  Fixture
construction, semantic controls, one task boundary, and the requested warmup
are therefore part of process counters; only the fixed-iteration selected
fixture loop scales with `iterations`.
-/

private abbrev Values := Array (Option ByteArray)
private abbrev Row := AcmeDb.Queries.ListWidgets.Row
private abbrev RowData := AcmeDb.Queries.ListWidgets.RowData

private abbrev PreparedDecoder :=
  Pgx.Typed.TypeResolver → Array Pgx.Typed.ResolvedType →
    Array Pg.Protocol.ColumnDesc → Pg.Protocol.DataRowSpans → Except Pgx.Typed.Error Row

private abbrev PreparedBatchDecoder :=
  Pgx.Typed.TypeResolver → Array Pgx.Typed.ResolvedType →
    Array Pg.Protocol.ColumnDesc → Array Pg.Protocol.DataRowSpans →
      Except Pgx.Typed.Error (Array Row)

private inductive DecodeMode where
  | reference
  | candidate
  | currentMany
  | batchMany

private inductive FixtureMode where
  | mixed0
  | mixed1
  | mixed55
  | text0
  | text1
  | text55
  | late1
  | late55

private inductive WireMode where
  | mixed
  | allText
  | lateMismatch
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
  | .lateMismatch => #[1, 1, 0, 0, 1, 1]

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
  | .mixed | .lateMismatch => Pg.putInt64BE value
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
  decode : PreparedBatchDecoder
  /-- Keep the selection result boxed across the opaque boundary. -/
  candidateSelected : Bool

@[noinline] private def decodeCurrentMany (decode : @& PreparedDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (columns : @& Array Pg.Protocol.ColumnDesc)
    (rows : @& Array Pg.Protocol.DataRowSpans) : Except Pgx.Typed.Error (Array Row) :=
  rows.mapM fun values => do
    unless values.size == 6 do
      throw (.queryDrift s!"data row has {values.size} fields; expected 6")
    decode resolve types columns values

/-- Select one complete batch decoder outside the measured loop. -/
@[noinline] private opaque selectDecoderBox
    (mode : DecodeMode) (candidate : PreparedDecoder)
    (batchCandidate : PreparedBatchDecoder) : DecoderBox :=
  match mode with
  | .reference => {
      decode := fun resolve types columns rows =>
        rows.mapM (referenceDecode resolve types columns)
      candidateSelected := false
    }
  | .candidate => {
      decode := fun resolve types columns rows =>
        rows.mapM (candidate resolve types columns)
      candidateSelected := true
    }
  | .currentMany => {
      decode := decodeCurrentMany candidate
      candidateSelected := true
    }
  | .batchMany => {
      decode := batchCandidate
      candidateSelected := true
    }

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

@[noinline] private def decodeSpanRows (decode : @& PreparedBatchDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (columns : @& Array Pg.Protocol.ColumnDesc) (rows : @& Array Pg.Protocol.DataRowSpans) :
    Except Pgx.Typed.Error (Array Row) :=
  decode resolve types columns rows

private def retainAndDecode (decode : @& PreparedBatchDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixture : @& Fixture) : Except String (Array Row) := do
  let rows ← retainSpanRows fixture.messages
  match decodeSpanRows decode resolve types fixture.columns rows with
  | .ok rows => pure rows
  | .error error => throw error.toMessage

@[noinline] private def runIterations (decode : @& PreparedBatchDecoder)
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
  let decodeRows : PreparedBatchDecoder := fun resolve types columns rows =>
    rows.mapM (decode resolve types columns)
  let rows ← match retainAndDecode decodeRows resolve types fixture with
    | .ok rows => pure rows
    | .error error => throw (IO.userError s!"{fixture.label}: {error}")
  validateRows fixture.label rows fixture.expected
  let actualChecksum := rows.foldl (fun total row => total + rowChecksum row.val) 0
  unless actualChecksum == fixture.expectedBatchChecksum do
    throw (IO.userError
      s!"{fixture.label}: batch checksum {actualChecksum} != {fixture.expectedBatchChecksum}")

private def validateBatchFixture (decode : @& PreparedBatchDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (fixture : @& Fixture) : IO Unit := do
  let rows ← match retainAndDecode decode resolve types fixture with
    | .ok rows => pure rows
    | .error error => throw (IO.userError s!"{fixture.label}: generated batch: {error}")
  validateRows (fixture.label ++ " generated batch") rows fixture.expected
  let actualChecksum := rows.foldl (fun total row => total + rowChecksum row.val) 0
  unless actualChecksum == fixture.expectedBatchChecksum do
    throw (IO.userError <|
      s!"{fixture.label}: generated batch checksum {actualChecksum} != " ++
        s!"{fixture.expectedBatchChecksum}")

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

private inductive BatchDecodeSnapshot where
  | ok (rows : Array RowSnapshot)
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

private def snapshotBatchDecode (decode : @& PreparedBatchDecoder)
    (resolve : @& Pgx.Typed.TypeResolver) (types : @& Array Pgx.Typed.ResolvedType)
    (columns : @& Array Pg.Protocol.ColumnDesc)
    (messages : @& Array Pg.Protocol.RawMessage) : Except String BatchDecodeSnapshot := do
  let rows ← retainSpanRows messages
  match decode resolve types columns rows with
  | .ok decoded => pure (.ok <| decoded.map fun row => RowSnapshot.ofRowData row.val)
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

private structure BatchSemanticCase where
  label : String
  columns : Array Pg.Protocol.ColumnDesc
  messages : Array Pg.Protocol.RawMessage
  expected : BatchDecodeSnapshot

private def batchSemanticCases : Array BatchSemanticCase :=
  let expected := makeRow 0
  let baseColumns := makeColumns .mixed
  let baseValues := wireValues .mixed expected
  let textValues := wireValues .allText expected
  let noncanonicalColumns := baseColumns.set! 5 {
    baseColumns[5]! with format := 2
  }
  let success := BatchDecodeSnapshot.ok #[.ofRowData expected]
  let uuidBytes := ByteArray.mk #[
    0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
    0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff
  ]
  let uuidColumns := baseColumns.set! 2 {
    baseColumns[2]! with typeOid := Pg.Oid.uuid, format := 1
  }
  let uuidExpected := {
    expected with name := "00112233-4455-6677-8899-aabbccddeeff"
  }
  let shortRow := makeDataRow (baseValues.extract 0 5)
  let malformedFirst := makeDataRow (baseValues.set! 0 (some (ByteArray.mk #[0xff])))
  #[
    {
      label := "mixed-success"
      columns := baseColumns
      messages := #[makeDataRow baseValues]
      expected := success
    },
    {
      label := "all-text-runtime-formats"
      columns := makeColumns .allText
      messages := #[makeDataRow textValues]
      expected := success
    },
    {
      label := "noncanonical-text-format-fallback"
      columns := noncanonicalColumns
      messages := #[makeDataRow baseValues]
      expected := success
    },
    {
      label := "runtime-uuid-oid"
      columns := uuidColumns
      messages := #[makeDataRow (baseValues.set! 2 (some uuidBytes))]
      expected := .ok #[.ofRowData uuidExpected]
    },
    {
      label := "bad-columns-empty-batch"
      columns := baseColumns.extract 0 5
      messages := #[]
      expected := .ok #[]
    },
    {
      label := "bad-columns-malformed-first-row"
      columns := baseColumns.extract 0 5
      messages := #[shortRow]
      expected := .error .queryDrift
        "query drift: data row has 5 fields; expected 6"
    },
    {
      label := "bad-columns-valid-first-row"
      columns := baseColumns.extract 0 5
      messages := #[makeDataRow baseValues]
      expected := .error .queryDrift
        "query drift: generated decoder expected 6 column descriptors"
    },
    {
      label := "later-malformed-row"
      columns := baseColumns
      messages := #[makeDataRow baseValues, shortRow]
      expected := .error .queryDrift
        "query drift: data row has 5 fields; expected 6"
    },
    {
      label := "earlier-decode-error-precedes-later-arity"
      columns := baseColumns
      messages := #[malformedFirst, shortRow]
      expected := .error .decode "row decoding failed: unexpected integer width 1"
    },
    {
      label := "leftmost-field-error"
      columns := baseColumns
      messages := #[makeDataRow <|
        (baseValues.set! 0 (some (ByteArray.mk #[0xff]))).set! 2
          (some (ByteArray.mk #[0xff]))]
      expected := .error .decode "row decoding failed: unexpected integer width 1"
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

private def validateBatchSemanticParity
    (bundle : @& Pgx.Typed.PreparedSpanDecoderBundle Row)
    (resolve : @& Pgx.Typed.TypeResolver)
    (types : @& Array Pgx.Typed.ResolvedType) : IO Nat := do
  let guarded : PreparedBatchDecoder :=
    Pgx.Typed.guardedPreparedSpanRows bundle.expectedColumns bundle.row
  for fixture in batchSemanticCases do
    let candidate ← match snapshotBatchDecode bundle.many resolve types
        fixture.columns fixture.messages with
      | .ok result => pure result
      | .error error => throw (IO.userError s!"{fixture.label}: batch setup: {error}")
    let reference ← match snapshotBatchDecode guarded resolve types
        fixture.columns fixture.messages with
      | .ok result => pure result
      | .error error => throw (IO.userError s!"{fixture.label}: guarded setup: {error}")
    unless reference == fixture.expected do
      throw (IO.userError
        s!"{fixture.label}: guarded decoder differs from expected: {reprStr reference}")
    unless candidate == fixture.expected do
      throw (IO.userError
        s!"{fixture.label}: batch decoder differs from expected: {reprStr candidate}")
    unless reference == candidate do
      throw (IO.userError s!"{fixture.label}: guarded and batch decoders differ")
  pure batchSemanticCases.size

private def formatVector (columns : Array Pg.Protocol.ColumnDesc) : String :=
  "[" ++ String.intercalate "," (columns.toList.map (toString ·.format)) ++ "]"

/-- ListWidgets' three String fields use the generic binary-span fallback and
therefore materialize an exact cell even when their runtime format is binary.
Every text-format field materializes for UTF-8 validation as well. -/
private def materializedCellsPerRow (columns : Array Pg.Protocol.ColumnDesc) : Nat :=
  (Array.range columns.size).foldl (init := 0) fun count index =>
    if columns[index]!.format != 1 || index == 2 || index == 3 || index == 5 then
      count + 1
    else
      count

private def runSelected (decode : @& PreparedBatchDecoder)
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
          "(reference|candidate|current_many|batch_many) " ++
          "(mixed_0|mixed_1|mixed_55|text_0|text_1|text_55|late_1|late_55) " ++
          "iterations warmup")
  let mode ← match modeName with
    | "reference" => pure DecodeMode.reference
    | "candidate" => pure DecodeMode.candidate
    | "current_many" => pure DecodeMode.currentMany
    | "batch_many" => pure DecodeMode.batchMany
    | _ => throw (IO.userError
        "mode must be reference, candidate, current_many, or batch_many")
  let fixture ← match fixtureName with
    | "mixed_0" => pure FixtureMode.mixed0
    | "mixed_1" => pure FixtureMode.mixed1
    | "mixed_55" => pure FixtureMode.mixed55
    | "text_0" => pure FixtureMode.text0
    | "text_1" => pure FixtureMode.text1
    | "text_55" => pure FixtureMode.text55
    | "late_1" => pure FixtureMode.late1
    | "late_55" => pure FixtureMode.late55
    | _ => throw (IO.userError <|
        "fixture must be mixed_0, mixed_1, mixed_55, text_0, text_1, " ++
          "text_55, late_1, or late_55")
  pure { mode, modeName, fixture, fixtureName, iterations, warmup }

def main (args : List String) : IO Unit := do
  let options ← parseArgs args
  let expected55 := Array.ofFn (n := 55) (fun i => makeRow i)
  let expected1 := expected55.extract 0 1
  let expected0 := expected55.extract 0 0
  let mixed0 := makeFixture "mixed_0" .mixed expected0
  let mixed55 := makeFixture "mixed_55" .mixed expected55
  let mixed1 := makeFixture "mixed_1" .mixed expected1
  let text0 := makeFixture "text_0" .allText expected0
  let text1 := makeFixture "text_1" .allText expected1
  let text55 := makeFixture "all_text_55" .allText expected55
  let late1 := makeFixture "late_1" .lateMismatch expected1
  let late55 := makeFixture "late_55" .lateMismatch expected55
  let candidate ← match AcmeDb.Queries.ListWidgets.spec.preparedSpanDecode with
    | some decode => pure decode
    | none => throw (IO.userError "ListWidgets has no generated span decoder")
  let bundle ← match AcmeDb.Queries.ListWidgets.spec.preparedSpanDecoderBundle with
    | some bundle => pure bundle
    | none => throw (IO.userError
        "ListWidgets has no generated prepared-span decoder bundle")
  unless AcmeDb.Queries.ListWidgets.spec.resultFormats == formats .mixed do
    throw (IO.userError "ListWidgets generated result-format vector changed")
  unless bundle.expectedColumns == 6 do
    throw (IO.userError "ListWidgets bundle expected-column count changed")
  -- `ListWidgets` consists entirely of planned built-ins, so its generated
  -- decoder intentionally ignores the resolver/type array and dispatches from
  -- the already-validated physical ColumnDesc OID/format pair.  A fail-closed
  -- resolver makes any future generated dependency visible to this benchmark.
  let resolve : Pgx.Typed.TypeResolver := fun key =>
    throw (.queryDrift s!"benchmark did not resolve unexpected nested type {repr key}")
  let types : Array Pgx.Typed.ResolvedType := #[]
  let currentManyControl :=
    (selectDecoderBox .currentMany candidate bundle.many).decode
  validateEquivalence mixed55 text55
  validateEquivalence mixed55 late55
  for fixture in #[mixed0, mixed1, mixed55, text0, text1, text55, late1, late55] do
    validateFixture referenceDecode resolve types fixture
    validateFixture candidate resolve types fixture
    validateBatchFixture currentManyControl resolve types fixture
    validateBatchFixture bundle.many resolve types fixture
  let semanticCaseCount ← validateSemanticParity candidate resolve types
  let batchSemanticCaseCount ← validateBatchSemanticParity bundle resolve types
  let decoderBox := selectDecoderBox options.mode candidate bundle.many
  let decode := decoderBox.decode
  let fixture := match options.fixture with
    | .mixed0 => mixed0
    | .mixed1 => mixed1
    | .mixed55 => mixed55
    | .text0 => text0
    | .text1 => text1
    | .text55 => text55
    | .late1 => late1
    | .late55 => late55
  -- Crossing a task boundary matches the multi-threaded ownership regime of
  -- the service. Whole-process counters also include the fixed setup above.
  let task ← IO.asTask
    (runSelected decode resolve types fixture options.iterations options.warmup)
  let checksum ← match ← IO.wait task with
  | .ok checksum => pure checksum
  | .error error => throw error
  let materializedPerRow := materializedCellsPerRow fixture.columns
  IO.println <| s!"benchmark=row_owned_span_decode_v4 mode={options.modeName} " ++
    s!"case={options.fixtureName} iterations={options.iterations} warmup={options.warmup}"
  IO.println <| "counter_scope=whole_process " ++
    s!"row_semantic_cases={semanticCaseCount} " ++
    s!"batch_semantic_cases={batchSemanticCaseCount} " ++
    "success_controls=reference,candidate,current_many,generated_batch " ++
    "task_boundary=one measured_loop=retain_spans,decode_six_fields,validate,consume"
  IO.println "routing_scope=decoder_body callback_selected_once=true bundle_width_dispatch=excluded"
  IO.println <| s!"rows_per_iteration={fixture.expected.size} " ++
    s!"formats={formatVector fixture.columns} wire_payload_bytes={fixture.wirePayloadBytes} " ++
    s!"materialized_cells_per_row={materializedPerRow} " ++
    s!"materialized_cells_per_batch={fixture.expected.size * materializedPerRow}"
  IO.println <| s!"first_row_checksum={fixture.expectedFirstRowChecksum} " ++
    s!"last_row_checksum={fixture.expectedLastRowChecksum} " ++
    s!"batch_checksum={fixture.expectedBatchChecksum} measured_checksum={checksum}"
  IO.println "row-owned span decode benchmark completed"
