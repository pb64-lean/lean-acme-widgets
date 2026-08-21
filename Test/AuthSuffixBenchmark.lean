import Acme.Auth

/-!
Deterministic auth-only comparison harness. `copied_suffix` is the former
production composition; `borrowed_suffix` is `TokenTable.authenticate`.
Run one mode/metadata size per process under an instruction counter.
-/

private def authenticateCopiedSuffix (table : Acme.Auth.TokenTable)
    (metadata : Grpc.Metadata) : Except Grpc.Status Acme.Auth.Principal :=
  match Acme.Auth.bearerToken? metadata with
  | none => .error (Grpc.Status.error .unauthenticated
      "missing authorization bearer token")
  | some token =>
    match table.lookup? token with
    | some principal => .ok principal
    | none => .error (Grpc.Status.error .unauthenticated "unknown bearer token")

private def metadataOfSize (size : Nat) : Grpc.Metadata := Id.run do
  let mut metadata := Grpc.Metadata.empty
  for index in [0:size - 1] do
    metadata := metadata.insert s!"x-benchmark-{index}" "ignored"
  metadata := metadata.insert "authorization" "Bearer acme-editor-8"
  return metadata

private def runIterations
    (authenticate : Acme.Auth.TokenTable → Grpc.Metadata →
      Except Grpc.Status Acme.Auth.Principal)
    (table : Acme.Auth.TokenTable) (metadata : Grpc.Metadata)
    (iterations : Nat) : IO UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    match authenticate table metadata with
    | .ok principal =>
      checksum := checksum + principal.id.val + principal.roles.val.size.toUInt64
    | .error status => throw (IO.userError s!"benchmark authentication failed: {repr status}")
  pure checksum

private def parsePositive (label value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{label} must be a positive decimal integer")
  unless parsed > 0 do
    throw (IO.userError s!"{label} must be positive")
  pure parsed

def main (args : List String) : IO Unit := do
  let (mode, metadataSize, iterations) ← match args with
    | [mode, size, iterations] =>
      pure (mode, ← parsePositive "metadata size" size, ← parsePositive "iterations" iterations)
    | _ => throw (IO.userError
        "usage: auth_suffix_benchmark (copied_suffix|borrowed_suffix) (1|4|16) iterations")
  unless metadataSize == 1 || metadataSize == 4 || metadataSize == 16 do
    throw (IO.userError "metadata size must be 1, 4, or 16")
  let metadata := metadataOfSize metadataSize
  unless metadata.size == metadataSize do
    throw (IO.userError "metadata fixture has the wrong number of headers")
  let authenticate ← match mode with
    | "copied_suffix" => pure authenticateCopiedSuffix
    | "borrowed_suffix" => pure Acme.Auth.authenticate
    | _ => throw (IO.userError "mode must be copied_suffix or borrowed_suffix")
  let expectedPerIteration : UInt64 := 9
  let expected := expectedPerIteration * UInt64.ofNat iterations
  let checksum ← runIterations authenticate Acme.Auth.demoTable metadata iterations
  unless checksum == expected do
    throw (IO.userError s!"checksum {checksum} != expected {expected}")
  IO.println <| s!"benchmark=auth_suffix mode={mode} metadata_headers={metadataSize} " ++
    s!"iterations={iterations} checksum={checksum}"
