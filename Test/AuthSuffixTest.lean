import Acme.Auth

/-!
Focused differential coverage for allocation-free bearer-token lookup.  The
reference is the former production composition: select the last authorization
value, copy the suffix returned by `bearerToken?`, then use `TokenTable.lookup?`.
-/

private def referenceAuthenticate (table : Acme.Auth.TokenTable)
    (metadata : _root_.Http2.Headers) : Except Grpc.Status Acme.Auth.Principal :=
  match Acme.Auth.bearerToken? metadata with
  | none => .error (Grpc.Status.error .unauthenticated
      "missing authorization bearer token")
  | some token =>
    match table.lookup? token with
    | some principal => .ok principal
    | none => .error (Grpc.Status.error .unauthenticated "unknown bearer token")

private inductive Expected where
  | principal (id : UInt64) (roles : Array String)
  | failure (detail : String)

private structure Fixture where
  label : String
  metadata : _root_.Http2.Headers
  expected : Expected

private def authorizationValues (values : Array String) : _root_.Http2.Headers :=
  values.foldl (fun metadata value => metadata.insert "authorization" value)
    _root_.Http2.Headers.empty

private def sameAuthentication
    (left right : Except Grpc.Status Acme.Auth.Principal) : Bool :=
  match left, right with
  | .ok l, .ok r => l.id.val == r.id.val && l.roles.val == r.roles.val
  | .error l, .error r => l == r
  | _, _ => false

private def checkExpected (fixture : Fixture)
    (result : Except Grpc.Status Acme.Auth.Principal) : IO Unit := do
  match fixture.expected, result with
  | .principal expectedId expectedRoles, .ok principal =>
      unless principal.id.val == expectedId && principal.roles.val == expectedRoles do
        throw (IO.userError s!"{fixture.label}: wrong authenticated principal")
  | .failure expectedMessage, .error status =>
      unless status.code == .unauthenticated && status.messageD == expectedMessage do
        throw (IO.userError s!"{fixture.label}: wrong status {repr status}")
  | .principal .., .error status =>
      throw (IO.userError s!"{fixture.label}: unexpectedly rejected: {repr status}")
  | .failure .., .ok principal =>
      throw (IO.userError
        s!"{fixture.label}: unexpectedly accepted principal {principal.id.val}")

private def makeTable : IO Acme.Auth.TokenTable := do
  let nulToken := "nul" ++ String.singleton (Char.ofNat 0) ++ "tail"
  let longToken := String.ofList (List.replicate 128 'z')
  match Acme.Auth.TokenTable.ofEntries #[
      { token := "x", id := 1, roles := #[] },
      { token := "acme-editor-7", id := 7, roles := #["editor"] },
      { token := "tøkén🚀", id := 8, roles := #["admin"] },
      { token := nulToken, id := 9, roles := #["editor", "auditor"] },
      { token := longToken, id := 10, roles := #["viewer"] }] with
  | .ok table => pure table
  | .error error => throw (IO.userError s!"fixture token table failed: {error}")

def main : IO Unit := do
  let table ← makeTable
  let nulToken := "nul" ++ String.singleton (Char.ofNat 0) ++ "tail"
  let nulMismatch := "nul" ++ String.singleton (Char.ofNat 0) ++ "tails"
  let longToken := String.ofList (List.replicate 128 'z')
  let noAuthorization := _root_.Http2.Headers.empty
    |>.insert "x-filler" "Bearer acme-editor-7"
  let fixtures : Array Fixture := #[
    { label := "missing", metadata := noAuthorization,
      expected := .failure "missing authorization bearer token" },
    { label := "one-byte boundary", metadata := authorizationValues #["Bearer x"],
      expected := .principal 1 #[] },
    { label := "ordinary valid", metadata := authorizationValues #["Bearer acme-editor-7"],
      expected := .principal 7 #["editor"] },
    { label := "unknown", metadata := authorizationValues #["Bearer bogus"],
      expected := .failure "unknown bearer token" },
    { label := "six-byte boundary", metadata := authorizationValues #["Bearer"],
      expected := .failure "missing authorization bearer token" },
    { label := "seven-byte boundary", metadata := authorizationValues #["Bearer "],
      expected := .failure "unknown bearer token" },
    { label := "wrong scheme", metadata := authorizationValues #["Basic acme-editor-7"],
      expected := .failure "missing authorization bearer token" },
    { label := "wrong scheme case", metadata := authorizationValues #["bearer acme-editor-7"],
      expected := .failure "missing authorization bearer token" },
    { label := "leading space", metadata := authorizationValues #[" Bearer acme-editor-7"],
      expected := .failure "missing authorization bearer token" },
    { label := "missing scheme space", metadata := authorizationValues #["Beareracme-editor-7"],
      expected := .failure "missing authorization bearer token" },
    { label := "double scheme space", metadata := authorizationValues #["Bearer  acme-editor-7"],
      expected := .failure "unknown bearer token" },
    { label := "trailing token space", metadata := authorizationValues #["Bearer acme-editor-7 "],
      expected := .failure "unknown bearer token" },
    { label := "unicode exact", metadata := authorizationValues #["Bearer tøkén🚀"],
      expected := .principal 8 #["admin"] },
    { label := "unicode byte mismatch", metadata := authorizationValues #["Bearer tøkén🚁"],
      expected := .failure "unknown bearer token" },
    { label := "embedded NUL exact", metadata := authorizationValues #["Bearer " ++ nulToken],
      expected := .principal 9 #["editor", "auditor"] },
    { label := "embedded NUL boundary mismatch",
      metadata := authorizationValues #["Bearer " ++ nulMismatch],
      expected := .failure "unknown bearer token" },
    { label := "long exact", metadata := authorizationValues #["Bearer " ++ longToken],
      expected := .principal 10 #["viewer"] },
    { label := "long extra byte", metadata := authorizationValues #["Bearer " ++ longToken ++ "z"],
      expected := .failure "unknown bearer token" },
    { label := "duplicate last valid",
      metadata := authorizationValues #["Bearer x", "Bearer acme-editor-7"],
      expected := .principal 7 #["editor"] },
    { label := "duplicate last malformed",
      metadata := authorizationValues #["Bearer acme-editor-7", "Basic x"],
      expected := .failure "missing authorization bearer token" },
    { label := "duplicate last unknown",
      metadata := authorizationValues #["Bearer acme-editor-7", "Bearer absent"],
      expected := .failure "unknown bearer token" },
    { label := "duplicate last unicode",
      metadata := authorizationValues #["Bearer x", "Bearer tøkén🚀"],
      expected := .principal 8 #["admin"] }]
  for fixture in fixtures do
    let reference := referenceAuthenticate table fixture.metadata
    let candidate := Acme.Auth.authenticate table fixture.metadata
    unless sameAuthentication reference candidate do
      throw (IO.userError s!"{fixture.label}: candidate differs from copied-suffix reference")
    checkExpected fixture candidate
  IO.println s!"all {fixtures.size} bearer suffix differential fixtures passed"
