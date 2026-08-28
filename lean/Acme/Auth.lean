module

public import Grpc
public import Pb64Authz.principal
public import Pb64AuthzValid.principal

public section

namespace Acme
namespace Auth

/-!
The authentication layer resolves the `authorization` request header to the
shared, validated `pb64.authz.v1.Principal` *before any request body is read*.
The principal comes exclusively from server configuration and is passed to
the generated protected-service registration through `RequestAuthenticator`;
it never appears in an Acme request message.

The security claim, precisely:

* `TokenTable.ofEntries`/`parse` validate every configured identity with the
  common generated Principal refinement. `lookup?` and `authenticate` can
  therefore only return positive IDs with unique, individually nonempty,
  bounded role strings (the role set itself may be empty).
* `Grpc.Authenticated` is minted only by grpc-lean after this authenticator
  succeeds; generated method-call constructors remain private. Holding a
  generated `*Call` is therefore the capability that combines authentication,
  request validity, and the method's CEL propositions.
* What remains trusted: the token table itself (server configuration) and
  the transport keeping tokens confidential (serve TLS in production).
-/

/-- The common proof-carrying Principal used by every generated protected
service. This alias adds no consumer-owned identity representation. -/
abbrev Principal := pb64.authz.v1.Valid.Principal

/-- One configured bearer credential. Roles are a flat, application-defined
set; role implication is expressed explicitly in method CEL. -/
structure TokenEntry where
  token : String
  id : UInt64
  roles : Array String
  deriving Repr

/-- Bearer-token table: the deliberately simple but honest authenticator.
Entries are validated (and their principals minted) at construction, so a
misconfigured table fails at startup, not per-request. -/
structure TokenTable where
  private mk ::
  private entries : Array (String × Principal)

/-- Build a table, validating every entry's ranges up front. -/
def TokenTable.ofEntries (entries : Array TokenEntry) : Except String TokenTable := do
  let mut out : Array (String × Principal) := #[]
  for e in entries do
    if e.token.isEmpty then
      throw "token table: empty token"
    match pb64.authz.v1.Valid.Principal.validate { id := e.id, roles := e.roles } with
    | .ok principal => out := out.push (e.token, principal)
    | .error violation =>
      throw s!"token table: invalid principal for token {e.token}: {violation}"
  pure ⟨out⟩

/-- Parse a `token:id:[role[+role...]][,token:id:[role[+role...]]]` spec (the
`ACME_BEARER_TOKENS` environment format). Tokens and roles may not contain
the delimiters `:`, `,`, and `+`. -/
def TokenTable.parse (spec : String) : Except String TokenTable := do
  let mut entries : Array TokenEntry := #[]
  for part in spec.splitOn "," do
    match part.splitOn ":" with
    | [token, idStr, rolesStr] =>
      match idStr.toNat? with
      | some id =>
        if id < 2 ^ 64 then
          entries := entries.push {
            token,
            id := UInt64.ofNat id,
            roles := if rolesStr.isEmpty then #[]
              else rolesStr.splitOn "+" |>.toArray
          }
        else throw s!"token table: numeric id out of range in {part}"
      | none => throw s!"token table: malformed numeric id in {part}"
    | _ => throw s!"token table: expected token:id:[role[+role...]], got {part}"
  TokenTable.ofEntries entries

/-- Static demo credentials, mirroring the e2e principals
(`scripts/acme-e2e.sh`): two differently-privileged credentials for user 7,
an admin, and a second legitimate editor used as the "stranger". -/
def demoEntries : Array TokenEntry := #[
  { token := "acme-editor-7", id := 7, roles := #["editor"] },
  { token := "acme-viewer-7", id := 7, roles := #["viewer"] },
  { token := "acme-admin-99", id := 99, roles := #["admin"] },
  { token := "acme-editor-8", id := 8, roles := #["editor"] }]

def demoTable : TokenTable :=
  match TokenTable.ofEntries demoEntries with
  | .ok t => t
  | .error _ => ⟨#[]⟩  -- unreachable: demoEntries are in range

/-- Resolve a bearer token. Knowing a configured token *is* the credential. -/
def TokenTable.lookup? (table : TokenTable) (token : String) :
    Option Principal :=
  table.entries.findSome? fun (t, p) => if t == token then some p else none

/-- Compare a configured token with the bytes after the ASCII `Bearer `
prefix without copying those bytes into a new `String`.  The lookup computes
the suffix byte length once and supplies the erased bound proof; each table
entry needs only a length check followed by the runtime string `memcmp`. -/
@[inline] private def configuredTokenMatchesHeader
    (configured header : String) (suffixBytes : Nat)
    (hsuffix : suffixBytes + 7 = header.utf8ByteSize) : Bool :=
  if hlength : configured.utf8ByteSize = suffixBytes then
    String.Slice.Pattern.Internal.memcmpStr configured header 0 ⟨7⟩
      configured.rawEndPos
      (by simp)
      (by
        simp only [String.Pos.Raw.le_iff, String.Pos.Raw.byteIdx_offsetBy,
          String.byteIdx_rawEndPos]
        omega)
  else
    false

private def TokenTable.lookupBearerHeader? (table : TokenTable)
    (header : String) : Option Principal :=
  if hsize : 7 ≤ header.utf8ByteSize then
    let suffixBytes := header.utf8ByteSize - 7
    have hsuffix : suffixBytes + 7 = header.utf8ByteSize := by omega
    table.entries.findSome? fun (configured, principal) =>
      if configuredTokenMatchesHeader configured header suffixBytes hsuffix then
        some principal
      else
        none
  else
    none

/-- Extract the token of an `authorization: Bearer <token>` header. -/
def bearerToken? (metadata : _root_.Http2.Headers) : Option String :=
  match metadata.getLast? "authorization" with
  | some v => if v.startsWith "Bearer " then some (v.drop 7).toString else none
  | none => none

/-- Select the same last bearer header as `bearerToken?`, but retain the
original header so the authentication lookup can compare its suffix in place. -/
private def bearerHeader? (metadata : _root_.Http2.Headers) : Option String :=
  match metadata.getLast? "authorization" with
  | some v => if v.startsWith "Bearer " then some v else none
  | none => none

/-- Authenticate a request's headers. Missing or unknown credentials are
UNAUTHENTICATED (gRPC: the caller could not be identified at all). -/
def authenticate (table : TokenTable) (metadata : _root_.Http2.Headers) :
    Except Grpc.Status Principal :=
  match bearerHeader? metadata with
  | none => .error (Grpc.Status.error .unauthenticated
      "missing authorization bearer token")
  | some header =>
    match table.lookupBearerHeader? header with
    | some p => .ok p
    | none => .error (Grpc.Status.error .unauthenticated "unknown bearer token")

/-- The pure pre-body authenticator consumed by generated protected-service
registration. grpc-lean wraps successful results in `Grpc.Authenticated`.
The immutable token-table snapshot and its authenticator are process-scoped,
so Lentil constructs and shares this adapter once. -/
def requestAuthenticator (table : TokenTable) :
    Grpc.RequestAuthenticator Principal :=
  .pure (authenticate table)

end Auth
end Acme
