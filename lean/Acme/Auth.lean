module

public import Grpc
public import AcmeLean.authz
public import AcmeValid.authz

public section

namespace Acme
namespace Auth

/-!
The authentication layer: resolves the `authorization` request header to an
`AuthenticatedPrincipal` *before any request body is read* (it runs inside
grpc-lean's request-header authorizer at END_HEADERS), and provides the
binding predicate `Bound` that ties the wire-level `acme.v1.Principal` of a
validated request to that authenticated identity.

The security claim, precisely:

* `AuthenticatedPrincipal` is unfabricable outside this module — its
  constructor is `private`, and the Lean module system makes a `private`
  constructor invisible to ordinary importers (only `import all Acme.Auth`,
  the white-box escape hatch used by in-repo proof/test targets, can see it).
  The only producers are `TokenTable.ofEntries`/`parse` + `lookup?` /
  `authenticate`, so *holding* an `AuthenticatedPrincipal` is evidence that a
  configured bearer token vouched for exactly this `(id, role_level)` pair.
* What remains trusted: the token table itself (server configuration) and
  the transport keeping tokens confidential (serve TLS in production).
-/

/-- An authenticated caller identity, minted only by this module (private
constructor; see the module docstring for the exact guarantee). Carries the
same range refinements as the wire `Principal` rules, so downstream policy
propositions can be stated directly against the authenticated identity. -/
structure AuthenticatedPrincipal where
  private mk ::
  id : UInt64
  roleLevel : UInt32
  id_pos : 0 < id
  role_ge : 1 ≤ roleLevel
  role_le : roleLevel ≤ 3

instance : ToString AuthenticatedPrincipal :=
  ⟨fun p => s!"principal {p.id} (role_level {p.roleLevel})"⟩

/-- One configured bearer credential: `token` authenticates as `(id, roleLevel)`. -/
structure TokenEntry where
  token : String
  id : UInt64
  roleLevel : UInt32
  deriving Repr

/-- Bearer-token table: the deliberately simple but honest authenticator.
Entries are validated (and their principals minted) at construction, so a
misconfigured table fails at startup, not per-request. -/
structure TokenTable where
  private mk ::
  private entries : Array (String × AuthenticatedPrincipal)

/-- Build a table, validating every entry's ranges up front. -/
def TokenTable.ofEntries (entries : Array TokenEntry) : Except String TokenTable := do
  let mut out : Array (String × AuthenticatedPrincipal) := #[]
  for e in entries do
    if e.token.isEmpty then
      throw "token table: empty token"
    if hid : 0 < e.id then
      if hge : 1 ≤ e.roleLevel then
        if hle : e.roleLevel ≤ 3 then
          out := out.push (e.token, ⟨e.id, e.roleLevel, hid, hge, hle⟩)
        else throw s!"token table: role_level {e.roleLevel} > 3 for token {e.token}"
      else throw s!"token table: role_level 0 for token {e.token}"
    else throw s!"token table: id 0 for token {e.token}"
  pure ⟨out⟩

/-- Parse a `token:id:role_level[,token:id:role_level...]` spec (the
`ACME_BEARER_TOKENS` environment format). Tokens may not contain `:` or `,`. -/
def TokenTable.parse (spec : String) : Except String TokenTable := do
  let mut entries : Array TokenEntry := #[]
  for part in spec.splitOn "," do
    match part.splitOn ":" with
    | [token, idStr, roleStr] =>
      match idStr.toNat?, roleStr.toNat? with
      | some id, some role =>
        if id < 2 ^ 64 && role < 2 ^ 32 then
          entries := entries.push
            { token, id := UInt64.ofNat id, roleLevel := UInt32.ofNat role }
        else throw s!"token table: numeric field out of range in {part}"
      | _, _ => throw s!"token table: malformed numeric field in {part}"
    | _ => throw s!"token table: expected token:id:role_level, got {part}"
  TokenTable.ofEntries entries

/-- Static demo credentials, mirroring the e2e principals
(`scripts/acme-e2e.sh`): two roles for user 7, an admin, and a second
legitimate editor used as the "stranger". -/
def demoEntries : Array TokenEntry := #[
  { token := "acme-editor-7", id := 7, roleLevel := 2 },
  { token := "acme-viewer-7", id := 7, roleLevel := 1 },
  { token := "acme-admin-99", id := 99, roleLevel := 3 },
  { token := "acme-editor-8", id := 8, roleLevel := 2 }]

def demoTable : TokenTable :=
  match TokenTable.ofEntries demoEntries with
  | .ok t => t
  | .error _ => ⟨#[]⟩  -- unreachable: demoEntries are in range

/-- Resolve a bearer token. Knowing a configured token *is* the credential. -/
def TokenTable.lookup? (table : TokenTable) (token : String) :
    Option AuthenticatedPrincipal :=
  table.entries.findSome? fun (t, p) => if t == token then some p else none

/-- Extract the token of an `authorization: Bearer <token>` header. -/
def bearerToken? (metadata : Grpc.Metadata) : Option String :=
  match (metadata.getAll "authorization").back? with
  | some v => if v.startsWith "Bearer " then some (v.drop 7).toString else none
  | none => none

/-- Authenticate a request's headers. Missing or unknown credentials are
UNAUTHENTICATED (gRPC: the caller could not be identified at all). -/
def authenticate (table : TokenTable) (metadata : Grpc.Metadata) :
    Except Grpc.Status AuthenticatedPrincipal :=
  match bearerToken? metadata with
  | none => .error (Grpc.Status.error .unauthenticated
      "missing authorization bearer token")
  | some token =>
    match table.lookup? token with
    | some p => .ok p
    | none => .error (Grpc.Status.error .unauthenticated "unknown bearer token")

/-- The binding predicate: the wire-level `principal` field of a request names
exactly the authenticated caller. Decidable, so handlers check it once and
carry the proof; every generated `authz.*` proposition about the wire
principal then transports to the authenticated identity. -/
abbrev Bound (p : AuthenticatedPrincipal) (wire : acme.v1.Valid.Principal) : Prop :=
  wire.toBase.id = p.id ∧ wire.toBase.role_level = p.roleLevel

end Auth
end Acme
