module

public import Grpc
public import AcmeLean.widgets
public import AcmeLean.authz
public import AcmeLean.service
public import AcmeValid.widgets
public import AcmeValid.authz
public import Acme.Auth
public import Acme.Repo

public section

namespace Acme
namespace Service

open acme.v1

/-!
WidgetService, authenticated and capability-typed:

1. grpc-lean's request-header authorizer resolves the `authorization` bearer
   token to an `Auth.AuthenticatedPrincipal` at END_HEADERS — unauthenticated
   requests are rejected *before any request body is accepted* — and the
   accept-capability it returns is a handler closing over that principal.
2. The handler validates the wire request into the `AcmeValid` refinement
   type (policy propositions), then `Repo.authorize*` performs the single
   binding check (`Auth.Bound`): the wire `principal` field must name exactly
   the authenticated caller. A mismatch is PERMISSION_DENIED — the caller is
   identified (valid token, so not UNAUTHENTICATED per gRPC conventions) but
   may not act as the principal named in the request.
3. Past that point the repository is called only with `Authorized*`
   capabilities: validated request + authenticated principal + policy
   propositions, projected only into generated checked query parameters.

Field-rule violations map to INVALID_ARGUMENT and `authz.*` policy
violations to PERMISSION_DENIED via the total `ruleKind` classification.
-/

-- ── typed violation classification ────────────────────────────────────────

/-- How a protovalidate rule violation maps to a gRPC status. -/
inductive RuleKind where
  /-- Authorization policy violated by an identified caller → PERMISSION_DENIED. -/
  | authz
  /-- Malformed request contents → INVALID_ARGUMENT. -/
  | field
  deriving DecidableEq, Repr, BEq

/-- Every `authz.*` CEL rule id declared in `proto/authz.proto`, verbatim.
Keep in sync with the proto; `ruleKind_matches_authzRuleIds` below checks the
mapping covers exactly this list. (Eventually protovalidate-lean's generator
should emit this metadata — RuleKind per rule — directly.) -/
def authzRuleIds : List String := [
  "authz.create.self",
  "authz.create.editor",
  "authz.list.self_or_admin",
  "authz.update.self",
  "authz.update.editor",
  "authz.update.widget_owner",
  "authz.delete.self_or_admin"]

/-- Total, explicit classification of this service's rule ids: the `authz`
arms are exactly `authzRuleIds`; everything else (field rules, `required`,
message-level request rules like `create.owner_matches`) is a field rule. -/
def ruleKind : String → RuleKind
  | "authz.create.self"
  | "authz.create.editor"
  | "authz.list.self_or_admin"
  | "authz.update.self"
  | "authz.update.editor"
  | "authz.update.widget_owner"
  | "authz.delete.self_or_admin" => .authz
  | _ => .field

-- Completeness check: every declared authz rule id classifies as `.authz`
-- (elaboration-time; a drifted list fails the build). The converse — that
-- the match has no `.authz` arm outside the list — is syntactic: the arms
-- above are the list, verbatim.
#guard authzRuleIds.all (fun id => ruleKind id == .authz)
#guard authzRuleIds.length == 7
#guard ruleKind "create.owner_matches" == .field
#guard ruleKind "required" == .field

def statusOfViolation (v : Protovalidate.Violation) : Grpc.Status :=
  match ruleKind v.ruleId with
  | .authz => Grpc.Status.error .permissionDenied (toString v)
  | .field => Grpc.Status.invalidArgument (toString v)

-- ── handler plumbing ──────────────────────────────────────────────────────

/-- Validate into the refinement type or fail the RPC. -/
def checked (validate : β → Except Protovalidate.Violation α) (req : β) : Grpc.GrpcM α :=
  match validate req with
  | .ok v => pure v
  | .error violation => throw (statusOfViolation violation)

/-- Wire principal ≠ authenticated principal. PERMISSION_DENIED, not
UNAUTHENTICATED: the bearer token identified the caller; what is denied is
acting as somebody else. -/
def principalMismatch : Grpc.Status :=
  Grpc.Status.error .permissionDenied
    "wire principal does not match the authenticated caller"

/-- Run an `authorize*` binding check or fail the RPC. -/
def bound (authorize : Option α) : Grpc.GrpcM α :=
  match authorize with
  | some cap => pure cap
  | none => throw principalMismatch

/-- Surface repository/database-contract failures as INTERNAL. -/
def repoM (action : IO (Except Repo.Error α)) : Grpc.GrpcM α := do
  match ← liftM action with
  | .ok v => pure v
  | .error e => throw (Grpc.Status.internal (toString e))

-- ── per-principal handlers (inside the accept-capability) ─────────────────

def create (repo : Repo.Repo) (p : Auth.AuthenticatedPrincipal) :
    Grpc.TypedUnaryHandler CheckedCreateWidgetRequest WidgetResponse :=
  fun req => do
    let v ← checked Valid.CheckedCreateWidgetRequest.validate req
    let cap ← bound (Repo.authorizeCreate p v)
    -- cap.owner_eq : the widget belongs to the *authenticated* p
    -- cap.editor   : p.roleLevel ≥ 2
    let id ← repoM (repo.insertWidget cap)
    pure { widget := some { cap.request.widget.toBase with id } }

def get (repo : Repo.Repo) (p : Auth.AuthenticatedPrincipal) :
    Grpc.TypedUnaryHandler CheckedGetWidgetRequest WidgetResponse :=
  fun req => do
    let v ← checked Valid.CheckedGetWidgetRequest.validate req
    let cap ← bound (Repo.authorizeGet p v)
    match ← repoM (repo.getWidget cap) with
    | some widget => pure { widget := some widget }
    | none => throw (Grpc.Status.error .notFound "widget not found")

def list (repo : Repo.Repo) (p : Auth.AuthenticatedPrincipal) :
    Grpc.TypedUnaryHandler CheckedListWidgetsRequest ListWidgetsResponse :=
  fun req => do
    let v ← checked Valid.CheckedListWidgetsRequest.validate req
    let cap ← bound (Repo.authorizeList p v)
    -- cap.self_or_admin : the listed owner is p, or p is admin
    let widgets ← repoM (repo.listWidgets cap)
    pure { widgets }

def update (repo : Repo.Repo) (p : Auth.AuthenticatedPrincipal) :
    Grpc.TypedUnaryHandler CheckedUpdateWidgetRequest WidgetResponse :=
  fun req => do
    let v ← checked Valid.CheckedUpdateWidgetRequest.validate req
    let cap ← bound (Repo.authorizeUpdate p v)
    let updated ← repoM (repo.updateWidget cap)
    if !updated then
      throw (Grpc.Status.error .notFound "widget not found for this owner")
    pure { widget := some cap.request.widget.toBase }

def delete (repo : Repo.Repo) (p : Auth.AuthenticatedPrincipal) :
    Grpc.TypedUnaryHandler CheckedDeleteWidgetRequest DeleteWidgetResponse :=
  fun req => do
    let v ← checked Valid.CheckedDeleteWidgetRequest.validate req
    let cap ← bound (Repo.authorizeDelete p v)
    -- cap.self_or_admin : the named owner is p, or p is admin
    let deleted ← repoM (repo.deleteWidget cap)
    pure { deleted }

/-- The service as seen by one authenticated caller. Only the accept
capability returned by the request-header authorizer ever holds one. -/
def widgetService (repo : Repo.Repo) (p : Auth.AuthenticatedPrincipal) : WidgetService := {
  handleCreateWidget := create repo p
  handleGetWidget := get repo p
  handleListWidgets := list repo p
  handleUpdateWidget := update repo p
  handleDeleteWidget := delete repo p
}

-- ── registry: authenticate at END_HEADERS, before any body ────────────────

def widgetServiceName : String := WidgetService.CreateWidgetMethod.service

/-- Defense in depth: registered fallback handlers that must never run —
dispatch always goes through the authorizer's accept capability. -/
def unauthenticatedService : WidgetService :=
  let deny {α β : Type} : Grpc.TypedUnaryHandler α β := fun _ =>
    throw (Grpc.Status.error .unauthenticated
      "request reached a WidgetService handler without authentication")
  { handleCreateWidget := deny, handleGetWidget := deny, handleListWidgets := deny,
    handleUpdateWidget := deny, handleDeleteWidget := deny }

/--
The pre-body authenticator. Runs at END_HEADERS, before any request DATA is
accepted: WidgetService methods resolve the bearer token to an
`AuthenticatedPrincipal` and return the accept-capability whose handler
closes over it (shape-safely, via `MethodEntry.handlerFor?`); missing or
unknown tokens are rejected with UNAUTHENTICATED while the request body is
still unread. Non-WidgetService methods (server reflection, needed by
`grpcurl` for discovery) stay open with their registered handlers.
-/
def authorizer (repo : Repo.Repo) (table : Auth.TokenTable) :
    Grpc.RequestHeaderAuthorizer :=
  let dispatches := table.bind fun principal =>
    WidgetService.register Grpc.Registry.empty (widgetService repo principal)
  fun entry metadata => do
    if entry.name.service != widgetServiceName then
      pure (.acceptRegistered entry)
    else
      match dispatches.authenticate metadata with
      | .error status => throw status
      | .ok dispatch =>
        match dispatch.findEntry? entry.name with
        | none => throw (Grpc.Status.internal "method missing from authenticated registry")
        | some entry' =>
          match entry'.handlerFor? entry.shape with
          | some handler => pure (.accept handler)
          | none => throw (Grpc.Status.internal "authorizer shape mismatch")

def registry (repo : Repo.Repo) (table : Auth.TokenTable) : Grpc.Registry :=
  Grpc.Services.Reflection.register
    (WidgetService.register Grpc.Registry.empty unauthenticatedService)
    |>.withRequestHeaderAuthorizer (authorizer repo table)

end Service
end Acme
