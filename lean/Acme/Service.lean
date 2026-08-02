module

public import Grpc
public import AcmeLean.widgets
public import AcmeLean.authz
public import AcmeLean.service
public import AcmeValid.widgets
public import AcmeValid.authz
public import Acme.Repo

public section

namespace Acme
namespace Service

open acme.v1

/-!
WidgetService: every handler first validates its wire request into the
`AcmeValid` refinement type. Past that point the authorization policy holds
as propositions carried by the value — the repository is only ever called
with proven-authorized data. Field-rule failures map to INVALID_ARGUMENT,
`authz.*` policy failures to PERMISSION_DENIED.
-/

def statusOfViolation (v : Protovalidate.Violation) : Grpc.Status :=
  if v.ruleId.startsWith "authz." then
    Grpc.Status.error .permissionDenied (toString v)
  else
    Grpc.Status.invalidArgument (toString v)

/-- Validate into the refinement type or fail the RPC. -/
def checked (validate : β → Except Protovalidate.Violation α) (req : β) : Grpc.GrpcM α :=
  match validate req with
  | .ok v => pure v
  | .error violation => throw (statusOfViolation violation)

/-- Surface repository/postgres failures as INTERNAL. -/
def repoM (action : IO (Except Pg.Error α)) : Grpc.GrpcM α := do
  match ← liftM action with
  | .ok v => pure v
  | .error e => throw (Grpc.Status.internal (toString e))

def create (repo : Repo.Repo) : Grpc.TypedUnaryHandler CheckedCreateWidgetRequest WidgetResponse :=
  fun req => do
    let v ← checked Valid.CheckedCreateWidgetRequest.validate req
    -- v.authz_create_self : principal.id = request.user_id
    -- v.request.create_owner_matches : the widget belongs to that user
    let widget := v.request.widget.toBase
    let id ← repoM (repo.insertWidget widget)
    pure { widget := some { widget with id } }

def get (repo : Repo.Repo) : Grpc.TypedUnaryHandler CheckedGetWidgetRequest WidgetResponse :=
  fun req => do
    let v ← checked Valid.CheckedGetWidgetRequest.validate req
    match ← repoM (repo.getWidget v.request.widget_id.val) with
    | some widget => pure { widget := some widget }
    | none => throw (Grpc.Status.error .notFound "widget not found")

def list (repo : Repo.Repo) : Grpc.TypedUnaryHandler CheckedListWidgetsRequest ListWidgetsResponse :=
  fun req => do
    let v ← checked Valid.CheckedListWidgetsRequest.validate req
    -- v.authz_list_self_or_admin: the listed owner is the principal, or the
    -- principal is admin.
    let widgets ← repoM (repo.listWidgets v.request.user_id.val v.request.page_size.val)
    pure { widgets }

def update (repo : Repo.Repo) : Grpc.TypedUnaryHandler CheckedUpdateWidgetRequest WidgetResponse :=
  fun req => do
    let v ← checked Valid.CheckedUpdateWidgetRequest.validate req
    let widget := v.request.widget.toBase
    let updated ← repoM (repo.updateWidget widget)
    if !updated then
      throw (Grpc.Status.error .notFound "widget not found for this owner")
    pure { widget := some widget }

def delete (repo : Repo.Repo) : Grpc.TypedUnaryHandler CheckedDeleteWidgetRequest DeleteWidgetResponse :=
  fun req => do
    let v ← checked Valid.CheckedDeleteWidgetRequest.validate req
    -- v.authz_delete_self_or_admin: request.user_id names the owner, and the
    -- principal is that owner or an admin.
    let deleted ← repoM (repo.deleteWidget v.request.widget_id.val v.request.user_id.val)
    pure { deleted }

def widgetService (repo : Repo.Repo) : WidgetService := {
  handleCreateWidget := create repo
  handleGetWidget := get repo
  handleListWidgets := list repo
  handleUpdateWidget := update repo
  handleDeleteWidget := delete repo
}

def registry (repo : Repo.Repo) : Grpc.Registry :=
  Grpc.Services.Reflection.register
    (WidgetService.register Grpc.Registry.empty (widgetService repo))

end Service
end Acme
