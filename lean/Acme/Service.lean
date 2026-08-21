module

public import Grpc
public import AcmeLean.widgets
public import AcmeLean.service
public import AcmeValid.widgets
public import AcmeValid.service
public import Acme.Auth
public import Acme.Repo

public section

namespace Acme
namespace Service

open acme.v1

/-!
WidgetService with generated, method-level authorization:

1. `Valid.WidgetService.register` resolves `authorization` metadata through
   `Auth.requestAuthenticator` at END_HEADERS, before accepting request DATA.
2. Generated registration validates the ordinary request message, evaluates
   each method's CEL policy against the server-side Principal and request, and
   privately constructs the proof-carrying `WidgetService.*Call` capability.
3. Handwritten handlers and the repository consume that generated capability
   directly. There is no wire Principal, binding predicate, rule-ID status
   table, per-principal service, or duplicate `Authorized*` wrapper.

The generated boundary maps authentication failures to UNAUTHENTICATED,
request validation failures to INVALID_ARGUMENT, and method-policy failures to
PERMISSION_DENIED.
-/

/-- Surface repository/database-contract failures as INTERNAL. -/
def repoM (action : IO (Except Repo.Error α)) : Grpc.GrpcM α := do
  match ← liftM action with
  | .ok value => pure value
  | .error error => throw (Grpc.Status.internal (toString error))

def create (repo : Repo.Repo) :
    Grpc.TypedUnaryHandler Valid.WidgetService.CreateWidgetCall WidgetResponse :=
  fun call => do
    let id ← repoM (repo.insertWidget call)
    pure { widget := some { call.request.widget.toBase with id } }

def get (repo : Repo.Repo) :
    Grpc.TypedUnaryHandler Valid.WidgetService.GetWidgetCall WidgetResponse :=
  fun call => do
    match ← repoM (repo.getWidget call) with
    | some widget => pure { widget := some widget }
    | none => throw (Grpc.Status.error .notFound "widget not found")

def list (repo : Repo.Repo) :
    Grpc.TypedUnaryHandler Valid.WidgetService.ListWidgetsCall ListWidgetsResponse :=
  fun call => do
    let widgets ← repoM (repo.listWidgets call)
    pure { widgets }

def update (repo : Repo.Repo) :
    Grpc.TypedUnaryHandler Valid.WidgetService.UpdateWidgetCall WidgetResponse :=
  fun call => do
    let updated ← repoM (repo.updateWidget call)
    if !updated then
      throw (Grpc.Status.error .notFound "widget not found for this owner")
    pure { widget := some call.request.widget.toBase }

def delete (repo : Repo.Repo) :
    Grpc.TypedUnaryHandler Valid.WidgetService.DeleteWidgetCall DeleteWidgetResponse :=
  fun call => do
    let deleted ← repoM (repo.deleteWidget call)
    pure { deleted }

/-- Business handlers over generated authentication/authorization capabilities. -/
def widgetService (repo : Repo.Repo) : Valid.WidgetService := {
  handleCreateWidget := create repo
  handleGetWidget := get repo
  handleListWidgets := list repo
  handleUpdateWidget := update repo
  handleDeleteWidget := delete repo
}

/-- Atomically register the protected service and then leave reflection
public. A duplicate generated RPC path is a startup error; callers must handle
it explicitly rather than receiving a partially populated registry. -/
def registry (repo : Repo.Repo) (table : Auth.TokenTable) :
    Except Grpc.DuplicateMethod Grpc.Registry := do
  let registry ← Valid.WidgetService.register Grpc.Registry.empty
    (Auth.requestAuthenticator table) (widgetService repo)
  pure (Grpc.Services.Reflection.register registry)

end Service
end Acme
