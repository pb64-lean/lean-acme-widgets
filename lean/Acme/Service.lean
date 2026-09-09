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

/-- Business handlers over generated authentication/authorization capabilities. -/
def widgetService (repo : Repo.Repo) : Valid.WidgetService := {
  handleCreateWidget := fun call => do
    let id ← repoM (repo.insertWidget call)
    pure { widget := some { call.request.widget.toBase with id } }
  handleGetWidget := fun call => do
    match ← repoM (repo.getWidget call) with
    | some widget => pure { widget := some widget }
    | none => throw (Grpc.Status.error .notFound "widget not found")
  handleListWidgets := fun call => do
    let widgets ← repoM (repo.listWidgets call)
    pure { widgets }
  handleUpdateWidget := fun call => do
    let updated ← repoM (repo.updateWidget call)
    if !updated then
      throw (Grpc.Status.error .notFound "widget not found for this owner")
    pure { widget := some call.request.widget.toBase }
  handleDeleteWidget := fun call => do
    let deleted ← repoM (repo.deleteWidget call)
    pure { deleted }
}

/-- Atomically register the protected service and then leave reflection
public. Keeping the structured duplicate-method result makes this reusable by
composition roots other than the Acme executable. -/
def register
    (authenticator : Grpc.RequestAuthenticator Auth.Principal)
    (service : Valid.WidgetService) : Except Grpc.DuplicateMethod Grpc.Registry := do
  let registry ← Valid.WidgetService.register Grpc.Registry.empty authenticator service
  pure (Grpc.Services.Reflection.register registry)

/-- Process-singleton registry recipe. Lentil supplies the shared authenticator
and handler table; a duplicate generated RPC path aborts startup rather than
exposing a partially populated registry. -/
def registry
    (authenticator : Grpc.RequestAuthenticator Auth.Principal)
    (service : Valid.WidgetService) : IO Grpc.Registry :=
  match register authenticator service with
  | .ok registry => pure registry
  | .error duplicate => throw (IO.userError
      s!"gRPC registry init: duplicate method {duplicate.name.path}")

/-- Composition roots adding managed standard services register reflection
after those services, so discovery sees the final service set. -/
def registryCore
    (authenticator : Grpc.RequestAuthenticator Auth.Principal)
    (service : Valid.WidgetService) : IO Grpc.Registry :=
  match Valid.WidgetService.register Grpc.Registry.empty authenticator service with
  | .ok registry => pure registry
  | .error duplicate => throw (IO.userError
      s!"gRPC registry init: duplicate method {duplicate.name.path}")

end Service
end Acme
