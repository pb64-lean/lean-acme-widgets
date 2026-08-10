# lean-acme-widgets

[![CI](https://github.com/pb64-lean/lean-acme-widgets/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/pb64-lean/lean-acme-widgets/actions/workflows/ci.yml) [![E2E](https://github.com/pb64-lean/lean-acme-widgets/actions/workflows/e2e.yml/badge.svg?branch=main)](https://github.com/pb64-lean/lean-acme-widgets/actions/workflows/e2e.yml) [![Assurance](https://github.com/pb64-lean/lean-acme-widgets/actions/workflows/assurance.yml/badge.svg?branch=main)](https://github.com/pb64-lean/lean-acme-widgets/actions/workflows/assurance.yml)

Example software system for the pure-Lean service ecosystem: the **Acme
Widgets** service, tying the sibling repositories together end to end —

- `rules_lean` — Bazel build rules for Lean 4
- `grpc-lean` (`rules_lean_grpc`) — proto/gRPC codegen, a pure-Lean gRPC
  runtime, and TLS 1.3 (client + server termination)
- `protovalidate-lean` — buf.validate CEL annotations compiled to Lean
  **refinement types**
- `lean-pgx` — DDL/query analysis, generated checked records and runners,
  runtime schema attachment, and relational contract metadata
- `pg-lean` — PostgreSQL wire/TLS transport beneath lean-pgx

The service enforces **authorization by construction**. Each RPC request is a
`(Principal, request)` product whose message-level CEL rules *are* the
authorization policy; the generated `AcmeValid.*` structure carries those
policies as dependent propositions, so a handler holding a validated request
holds a machine-checked proof that the policy was satisfied.

```lean
-- generated from authz.proto's CEL:
structure CheckedCreateWidgetRequest where
  principal : Valid.Principal
  request   : Valid.CreateWidgetRequest
  authz_create_self   : principal.toBase.id = request.toBase.user_id
  authz_create_editor : principal.toBase.role_level ≥ 2
```

**Scope of the guarantee — policy relative to an authenticated principal.**
Requests are authenticated *before any request body is read*: grpc-lean's
request-header authorizer resolves the `authorization: Bearer` token against
the server's token table at END_HEADERS, and a missing/unknown token is
rejected with `UNAUTHENTICATED` while the request body is still unread (the
demonstrable security win of the pre-body authorizer — malformed or oversized
bodies from unauthenticated peers never reach decoding). Successful
authentication mints an `Acme.Auth.AuthenticatedPrincipal` — a type that is
*unfabricable* outside `Auth.lean` (module-system `private` constructor;
holding one is evidence a configured token vouched for that identity) — and
the accept-capability the authorizer returns is a handler closing over it.

The wire `Principal` field is *bound* to the authenticated identity: after
validation, the handler's single
binding check (`Auth.Bound` — wire id and role_level equal the authenticated
principal's) turns every generated `authz.*` proposition into one about the
*authenticated* caller. A valid token presenting someone else's principal is
`PERMISSION_DENIED` (per gRPC conventions: the caller *is* identified, so not
`UNAUTHENTICATED`; what is denied is acting as somebody else). The evidence
then crosses the repository boundary as per-operation capabilities
(`Acme.Repo.AuthorizedCreate` carries `owner_eq : widget owner =
authenticated id` and `editor : role_level ≥ 2`; see
`authorizeCreate_sound`), then is projected into the generated query's typed
parameters.

The trusted boundary includes the token table itself (configuration:
`ACME_AUTH_TOKENS=token:id:role_level,...`, or a built-in demo table) and
transport confidentiality for tokens (serve TLS in production). The public
protocol includes the wire `Principal`; removing it and generating checked
products over only the server-side principal is outside the compatibility
contract because it changes the protobuf API.

## Layout

- `proto/` — `user.proto`, `widgets.proto`, `authz.proto`, `service.proto`
  with buf.validate annotations. Wired through `lean_proto_library`
  (`AcmeLean.*`) + `lean_protovalidate_library` (`AcmeValid.*`).
- `lean/Acme/` — `Auth.lean` (bearer-token authentication; unfabricable
  `AuthenticatedPrincipal`, `Bound` binding predicate), `Repo.lean`
  (capability-typed persistence through generated lean-pgx runners:
  `Authorized*` capabilities, `authorize*` smart constructors + soundness
  lemmas, and the checked PostgreSQL `Int64` ↔ protobuf unsigned adapter),
  `Service.lean`
  (WidgetService handlers: pre-body authentication, refinement-type
  validation, principal binding, typed `RuleKind` violation classification),
  `Model.lean` (pure in-memory service model over capability commands with
  policy-preservation lemmas), `Main.lean` (`//lean/Acme:acme_server`).
- `//Integration:grpc_tls_test` — in-process TLS end-to-end;
  `//Integration:lean_pgx_live_test{,_pg17}` — fresh PostgreSQL clusters,
  migration, attachment, and all five generated CRUD runners.
- `Test/` — `smoke_test` (ecosystem links), `acme_valid_test` (validation +
  authorization refinement types + authentication/binding/classification,
  hermetic), `//lean/Acme:acme_assurance` (compile-time audit: capability
  soundness + roundtrip theorems exist and are axiom-clean).
- `db/migrations/0001_schema.sql` — canonical DDL consumed by lean-pgx,
  Docker, and live tests; `db/queries/` — one literal SQL statement per
  generated runner; `db/fixtures/0001_seed.sql` — local/demo data only.
- `docker-compose.yml` — postgres:18 (plain + TLS variants), initialized from
  the canonical migration and demo fixture.

## Getting the source

All seven ecosystem repositories must be checked out side by side —
`MODULE.bazel` wires every sibling via Bzlmod `local_path_override`, and
because transitive overrides are ignored for non-root modules, this root
workspace re-declares all of them:

```sh
for r in rules_lean grpc-lean protovalidate-lean tls13-lean pg-lean lean-pgx lean-acme-widgets; do
  git clone "https://github.com/pb64-lean/$r"
done
cd lean-acme-widgets
bazel test //...
```

Prerequisites: Bazel 8.5 (see `.bazelversion`; bazelisk recommended) and Nix
— the Lean toolchain is nix-built from a pinned nixpkgs revision plus a Lean
4.31-pre overlay. The end-to-end scripts additionally need Docker Compose,
`grpcurl`, and `openssl`.

## Build & test

```
bazel test //...                 # includes transient PostgreSQL generation/live/compat tests
scripts/acme-e2e.sh              # compose postgres + server + grpcurl, 24 checks
scripts/acme-e2e.sh tls          # ... with the pg-lean → postgres link over TLS (verify-full)
scripts/acme-grpc-tls.sh         # in-process gRPC-over-TLS end-to-end
```

`scripts/acme-e2e.sh` drives the running server with `grpcurl` (every call
carries `-H "authorization: Bearer <token>"` against the demo token table),
covering: authentication negatives (missing token → `UNAUTHENTICATED` before
the body is processed; unknown token → `UNAUTHENTICATED`; valid token with a
mismatched wire principal → `PERMISSION_DENIED` binding rejection), the CRUD
happy paths, all runtime-reachable `authz.*` denial rules (by rule id →
`PERMISSION_DENIED`), a field-rule rejection (→ `INVALID_ARGUMENT`),
`NotFound`, cross-call persistence, and graceful listener shutdown. `tls`
serves postgres with hostssl-only pg_hba and connects `sslmode=verify-full`,
proving the database link is genuinely TLS (a plaintext client is refused).

`bazel test //...` does not use a developer database. The `//db:acme_db`
build action starts an action-private PostgreSQL 18 cluster, replays the real
DDL, asks PostgreSQL to analyze all five literal query files, and emits the
`AcmeDb` Lean API. `//db:acme_db_pg17_pg18_test` repeats analysis on both
supported majors, while `//Integration:lean_pgx_live_test` and its `_pg17`
variant start fresh clusters and exercise attachment plus
insert/get/list/update/delete at runtime. Production startup intentionally
does not run DDL: deployment must apply `db/migrations/0001_schema.sql` before
`AcmeDb.attach`; Docker Compose does this automatically.

## TLS

- **Service → postgres**: pg-lean connects with the standard `sslmode`/
  `sslrootcert` options; `scripts/acme-e2e.sh tls` exercises `verify-full`.
- **gRPC listener**: set `ACME_TLS_CERT` (DER leaf) + `ACME_TLS_KEY` (32-byte
  Ed25519 seed) and `acme_server` terminates TLS 1.3 (ALPN "h2") via
  grpc-lean's `serveTls`. `scripts/acme-grpc-tls.sh` verifies it in-process:
  the **Lean** gRPC client (`Client.connectTls`, trusting the leaf PEM) calls
  the WidgetService over TLS and gets an authenticated create, a pre-body
  `UNAUTHENTICATED` rejection (no token), a principal-binding denial, and two
  authz denials — exercising the whole stack under encryption.

  Mainstream TLS clients interoperate with this listener. The server
  *negotiates* a single suite (TLS_CHACHA20_POLY1305_SHA256 / X25519 /
  Ed25519), but it *selects* it from the client's offered overlap per
  RFC 8446 rather than requiring an exact match, so unknown suites, groups,
  extensions, and GREASE values are tolerated. grpc-lean's
  `//examples/lean_proto:note_grpcurl_tls_interop_test` drives the same
  `serveTls` path end to end with **grpcurl** over ALPN `h2` (unary,
  streaming, reflection-only invocation, and a 90 kB payload spanning many
  TLS records) and checks the TLS layer independently with
  `openssl s_client`. **Algorithm constraint:** a client offering none of
  those three algorithms gets a handshake failure rather than a fallback.

- **Listener termination**: `Main.lean` shuts the listener down gracefully on
  a stdin line or EOF (`Grpc.Server.shutdown` then `wait` to drain in-flight
  RPCs). Both e2e scripts assert the process exits 0 after a shutdown signal.

## Toolchain

Bazel builds with the shared Nix Lean 4.31-pre pinned at upstream commit
`24bef91f9a20a45f074729e869461d374687de1c`. Lake and Lean-aware editors use
`nightly-2026-04-25`, built from that same commit; `lakefile.lean` remains an
editor/LSP project model rather than the authoritative build. Install it with
`elan toolchain install leanprover/lean4-nightly:nightly-2026-04-25`. The
`lean4-nightly` selector spelling is intentional because Lean4IJ maps it
directly to Elan's on-disk nightly directory.
