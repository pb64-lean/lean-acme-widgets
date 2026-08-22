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
- `lentil` — compile-time dependency injection and environment-backed
  configuration (consumed remotely from a pinned commit, not a sibling
  checkout)

The service enforces **authorization by construction** without putting
authorization envelopes on the wire. RPCs use their ordinary request messages;
method-level CEL annotations describe policies over a synthetic
`{ principal, request }` value. The principal is resolved from request headers
by the server, and protovalidate-lean generates a proof-carrying call type whose
private constructor is used only after authentication, request validation, and
authorization have succeeded.

```lean
-- generated from service.proto's method annotation:
structure WidgetService.CreateWidgetPolicy
    (principal : pb64.authz.v1.Valid.Principal)
    (request : Valid.CreateWidgetRequest) : Prop where
  authz_create_self : principal.toBase.id = request.toBase.user_id
  authz_create_editor :
    "editor" ∈ principal.toBase.roles ∨ "admin" ∈ principal.toBase.roles

structure WidgetService.CreateWidgetCall where
  private mk ::
  principal : pb64.authz.v1.Valid.Principal
  request   : Valid.CreateWidgetRequest
  policy    : WidgetService.CreateWidgetPolicy principal request
```

Requests are authenticated *before any request body is read*: grpc-lean's
method-local request authenticator resolves the `authorization: Bearer` token
against the server's token table at END_HEADERS, and a missing/unknown token is
rejected with `UNAUTHENTICATED` while the request body is still unread (the
demonstrable security win of pre-body authentication — malformed or oversized
bodies from unauthenticated peers never reach decoding). Successful
authentication supplies the common validated `pb64.authz.v1.Principal` through
grpc-lean's private-constructor `Authenticated` wrapper. Request field failures
map to `INVALID_ARGUMENT`; method-policy failures map directly to
`PERMISSION_DENIED`, without consumer-maintained rule-ID classification.

The generated `*Call` is the repository capability: it contains the validated
request, the exact server-authenticated principal, and each policy proposition.
There is no wire principal to spoof, no binding predicate, no second local
Principal representation, and no per-principal service registry.

The trusted boundary includes the token table itself (configuration:
`ACME_BEARER_TOKENS=token:id:[role[+role...]],...`, or a built-in demo table) and
transport confidentiality for tokens (serve TLS in production). Roles are a
flat set: policies explicitly say `editor || admin`; common code never assigns
an ordinal rank or silently expands role implications.

## Layout

- `proto/` — `user.proto`, `widgets.proto`, and `service.proto`, with ordinary
  RPC inputs, buf.validate field/message rules, and `pb64.authz.v1.method`
  authorization options. Wired through `lean_proto_library` (`AcmeLean.*`) +
  `lean_protovalidate_grpc_library` (`AcmeValid.*`). The common Principal and
  annotation schema live with protovalidate-lean.
- `lean/Acme/` — `Auth.lean` (bearer tokens to the common validated Principal),
  `Repo.lean` (generated `*Call` capabilities through generated lean-pgx
  runners and the checked PostgreSQL `Int64` ↔ protobuf unsigned adapter),
  `Service.lean` (generated authenticated registration plus business handlers),
  `Model.lean` (pure in-memory service model over capability commands with
  policy-preservation lemmas), `Main.lean` (`//lean/Acme:acme_server`).
- `//Integration:grpc_tls_test` — in-process TLS end-to-end;
  `//Integration:lean_pgx_live_test{,_pg17}` — fresh PostgreSQL clusters,
  migration, attachment, and all five generated CRUD runners.
- `Test/` — `smoke_test` (ecosystem links), `acme_valid_test` (validation +
  generated method authorization and common-principal authentication,
  hermetic), `//lean/Acme:acme_assurance` (compile-time audit: capability
  soundness + roundtrip theorems exist and are axiom-clean).
- `db/migrations/0001_schema.sql` — canonical DDL consumed by lean-pgx,
  Docker, and live tests; `db/queries/` — one literal SQL statement per
  generated runner; `db/fixtures/0001_seed.sql` — local/demo data only.
- `docker-compose.yml` — postgres:18 (plain + TLS variants), initialized from
  the canonical migration and demo fixture.

## Getting the source

The seven co-developed ecosystem repositories must be checked out side by
side — `MODULE.bazel` wires every sibling via Bzlmod `local_path_override`,
and because transitive overrides are ignored for non-root modules, this root
workspace re-declares all of them. `lentil` is the exception: Bazel fetches
it remotely via `archive_override` from a pinned GitHub commit, so a sibling
checkout is only needed for the Lake/editor project model (`lakefile.lean`
requires `../lentil`):

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
bazel run //scripts:acme_load    # 8-second persistent-channel mixed CRUD load test
scripts/acme-e2e.sh              # compose postgres + server + grpcurl, 24 checks
scripts/acme-e2e.sh tls          # ... with the pg-lean → postgres link over TLS (verify-full)
scripts/acme-grpc-tls.sh         # in-process gRPC-over-TLS end-to-end
```

`acme_server` composes its process with
[lentil](https://github.com/pb64-lean/lentil): `@[lentil_config "ACME_"]`
derives one `AcmeConfig` from the `ACME_` environment prefix, `@[lentil]`
recipes autowire the postgres connection, repository, bearer-token table,
request authenticator, proof-carrying WidgetService, gRPC registry, and
terminal server instance, and `make_context AcmeContext` checks that dependency
graph during elaboration and generates the startup code:

| Variable | Type/default | Purpose |
| --- | --- | --- |
| `ACME_DATABASE_URL` | string; `postgres://acme@localhost:54398/acme` | PostgreSQL connection URI |
| `ACME_LISTEN_PORT` | checked `UInt16`; `50061` | gRPC listener port |
| `ACME_RESPONSE_COMPRESSION` | boolean; `false` | Enable negotiated gzip responses; request gzip remains supported |
| `ACME_BEARER_TOKENS` | optional `token:id:[role[+role...]],...` | Authentication table; absent uses the demo table; an empty final field means no roles |
| `ACME_TLS_CERTIFICATE` | optional file path | DER leaf certificate |
| `ACME_TLS_SIGNING_KEY` | optional file path | 32-byte Ed25519 signing key |

The TLS certificate and signing key must either both be set or both be absent.

`//scripts:acme_load` is a hermetic Python binary with protobuf messages and
the WidgetService client stub generated by Bazel. By default it starts an
isolated Compose PostgreSQL project plus the Bazel-built server, seeds a hot
working set, warms the persistent connection for two excluded seconds, and
then drives a weighted create/get/list/update/delete mix for eight measured
seconds with 48 asynchronous workers sharing one persistent HTTP/2 channel.
It reports attempted and successful IOPS/counts, per-operation counts,
mean/p95/p99/max RPC latency, failures, and client process CPU, then tears down
only the stack it created. Client CPU utilization uses process CPU time, so
100% corresponds to one fully occupied logical core and native gRPC worker
threads can make the value exceed 100%.

Use `--no-manage-stack` against an already-running server; `--warmup`,
`--duration`, `--concurrency`, `--random-seed`, and `--rpc-timeout` make
benchmark conditions explicit. `--json-output result.json` writes the full
configuration, machine/source metadata, topology, excluded warmup, and measured
results in a versioned machine-readable format. `--channels 1,2,4,8` runs an
ordered topology sweep without restarting the managed server. Workers are
assigned stably by worker id modulo channel count, and every multi-channel
transport uses its own gRPC local subchannel pool so Python cannot collapse the
channels onto a shared HTTP/2 connection. The one-channel path retains gRPC's
original shared-channel defaults. The throughput default uses no per-RPC
deadline; pass (for example) `--rpc-timeout 3` when testing deadline behavior
rather than maximum throughput.

`scripts/acme-e2e.sh` drives the running server with `grpcurl` (every call
carries `-H "authorization: Bearer <token>"` against the demo token table),
covering: authentication negatives (missing token → `UNAUTHENTICATED` before
the body is processed; unknown token → `UNAUTHENTICATED`; principal 8 asking
to act for user 7 → generated-policy `PERMISSION_DENIED`), the CRUD
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
- **gRPC listener**: set `ACME_TLS_CERTIFICATE` (DER leaf) +
  `ACME_TLS_SIGNING_KEY` (32-byte Ed25519 seed) and `acme_server` terminates
  TLS 1.3 (ALPN "h2") via
  grpc-lean's `serveTls`. `scripts/acme-grpc-tls.sh` verifies it in-process:
  the **Lean** gRPC client (`Client.connectTls`, trusting the leaf PEM) calls
  the WidgetService over TLS and gets an authenticated create, a pre-body
  `UNAUTHENTICATED` rejection (no token) and role/cross-principal authz denials
  — exercising the whole stack under encryption.

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

For Lean4IJ, refresh the Bazel-generated Lean sources before starting or
restarting the language server:

```sh
set -o pipefail
bazel cquery 'kind(rule, //...)' \
  --output=starlark \
  --starlark:expr='str(target.label) if [key for key in providers(target) if key.endswith("//lean:providers.bzl%LeanGeneratedSourceInfo")] else ""' |
  sed '/^$/d' |
  sort -u |
  xargs -r bazel build --output_groups=lean_srcs
```

The Lake project recompiles `AcmeDb`, `AcmeLean`, and `AcmeValid` from those
generated sources into `.lake/build/lib/lean`, alongside the sibling Lake
dependencies. Re-run the target whenever the database schema, SQL queries,
protos, or validation rules change, then restart the Lean language server.
