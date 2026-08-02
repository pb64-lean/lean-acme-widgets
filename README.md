# lean-acme-widgets

Example software system for the pure-Lean service ecosystem: the **Acme
Widgets** service, tying the sibling repositories together end to end —

- `rules_lean` — Bazel build rules for Lean 4
- `grpc-lean` (`rules_lean_grpc`) — proto/gRPC codegen, a pure-Lean gRPC
  runtime, and TLS 1.3 (client + server termination)
- `protovalidate-lean` — buf.validate CEL annotations compiled to Lean
  **refinement types**
- `pg-lean` — PostgreSQL client (with `tls13-lean` for TLS)

The headline idea: **authorization is a refinement type**. Each RPC request
is a `(Principal, request)` product whose message-level CEL rules *are* the
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

## Layout

- `proto/` — `user.proto`, `widgets.proto`, `authz.proto`, `service.proto`
  with buf.validate annotations. Wired through `lean_proto_library`
  (`AcmeLean.*`) + `lean_protovalidate_library` (`AcmeValid.*`).
- `lean/Acme/` — `Repo.lean` (widget persistence over pg-lean),
  `Service.lean` (WidgetService handlers: validate into the refinement type,
  then call the repository — authz holds by construction), `Main.lean`
  (`//lean/Acme:acme_server`).
- `Integration/grpc_tls_test` — in-process TLS end-to-end.
- `Test/` — `smoke_test` (ecosystem links), `acme_valid_test` (validation +
  authorization refinement types, hermetic).
- `db/init.sql`, `docker-compose.yml` — postgres:18 (plain + TLS variants).

This workspace is the root module; every sibling is wired via
`local_path_override` in `MODULE.bazel`.

## Build & test

```
bazel test //...                 # hermetic: smoke + validation/authz refinement types
scripts/acme-e2e.sh              # compose postgres + server + grpcurl, 18 checks
scripts/acme-e2e.sh tls          # ... with the pg-lean → postgres link over TLS (verify-full)
scripts/acme-grpc-tls.sh         # in-process gRPC-over-TLS end-to-end
```

`scripts/acme-e2e.sh` drives the running server with `grpcurl`, covering the
CRUD happy paths, all four `authz.*` denial rules (by rule id →
`PERMISSION_DENIED`), a field-rule rejection (→ `INVALID_ARGUMENT`),
`NotFound`, cross-call persistence, and graceful listener shutdown. `tls`
serves postgres with hostssl-only pg_hba and connects `sslmode=verify-full`,
proving the database link is genuinely TLS (a plaintext client is refused).

## TLS

- **Service → postgres**: pg-lean connects with the standard `sslmode`/
  `sslrootcert` options; `scripts/acme-e2e.sh tls` exercises `verify-full`.
- **gRPC listener**: set `ACME_TLS_CERT` (DER leaf) + `ACME_TLS_KEY` (32-byte
  Ed25519 seed) and `acme_server` terminates TLS 1.3 (ALPN "h2") via
  grpc-lean's `serveTls`. `scripts/acme-grpc-tls.sh` verifies it in-process:
  the **Lean** gRPC client (`Client.connectTls`, trusting the leaf PEM) calls
  the WidgetService over TLS and gets an authorized create plus two authz
  denials — exercising the whole stack under encryption.

  Note: grpc-lean's TLS server accepts a deliberately narrow ClientHello
  (X25519 + ChaCha20-Poly1305) and does not yet interoperate with mainstream
  TLS stacks such as Go's `crypto/tls` (grpcurl) or OpenSSL `s_client`. The
  in-process Lean client is therefore the interoperable — and more thorough —
  verification. Broadening server-side ClientHello support is upstream work
  in grpc-lean.

- **Listener termination**: `Main.lean` shuts the listener down gracefully on
  a stdin line or EOF (`Grpc.Server.shutdown` then `wait` to drain in-flight
  RPCs). Both e2e scripts assert the process exits 0 after a shutdown signal.

## Toolchain

Bazel builds with the shared pinned nix Lean (4.31-pre); `lakefile.lean` is
editor-LSP only.
