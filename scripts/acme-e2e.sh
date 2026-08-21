#!/usr/bin/env bash
# End-to-end: docker-compose postgres + the Lean acme_server + grpcurl.
# Exercises the full stack — wire decode, refinement-type validation (field
# rules → INVALID_ARGUMENT, authz.* policies → PERMISSION_DENIED), and the
# lean-pgx checked repository over pg-lean — then tears everything down.
set -euo pipefail

cd "$(dirname "$0")/.."
MODE="${1:-plain}"          # plain | tls (postgres over TLS, verify-full)
PORT="${ACME_LISTEN_PORT:-50061}"
ADDR="localhost:${PORT}"
SERVER_PID=""
FAILS=0
PG_SERVICE="postgres"
COMPOSE=(docker compose)
CTL_FIFO=""

cleanup() {
  if [[ -n "$SERVER_PID" ]]; then kill "$SERVER_PID" >/dev/null 2>&1 || true; fi
  if [[ -n "$CTL_FIFO" ]]; then exec 9>&- 2>/dev/null || true; rm -f "$CTL_FIFO"; fi
  docker compose --profile tls down -v >/dev/null 2>&1 || true
}
trap cleanup EXIT

bazel build //lean/Acme:acme_server

if [[ "$MODE" == "tls" ]]; then
  # Throwaway root + localhost leaf; postgres accepts hostssl ONLY, and the
  # client connects with sslmode=verify-full against the generated root.
  mkdir -p .certs
  if [[ ! -f .certs/root.crt ]]; then
    openssl req -x509 -newkey rsa:2048 -nodes -sha256 \
      -subj /CN=acme-e2e-root -days 2 \
      -addext basicConstraints=critical,CA:TRUE,pathlen:0 \
      -addext keyUsage=critical,keyCertSign,cRLSign \
      -keyout .certs/root.key -out .certs/root.crt >/dev/null 2>&1
    openssl req -new -newkey rsa:2048 -nodes -sha256 -subj /CN=localhost \
      -keyout .certs/server.key -out .certs/server.csr >/dev/null 2>&1
    cat > .certs/server.ext <<'EXT'
[server_ext]
basicConstraints = critical,CA:FALSE
keyUsage = critical,digitalSignature,keyEncipherment
extendedKeyUsage = serverAuth
subjectAltName = DNS:localhost,IP:127.0.0.1
EXT
    openssl x509 -req -sha256 -in .certs/server.csr \
      -CA .certs/root.crt -CAkey .certs/root.key -CAcreateserial -days 2 \
      -extfile .certs/server.ext -extensions server_ext \
      -out .certs/server.crt >/dev/null 2>&1
  fi
  cat > .certs/pg_hba.conf <<'HBA'
local   all all           trust
hostssl all all 0.0.0.0/0 trust
hostssl all all ::0/0     trust
HBA
  PG_SERVICE="postgres-tls"
  COMPOSE=(docker compose --profile tls)
  export ACME_DATABASE_URL="postgres://acme@localhost:54397/acme?sslmode=verify-full&sslrootcert=${PWD}/.certs/root.crt"
fi

"${COMPOSE[@]}" up -d "$PG_SERVICE" >/dev/null
for _ in $(seq 1 120); do
  "${COMPOSE[@]}" exec "$PG_SERVICE" pg_isready -h 127.0.0.1 -U acme >/dev/null 2>&1 && break
  sleep 0.5
done
"${COMPOSE[@]}" exec "$PG_SERVICE" pg_isready -h 127.0.0.1 -U acme >/dev/null

CTL_FIFO="$(mktemp -u /tmp/acme-ctl.XXXXXX)"
mkfifo "$CTL_FIFO"
ACME_LISTEN_PORT="$PORT" bazel-bin/lean/Acme/acme_server < "$CTL_FIFO" &
SERVER_PID=$!
exec 9>"$CTL_FIFO"   # hold the write end open so the server's stdin stays live

for _ in $(seq 1 60); do
  grpcurl -plaintext "$ADDR" list >/dev/null 2>&1 && break
  sleep 0.5
done

# grpcurl needs message descriptors; the generated Lean code does not embed
# them, so compile from the proto sources (validate.proto from bazel's
# external protovalidate and protovalidate-lean checkouts).
VALIDATE_ROOT="$(bazel info output_base)/external/protovalidate+/proto/protovalidate"
AUTHZ_ROOT="$(bazel info output_base)/external/protovalidate_lean+/proto"
GRPCURL=(grpcurl -plaintext -import-path . -import-path "$VALIDATE_ROOT" \
  -import-path "$AUTHZ_ROOT" -proto proto/service.proto)

pass() { echo "PASS $1"; }
fail() { echo "FAIL $1"; echo "$2" | sed 's/^/  | /'; FAILS=$((FAILS + 1)); }

# call METHOD TOKEN BODY — TOKEN "" sends no authorization header.
call() {
  local method="$1" token="$2" body="$3"
  if [[ -n "$token" ]]; then
    "${GRPCURL[@]}" -H "authorization: Bearer ${token}" -d "$body" "$ADDR" \
      "acme.v1.WidgetService/$method" 2>&1
  else
    "${GRPCURL[@]}" -d "$body" "$ADDR" "acme.v1.WidgetService/$method" 2>&1
  fi
}

expect_contains() {
  local label="$1" out="$2" needle="$3"
  if grep -q "$needle" <<<"$out"; then pass "$label"; else fail "$label" "$out"; fi
}

# Bearer tokens resolve to server-side Principals with flat string roles; no
# principal or authorization envelope appears in an RPC request body.
T_EDITOR=acme-editor-7
T_VIEWER=acme-viewer-7
T_ADMIN=acme-admin-99
T_STRANGER=acme-editor-8
WIDGET='{"ownerId":"7","name":"Left-handed flange","sku":"wgt-1024","quantity":5}'
CREATE_BODY="{\"userId\":\"7\",\"widget\":${WIDGET}}"

# ── authentication: rejected at request headers, before the body ──────────
OUT=$(call CreateWidget "" "$CREATE_BODY") || true
expect_contains "auth.missing_token" "$OUT" "Unauthenticated"
expect_contains "auth.missing_token_detail" "$OUT" "missing authorization bearer token"
OUT=$(call CreateWidget "no-such-token" "$CREATE_BODY") || true
expect_contains "auth.unknown_token" "$OUT" "Unauthenticated"
expect_contains "auth.unknown_token_detail" "$OUT" "unknown bearer token"
# A valid principal for user 8 still cannot act for user 7. Identity comes
# exclusively from the bearer token, and the generated method policy denies it.
OUT=$(call CreateWidget "$T_STRANGER" "$CREATE_BODY") || true
expect_contains "auth.cross_principal" "$OUT" "PermissionDenied"
expect_contains "auth.cross_principal_rule" "$OUT" "authz.create.self"

# create (editor, self) — expect assigned id 1
OUT=$(call CreateWidget "$T_EDITOR" "$CREATE_BODY")
expect_contains "create.editor_self" "$OUT" '"id": "1"'

# create denied: viewer lacks editor/admin membership
OUT=$(call CreateWidget "$T_VIEWER" "$CREATE_BODY") || true
expect_contains "create.viewer_denied" "$OUT" "PermissionDenied"
expect_contains "create.viewer_rule_id" "$OUT" "authz.create.editor"

# create denied: on someone else's behalf (authenticated as 8, asking for 7)
OUT=$(call CreateWidget "$T_STRANGER" "$CREATE_BODY") || true
expect_contains "create.stranger_denied" "$OUT" "authz.create.self"

# create rejected: bad sku (field rule → InvalidArgument)
BAD=$(sed 's/wgt-1024/bogus/' <<<"$WIDGET")
OUT=$(call CreateWidget "$T_EDITOR" "{\"userId\":\"7\",\"widget\":${BAD}}") || true
expect_contains "create.bad_sku" "$OUT" "InvalidArgument"
expect_contains "create.bad_sku_rule" "$OUT" "string.pattern"

# get (any authenticated principal)
OUT=$(call GetWidget "$T_VIEWER" '{"widgetId":"1"}')
expect_contains "get.found" "$OUT" '"sku": "wgt-1024"'
OUT=$(call GetWidget "$T_VIEWER" '{"widgetId":"555"}') || true
expect_contains "get.not_found" "$OUT" "NotFound"

# list: self ok, admin ok, stranger denied
OUT=$(call ListWidgets "$T_VIEWER" '{"userId":"7","pageSize":10}')
expect_contains "list.self" "$OUT" '"name": "Left-handed flange"'
OUT=$(call ListWidgets "$T_ADMIN" '{"userId":"7","pageSize":10}')
expect_contains "list.admin" "$OUT" '"name": "Left-handed flange"'
OUT=$(call ListWidgets "$T_STRANGER" '{"userId":"7","pageSize":10}') || true
expect_contains "list.stranger_denied" "$OUT" "authz.list.self_or_admin"

# update: editor rewrites own widget
UPD='{"id":"1","ownerId":"7","name":"Right-handed flange","sku":"wgt-1024","quantity":6}'
OUT=$(call UpdateWidget "$T_EDITOR" "{\"userId\":\"7\",\"widget\":${UPD}}")
expect_contains "update.editor" "$OUT" "Right-handed flange"
OUT=$(call GetWidget "$T_VIEWER" '{"widgetId":"1"}')
expect_contains "update.persisted" "$OUT" "Right-handed flange"

# update denied without editor/admin membership
OUT=$(call UpdateWidget "$T_VIEWER" "{\"userId\":\"7\",\"widget\":${UPD}}") || true
expect_contains "update.viewer_denied" "$OUT" "authz.update.editor"

# delete: stranger denied, admin allowed
OUT=$(call DeleteWidget "$T_STRANGER" '{"userId":"7","widgetId":"1"}') || true
expect_contains "delete.stranger_denied" "$OUT" "authz.delete.self_or_admin"
OUT=$(call DeleteWidget "$T_ADMIN" '{"userId":"7","widgetId":"1"}')
expect_contains "delete.admin" "$OUT" '"deleted": true'
OUT=$(call GetWidget "$T_VIEWER" '{"widgetId":"1"}') || true
expect_contains "delete.gone" "$OUT" "NotFound"

if [[ "$MODE" == "tls" ]]; then
  # Prove the hostssl-only gate is real: a plaintext client must be refused.
  if PGSSLMODE=disable "${COMPOSE[@]}" exec postgres-tls \
      psql "postgres://acme@127.0.0.1:5432/acme?sslmode=disable" -c 'SELECT 1' >/dev/null 2>&1; then
    fail "tls.plaintext_refused" "plaintext connection unexpectedly accepted"
  else
    pass "tls.plaintext_refused"
  fi
fi

# Graceful listener termination: trigger shutdown over the control FIFO and
# assert the process drains and exits 0.
echo quit >&9
exec 9>&-
TERM_OK=1
for _ in $(seq 1 40); do
  if ! kill -0 "$SERVER_PID" >/dev/null 2>&1; then TERM_OK=0; break; fi
  sleep 0.25
done
if [[ "$TERM_OK" == "0" ]]; then
  if wait "$SERVER_PID"; then pass "listener.graceful_shutdown"
  else fail "listener.graceful_shutdown" "server exited non-zero"; fi
else
  fail "listener.graceful_shutdown" "server did not terminate after shutdown"
  kill "$SERVER_PID" >/dev/null 2>&1 || true
fi
SERVER_PID=""

if [[ "$FAILS" -eq 0 ]]; then
  echo "ALL PASS"
else
  echo "${FAILS} FAILURE(S)"
  exit 1
fi
