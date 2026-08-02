#!/usr/bin/env bash
# In-process TLS end-to-end: the Lean gRPC client calls our WidgetService over
# TLS 1.3 (grpc-lean's TLS terminator), backed by docker-compose postgres.
# Proves server-side TLS termination + graceful listener shutdown against a
# real Lean gRPC client (grpcurl/Go does not interoperate with grpc-lean's
# narrow ClientHello acceptance — see README).
set -euo pipefail

cd "$(dirname "$0")/.."

cleanup() { docker compose down -v >/dev/null 2>&1 || true; }
trap cleanup EXIT

bazel build //Integration:grpc_tls_test

# Ed25519 leaf for the gRPC listener. The raw 32-byte seed is the tail of the
# PKCS8 DER; the client trusts the leaf PEM directly as its anchor.
mkdir -p .certs
if [[ ! -f .certs/grpc.der ]]; then
  openssl req -x509 -newkey ed25519 -nodes -subj /CN=localhost -days 2 \
    -addext subjectAltName=DNS:localhost,IP:127.0.0.1 \
    -keyout .certs/grpc.key.pem -out .certs/grpc.crt.pem >/dev/null 2>&1
  openssl x509 -in .certs/grpc.crt.pem -outform DER -out .certs/grpc.der
  openssl pkey -in .certs/grpc.key.pem -outform DER | tail -c 32 > .certs/grpc.seed
fi

docker compose up -d postgres >/dev/null
for _ in $(seq 1 120); do
  docker compose exec postgres pg_isready -h 127.0.0.1 -U acme >/dev/null 2>&1 && break
  sleep 0.5
done
docker compose exec postgres pg_isready -h 127.0.0.1 -U acme >/dev/null

PG_URL="postgres://acme@localhost:54398/acme" \
  ACME_TLS_CERT="${PWD}/.certs/grpc.der" \
  ACME_TLS_KEY="${PWD}/.certs/grpc.seed" \
  ACME_TLS_PEM="${PWD}/.certs/grpc.crt.pem" \
  bazel-bin/Integration/grpc_tls_test
