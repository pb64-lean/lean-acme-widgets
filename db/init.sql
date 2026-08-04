-- Schema for the Acme Widgets service. The server's Repo.migrate also
-- creates the widgets table if missing, so a bind-mounted init is a
-- convenience, not a requirement.
--
-- CHECK constraints mirror the proto numeric ranges so the Lean checked
-- row decoders (Acme.Repo.uint64OfInt/uint32OfInt) can only fail if the
-- database was modified out-of-band: id/owner_id nonnegative (BIGINT is
-- already < 2^63, inside uint64), quantity within uint32.

CREATE TABLE IF NOT EXISTS users (
  id BIGSERIAL PRIMARY KEY CHECK (id > 0),
  username TEXT NOT NULL UNIQUE,
  email TEXT NOT NULL,
  role INT NOT NULL DEFAULT 1 CHECK (role BETWEEN 1 AND 3)
);

CREATE TABLE IF NOT EXISTS widgets (
  id BIGSERIAL PRIMARY KEY CHECK (id > 0),
  owner_id BIGINT NOT NULL CHECK (owner_id >= 0),
  name TEXT NOT NULL,
  sku TEXT NOT NULL,
  quantity BIGINT NOT NULL CHECK (quantity >= 0 AND quantity < 4294967296),
  description TEXT NOT NULL DEFAULT ''
);

INSERT INTO users (id, username, email, role) VALUES
  (7, 'bill_w', 'bill@acme.example', 2),
  (8, 'eve_x', 'eve@acme.example', 1),
  (99, 'root_a', 'root@acme.example', 3)
ON CONFLICT DO NOTHING;

SELECT setval('users_id_seq', 100);
