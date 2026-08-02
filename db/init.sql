-- Schema for the Acme Widgets service. The server's Repo.migrate also
-- creates the widgets table if missing, so a bind-mounted init is a
-- convenience, not a requirement.

CREATE TABLE IF NOT EXISTS users (
  id BIGSERIAL PRIMARY KEY,
  username TEXT NOT NULL UNIQUE,
  email TEXT NOT NULL,
  role INT NOT NULL DEFAULT 1
);

CREATE TABLE IF NOT EXISTS widgets (
  id BIGSERIAL PRIMARY KEY,
  owner_id BIGINT NOT NULL,
  name TEXT NOT NULL,
  sku TEXT NOT NULL,
  quantity INT NOT NULL,
  description TEXT NOT NULL DEFAULT ''
);

INSERT INTO users (id, username, email, role) VALUES
  (7, 'bill_w', 'bill@acme.example', 2),
  (8, 'eve_x', 'eve@acme.example', 1),
  (99, 'root_a', 'root@acme.example', 3)
ON CONFLICT DO NOTHING;

SELECT setval('users_id_seq', 100);
