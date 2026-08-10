-- Canonical schema for the Acme Widgets service.
--
-- CHECK constraints mirror the PostgreSQL storage ranges expected by the
-- checked application adapters: id is positive, owner_id is nonnegative, and
-- quantity fits in a protobuf uint32.

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
