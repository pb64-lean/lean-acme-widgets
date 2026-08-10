-- Demo principals used by the local and end-to-end service fixtures.

INSERT INTO users (id, username, email, role) VALUES
  (7, 'bill_w', 'bill@acme.example', 2),
  (8, 'eve_x', 'eve@acme.example', 1),
  (99, 'root_a', 'root@acme.example', 3)
ON CONFLICT DO NOTHING;

SELECT setval('users_id_seq', 100);
