SELECT id, owner_id, name, sku, quantity, description
FROM public.widgets
WHERE owner_id = $1
ORDER BY id
LIMIT $2;
