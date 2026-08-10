SELECT id, owner_id, name, sku, quantity, description
FROM public.widgets
WHERE id = $1;
