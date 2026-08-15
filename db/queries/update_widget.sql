UPDATE public.widgets
SET name = $3, sku = $4, quantity = $5, description = $6
WHERE id = $1 AND owner_id = $2;
