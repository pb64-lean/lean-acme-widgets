INSERT INTO public.widgets (owner_id, name, sku, quantity, description)
VALUES ($1, $2, $3, $4, $5)
RETURNING id;
