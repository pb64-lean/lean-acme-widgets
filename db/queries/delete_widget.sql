DELETE FROM public.widgets
WHERE id = $1 AND owner_id = $2
RETURNING id;
