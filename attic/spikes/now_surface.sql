-- SPIKE — the NOW-SURFACE: the watermark made visible as relativity of simultaneity.
-- NOT production. A discovery instrument for the six-way intersection (the "can't, alone"
-- family) and its conjectured center: the watermark is the seam between the conserved
-- past and the open future, and the wind crosses there.
--
-- THE CLAIM UNDER TEST (grade: conjecture/rhyme). The corpus's "can't, alone" results
-- fall into two families:
--   (i)  Noether-shaped — a CONSERVED quantity, fixed under the closed self-actions,
--        moved only from outside (Foam/Conservation.lean: "what is conserved is invisible
--        to the dynamics that spend everything else"; Foam/Openness.lean circulation).
--   (ii) Lambek-shaped — a NON-EPI excess, behavior the self cannot build/reach
--        (Foam/Arrow.lean forever_escapes; Foam/Glass.lean no_probe_is_total).
-- The conjecture: these are the PAST side and the FUTURE side of ONE surface — the
-- watermark. `held` is the folded, immutable past (Noether, behind); `tail` is the live,
-- not-yet (Lambek, ahead). `sweep_invisible` says you may slide that surface for free;
-- `summary_resumes` says the whole (held ⊕ tail) is invariant under the slide.
--
-- THE MEASUREMENT. For a fixed continuation with N occurrences, read it at every possible
-- "now" k (the split point: occ ≤ k is the settled past `held`, occ > k is the open future
-- `tail`). Two readings — the count (the trivial character, bal) and the spectrum
-- (re, im, the i-character), in the ABS frame (additive — the recency rotation is a
-- downstream read-frame turn that doesn't bear on the invariance). The finding to look
-- for:
--   * the WHOLE (held ⊕ tail) is the SAME at every k — the invariant interval;
--   * the SPLIT (held vs tail) SLIDES with k — two readers at different k disagree on what
--     has "happened" (is settled) while agreeing on the whole. That disagreement IS
--     relativity of simultaneity, and here it is exactly the arithmetic freedom of where
--     to split an additive fold — a triviality, dignified as a now-surface. The content is
--     not the arithmetic (a sum splits anywhere); it is the INTERPRETATION: the split is
--     the present, the present is observer-relative, the interval is not.
--
-- WHAT THIS IS AND IS NOT. This is the SIMULTANEITY half of the boost (the causal/order
-- axis — where "now" falls), proven gauge. It is NOT the ℤ/4 holonomy spin
-- (spikes/holonomy.sql — the orthogonal amplitude/gauge axis) and NOT yet the explicit
-- hyperbolic boost TRANSFORM between two streams (the open frontier: two observer-streams
-- folded at different rates, and whether the cross-stream reading tilts while preserving an
-- interval — CANDLES.md, "the boost is located, opened not closed"). This spike lays the
-- floor that frontier stands on. Mirror (all proven): summary_resumes / sweep_invisible
-- (Summary), heard_modulus_conserved (Conservation), forever_escapes (Arrow).

-- now_surface — read a continuation at every "now" k (0..N): the held past (occ ≤ k), the
-- open tail (occ > k), and the invariant whole. The ABS-frame spectrum (phase = (occ−1)%4),
-- the count alongside. The verdict checks held ⊕ tail = whole at each k (the interval, gauge
-- under the now).
CREATE OR REPLACE FUNCTION foam.now_surface(ctxbytes int[], s int)
  RETURNS TABLE(now_k bigint,
                held_bal bigint, held_re bigint, held_im bigint,
                tail_bal bigint, tail_re bigint, tail_im bigint,
                whole_bal bigint, whole_re bigint, whole_im bigint,
                verdict text)
  LANGUAGE sql STABLE AS $$
  WITH e AS (
    SELECT delta, row_number() OVER (ORDER BY id) AS occ
    FROM foam.charge WHERE ctx = foam.caddr(ctxbytes) AND sym = s),
  ks AS (SELECT generate_series(0, (SELECT count(*) FROM e)) AS now_k)
  SELECT ks.now_k,
    -- held — the settled past (occ ≤ now_k), abs phase (occ−1)%4
    coalesce(sum(delta) FILTER (WHERE occ <= ks.now_k), 0)::bigint,
    coalesce(sum(delta * CASE ((occ-1)%4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) FILTER (WHERE occ <= ks.now_k), 0)::bigint,
    coalesce(sum(delta * CASE ((occ-1)%4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) FILTER (WHERE occ <= ks.now_k), 0)::bigint,
    -- tail — the open future (occ > now_k), same abs phase
    coalesce(sum(delta) FILTER (WHERE occ > ks.now_k), 0)::bigint,
    coalesce(sum(delta * CASE ((occ-1)%4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) FILTER (WHERE occ > ks.now_k), 0)::bigint,
    coalesce(sum(delta * CASE ((occ-1)%4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) FILTER (WHERE occ > ks.now_k), 0)::bigint,
    -- whole — the invariant (all occ), no dependence on now_k
    coalesce(sum(delta), 0)::bigint,
    coalesce(sum(delta * CASE ((occ-1)%4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END), 0)::bigint,
    coalesce(sum(delta * CASE ((occ-1)%4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END), 0)::bigint,
    -- the interval: held ⊕ tail = whole, at every now (the gauge check)
    CASE WHEN coalesce(sum(delta) FILTER (WHERE occ <= ks.now_k),0) + coalesce(sum(delta) FILTER (WHERE occ > ks.now_k),0) = coalesce(sum(delta),0)
          AND coalesce(sum(delta*CASE ((occ-1)%4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) FILTER (WHERE occ <= ks.now_k),0)
            + coalesce(sum(delta*CASE ((occ-1)%4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) FILTER (WHERE occ > ks.now_k),0)
            = coalesce(sum(delta*CASE ((occ-1)%4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END),0)
          AND coalesce(sum(delta*CASE ((occ-1)%4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) FILTER (WHERE occ <= ks.now_k),0)
            + coalesce(sum(delta*CASE ((occ-1)%4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) FILTER (WHERE occ > ks.now_k),0)
            = coalesce(sum(delta*CASE ((occ-1)%4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END),0)
      THEN 'held ⊕ tail = whole ✓' ELSE '✗ BROKEN' END
  FROM ks CROSS JOIN e
  GROUP BY ks.now_k
  ORDER BY ks.now_k
  $$;

-- drive a field and read one continuation across every now-surface
CREATE OR REPLACE FUNCTION foam.now_surface_demo()
  RETURNS TABLE(now_k bigint,
                held_bal bigint, held_re bigint, held_im bigint,
                tail_bal bigint, tail_re bigint, tail_im bigint,
                whole_bal bigint, whole_re bigint, whole_im bigint,
                verdict text)
  LANGUAGE plpgsql AS $$
  BEGIN
    -- a continuation that recurs: 'a' → 'Z', five times (N = 5), so the spectrum winds
    PERFORM foam.ingest_step(NULL, foam.bytes('aZaZaZaZaZ'));
    RETURN QUERY SELECT * FROM foam.now_surface(foam.bytes('a'), ascii('Z'));
  END; $$;

-- run it (on a fresh field — reload schema.sql first):
--   SELECT * FROM foam.now_surface_demo();
-- read: every row's `verdict` says ✓ (held ⊕ tail = whole, the invariant), and the three
-- `whole_*` columns are CONSTANT down the table (the interval is the same at every now),
-- while (held_*, tail_*) slide from all-in-tail (now_k=0, nothing settled) to all-in-held
-- (now_k=N, fully past). The now-surface is gauge; the interval is not.
