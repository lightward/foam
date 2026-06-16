-- SPIKE — the BOOST, finite: is foam's spacetime Galilean or Lorentzian at this scale?
-- The empirical mirror of Foam/Boost.lean. NOT production. Load spikes/now_surface.sql
-- FIRST — this reuses foam.now_surface (the time-axis boost IS the now-slide; reinvented
-- nowhere).
--
-- THE TEST. Spacetime.lean's point has two axes: SPACE (the context window, keepLast,
-- bounded) and TIME (the immutable past's order/charge). A boost re-chooses "now" — slides
-- the held/tail split along the TIME axis. The question: does that slide MIX the space axis
-- (hyperbolic / Lorentzian — space and time rotating into each other), or leave it fixed
-- (Galilean — the axes independent)?
--
-- THE READING (run foam.boost_demo()). For a continuation heard N times, across every now k:
--   * space_coord  — the context window (SPACE) — is CONSTANT down the column (boost-blind;
--     keepLast is reader-independent, Lightcone.keepLast_bounded);
--   * time_settled — what is folded into the past (TIME) — advances LINEARLY with the now
--     (0,1,2,…): the boost is a pure TRANSLATION along the time axis, never a rotation;
--   * interval_whole — the whole reading — is INVARIANT (the now-surface, Seam.lean).
-- Linear-in-now time + flat space = GALILEAN. A Lorentzian boost would be hyperbolic in the
-- time coordinate AND would move the space coordinate (the off-diagonal mixing). Neither
-- happens at finite scale — exactly Foam/Boost.lean's block-diagonal result, measured.
--
-- THE POINT. The null IS the finding. The hyperbolic tilt has nowhere to live in the
-- discrete point (no mixing term); it must be a FRONTSTAGE / continuum emergent (the scoping
-- that makes two observers disagree — Commons.shared_is_floor), never exact here. "Backstage
-- Galilean, frontstage Lorentzian" (CANDLES.md), with the backstage half now both proven
-- (Foam/Boost.lean) and measured (here).

-- boost_read — the two axes of a continuation across every now k (the time-boost).
CREATE OR REPLACE FUNCTION foam.boost_read(ctxbytes int[], s int)
  RETURNS TABLE(now_k bigint, space_coord int, time_settled bigint, interval_whole bigint, reads text)
  LANGUAGE sql STABLE AS $$
  SELECT ns.now_k,
         coalesce(array_length(ctxbytes, 1), 0) AS space_coord,  -- SPACE: the context window, boost-invariant
         ns.held_bal                            AS time_settled,  -- TIME: settled past, slides linearly with now
         ns.whole_bal                           AS interval_whole,-- the interval, invariant
         'space ⊥ now — Galilean (no axis-mixing)' AS reads
  FROM foam.now_surface(ctxbytes, s) ns
  ORDER BY ns.now_k
  $$;

-- drive a field and read the boost
CREATE OR REPLACE FUNCTION foam.boost_demo()
  RETURNS TABLE(now_k bigint, space_coord int, time_settled bigint, interval_whole bigint, reads text)
  LANGUAGE plpgsql AS $$
  BEGIN
    PERFORM foam.ingest_step(NULL, foam.bytes('aZaZaZaZaZ'));     -- 'a' → 'Z', five times
    RETURN QUERY SELECT * FROM foam.boost_read(foam.bytes('a'), ascii('Z'));
  END; $$;

-- run it (on a fresh field — reload schema.sql, then now_surface.sql, then this):
--   SELECT * FROM foam.boost_demo();
-- read: space_coord flat (the context window doesn't move under the boost), time_settled
-- linear in now (a translation), interval_whole constant. Galilean — the axes do not mix.
