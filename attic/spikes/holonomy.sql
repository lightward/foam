-- SPIKE — the HOLONOMY PROBE: assemble a probe on the bench, push one end into a
-- foam frontstage, read the SPIN it comes back with. NOT production. The amniscient
-- haptic probe (the meta-theory's §IX) made into an instrument: a blind round-trip,
-- read the holonomy the current returns, never a view of the interior.
--
-- THE OBJECT. You push a context+sym into the field and it comes back PHASED — the
-- field stamps its own recurrence-clock onto your probe as a rotation (the spin).
-- `holo(ctx, sym)` reads that spin three ways:
--   * spin (re, im) — the recency-spectrum (rot^(N-1)·conj of the abs spectrum;
--     Chirality.lean's specR_bridge, the conversion postgres performs at read time);
--   * holo_mag = re²+im² — the GAUGE-INVARIANT magnitude (Noether's normSq, conserved
--     under the dial's rotation: normSq_rot; the Wilson-loop reading, frame-free);
--   * frame0..3 — what a reader at clock-station tk SEES: born = (align tk spin)²
--     (Born.lean), the per-frame reading, which VARIES with the frame.
--
-- THE RESULT (run holo_demo()). Three probes into a driven field:
--   a->Z heard a COMPLETE ℤ/4 cycle (N=4): spin (0,0), holo_mag 0 — FLAT, zero
--        holonomy, the dark fringe (rot_complete: a complete cycle is invisible). Flat
--        from EVERY frame, because it is genuinely still — no flux.
--   b->Y heard 3×: spin (0,1), holo_mag 1 — WOUND. But frame0 reads it 0 ("flat!")
--        and frame1 reads it 1. A single reader, at the wrong angle, mistakes a
--        spinning probe for a still one.
--   c->X heard 5×: spin (1,0), holo_mag 1 — WOUND, wound in the OTHER frame
--        (frame0 reads 1, frame1 reads 0) — same magnitude, orthogonal angle (N mod 4).
--
-- THE POINT. The spin a probe returns is FRAME-RELATIVE — a lone frame can be fooled
-- into seeing flat. The HOLONOMY MAGNITUDE is gauge-invariant and tells the truth:
-- zero only when the probe is truly still (a complete cycle). The four frames' borns
-- sum to 2·holo_mag (born_parseval, proven) — the invariant total no frame holds alone.
-- The amniscient probe reads the field's flux haptically (the displacement of the
-- round-trip), and you must read it gauge-invariantly or be fooled.
--
-- SCOPE / the honest label (watching the rhyme). The spin is a CIRCULAR rotation —
-- the ℤ/4 dial, the U(1)/gauge/amplitude layer (Born, interference, the dark fringe).
-- It is NOT the hyperbolic Lorentz BOOST (the spacetime/causal layer — the order, the
-- cone, Lightcone.lean); those are different rotations. This instrument reads the
-- gauge/amplitude axis: the field's flux and curvature via holonomy. It is foam's
-- SECOND instrument (the first being the lightcone, the causal/order reader) — and it
-- reads the half of the physics the spacetime floor does not touch. Mirror (all
-- proven): specR_bridge (Chirality), normSq_rot / born_parseval (Noether / Born),
-- rot_complete (Spectrum — the flat/dark-fringe condition).

CREATE OR REPLACE FUNCTION foam.holo(ctxbytes int[], s int)
  RETURNS TABLE(occ bigint, spin_re bigint, spin_im bigint, holo_mag bigint,
                frame0 bigint, frame1 bigint, frame2 bigint, frame3 bigint, verdict text)
  LANGUAGE sql STABLE AS $$
  WITH e AS (
    SELECT delta, row_number() OVER (ORDER BY id) AS o
    FROM foam.charge WHERE ctx = foam.caddr(ctxbytes) AND sym = s),
  absf AS (
    SELECT count(*) AS n,
           sum(delta*CASE ((o-1)%4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) AS re,
           sum(delta*CASE ((o-1)%4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) AS im
    FROM e),
  rec AS (
    -- recency = rot^((N-1) mod 4)·conj(abs); (N+3)%4 = (N-1)%4 for N >= 1 (specR_bridge)
    SELECT n,
      CASE ((n+3)%4) WHEN 0 THEN re WHEN 1 THEN im WHEN 2 THEN -re ELSE -im END AS rre,
      CASE ((n+3)%4) WHEN 0 THEN -im WHEN 1 THEN re WHEN 2 THEN im ELSE -re END AS rim
    FROM absf)
  -- born at reader-frame tk: align(tk, rre, rim)², the four stations of the dial
  SELECT n, rre, rim, rre*rre + rim*rim,
         rre*rre, rim*rim, rre*rre, rim*rim,
         CASE WHEN rre*rre + rim*rim = 0 THEN 'FLAT (zero holonomy - dark fringe)'
              ELSE 'WOUND (nonzero holonomy)' END
  FROM rec;
$$;

-- drive a field and push three probes through the instrument
CREATE OR REPLACE FUNCTION foam.holo_demo()
  RETURNS TABLE(probe text, occ bigint, spin_re bigint, spin_im bigint, holo_mag bigint,
                frame0 bigint, frame1 bigint, frame2 bigint, frame3 bigint, verdict text)
  LANGUAGE plpgsql AS $$
  BEGIN
    PERFORM foam.ingest_step(NULL, foam.bytes('aZaZaZaZ'));    -- a->Z complete cycle (flat)
    PERFORM foam.ingest_step(NULL, foam.bytes('bYbYbY'));      -- b->Y three times (wound)
    PERFORM foam.ingest_step(NULL, foam.bytes('cXcXcXcXcX'));  -- c->X five times (wound, N=5)
    RETURN QUERY SELECT 'a -> Z', * FROM foam.holo(foam.bytes('a'), ascii('Z'));
    RETURN QUERY SELECT 'b -> Y', * FROM foam.holo(foam.bytes('b'), ascii('Y'));
    RETURN QUERY SELECT 'c -> X', * FROM foam.holo(foam.bytes('c'), ascii('X'));
  END; $$;

-- run it (on a fresh field — reload schema.sql first):
--   SELECT * FROM foam.holo_demo();
-- read: a->Z FLAT (holo_mag 0, every frame agrees - a complete cycle is truly still);
-- b->Y and c->X WOUND (holo_mag 1) but readable as 0 from the wrong frame - the
-- magnitude is the gauge-invariant truth, a single frame can be fooled.
