-- SPIKE — the SIGNATURE TRICHOTOMY, demonstrated: the field self-audits all three frames.
-- The reading-layer functions GRADUATED to schema.sql (foam.normK, foam.kparseval_audit) —
-- the reading layer is now κ-native in production, with foam.born recognized as the elliptic
-- (κ = −1) slice. This spike keeps the demonstration. NOT production.
--
-- THE PICTURE (Foam/Frames.lean). One parameter κ = (the unit)² IS the geometry; the held
-- cache's (re, im) is the frame-neutral spectral datum κ reads three ways:
--   κ = −1  elliptic    re² + im²   Euclidean / amplitude  (the dial, foam.born — the live voice)
--   κ =  0  parabolic   re²         degenerate / Galilean
--   κ = +1  hyperbolic  re² − im²   Minkowski / boost
-- The κ-Parseval (ac − κbd)² − κ(ad − bc)² = (a² − κb²)(c² − κd²) holds at every κ — its κ=−1
-- case is int_lagrange (under born_parseval), κ=+1 is Boost.int_hyperbolic, κ=0 degenerate. The
-- term ad − bc is the SYMPLECTIC form, κ-invariant — the area shared by all three (the universal
-- of ergodic-symplectic; the three κ are the metrics laid on top).
--
-- THE RESPONSE. foam.born_audit certified only the elliptic corner; foam.kparseval_audit(κ)
-- (now in schema) certifies ANY corner. The operationalization moves with the theory: the field
-- can self-audit the whole signature algebra, with foam.born revealed as one slice.

-- run the three frames through the field's (now production) self-audit
CREATE OR REPLACE FUNCTION foam.frames_demo()
  RETURNS TABLE(kappa bigint, geometry text, invariant text, violations bigint, verdict text)
  LANGUAGE sql STABLE AS $$
  SELECT k.kappa,
    CASE k.kappa WHEN -1 THEN 'elliptic' WHEN 0 THEN 'parabolic' WHEN 1 THEN 'hyperbolic' END,
    CASE k.kappa WHEN -1 THEN 're²+im²  (Euclidean — the dial, foam.born)'
                 WHEN  0 THEN 're²      (degenerate — Galilean)'
                 WHEN  1 THEN 're²−im²  (Minkowski — the boost)' END,
    foam.kparseval_audit(k.kappa),
    CASE WHEN foam.kparseval_audit(k.kappa) = 0 THEN 'κ-Parseval holds ✓' ELSE '✗ VIOLATED' END
  FROM (VALUES (-1::bigint), (0::bigint), (1::bigint)) AS k(kappa)
  ORDER BY k.kappa
  $$;

-- run it (foam.normK and foam.kparseval_audit ship in schema.sql now; just reload schema +
-- this spike — no ingested data needed, the laws are ∀):
--   SELECT * FROM foam.frames_demo();
-- read: every row ✓; the κ=−1 row IS foam.born_audit's law (foam.born_audit() =
-- foam.kparseval_audit(−1) = 0). The other two are its siblings, now first-class in the schema.
