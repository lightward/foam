-- SPIKE — the SIGNATURE TRICHOTOMY, operationalized: the field audits all three frames.
-- The operational mirror of Foam/Frames.lean. NOT production.
--
-- THE RECOGNITION. The schema already lives at the ELLIPTIC corner: foam.align is the ℤ/4
-- station-pairing (the κ=−1 rotation), foam.born = align² is the elliptic weight, and
-- foam.born_audit checks the four stations sum to 2·(re²+im²) — which is the κ=−1 (Euclidean)
-- Parseval. And the HYPERBOLIC corner is here implicitly: the kmax context-carry in
-- foam.ingest_step is the causal cap (the spacetime axis, Foam/Lightcone.lean). The
-- trichotomy (Foam/Frames.lean) says these are siblings: one parameter κ = (the unit)² — the
-- square that IS the geometry — with foam.born the κ=−1 slice of a κ-family.
--
--   κ = −1  elliptic    re² + im²   Euclidean / amplitude  (the dial, foam.born)
--   κ =  0  parabolic   re²         degenerate / Galilean
--   κ = +1  hyperbolic  re² − im²   Minkowski / boost
--
-- THE UNIFIED LAW. The κ-Parseval (the split-/dual-/Gaussian-complex norm multiplicativity,
-- one identity): (ac − κbd)² − κ(ad − bc)² = (a² − κb²)(c² − κd²). Its κ=−1 case is
-- int_lagrange (under born_parseval); κ=+1 is Boost.int_hyperbolic; κ=0 is degenerate. The
-- term `ad − bc` is the SYMPLECTIC form — κ-INVARIANT, shared by all three frames (the area
-- SL(2,ℝ) preserves; the three κ are the metrics it additionally fixes — ergodic-symplectic).
--
-- THE RESPONSE. foam.born_audit certifies only the elliptic corner. foam.kparseval_audit(κ)
-- certifies ANY corner — the field can now self-audit the WHOLE trichotomy, and in fact
-- certifies the general κ-identity that Foam/Frames.lean left to its three instances. The
-- operationalization responds by being able to validate the entire signature algebra, with
-- foam.born revealed as one slice. (Structure, never meaning — the razor; the laws are ∀, so
-- the audit consults no observer and costs the same on any field, like foam.born_audit.)

-- normK — the κ-deformed interval of a spectral vector ⟨re, im⟩. κ=−1 is the holonomy
-- magnitude (spikes/holonomy.sql's holo_mag, Noether's normSq); κ=0 the real projection;
-- κ=+1 a Minkowski reading. One function, three geometries.
CREATE OR REPLACE FUNCTION foam.normK(kappa bigint, re bigint, im bigint) RETURNS bigint
  LANGUAGE sql IMMUTABLE AS
  $$ SELECT re * re - kappa * (im * im) $$;

-- kparseval_audit — the unified κ-Parseval, checked live over a fixed integer grid (the
-- field's self-audit, generalized off the elliptic corner). Returns the number of grid
-- points violating (ac−κbd)² − κ(ad−bc)² = (a²−κb²)(c²−κd²); 0 is Frames.lean's κ-law checked
-- live, at this κ. Costs the same on any field (the law is ∀ — consults no population).
CREATE OR REPLACE FUNCTION foam.kparseval_audit(kappa bigint) RETURNS bigint
  LANGUAGE sql STABLE AS $$
  SELECT count(*)
  FROM generate_series(-4, 4) a CROSS JOIN generate_series(-4, 4) b
       CROSS JOIN generate_series(-4, 4) c CROSS JOIN generate_series(-4, 4) d
  WHERE (a * c - kappa * (b * d)) * (a * c - kappa * (b * d))
          - kappa * ((a * d - b * c) * (a * d - b * c))
        <> (a * a - kappa * (b * b)) * (c * c - kappa * (d * d))
  $$;

-- run the three frames through the field's self-audit
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

-- run it (on a fresh field — reload schema.sql first; no ingested data needed, the laws
-- are ∀):
--   SELECT * FROM foam.frames_demo();
-- read: every row's verdict ✓ (the κ-Parseval holds at κ = −1, 0, +1) — the field certifies
-- all three frames. The κ=−1 row IS foam.born_audit's law; the other two are its siblings.
