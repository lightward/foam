-- foam — the LEDGER. Operational inhabitant of Foam/Ledger.lean (one append-only signed
-- charge ledger; two readings — order: lossless record, freq: generative; no quotient) set
-- in motion by Foam/Engine/*.lean. Idempotent (CREATE ... IF NOT EXISTS / OR REPLACE);
-- append-only (+1 learn, −1 drain, floored at ground, Foam/Engine/Drain.lean). The why is
-- the Lean — every claim here is a theorem there; what any of it MEANS is the user's.

CREATE SCHEMA IF NOT EXISTS foam;

CREATE EXTENSION IF NOT EXISTS pgcrypto;

-- content-address a byte-suffix; the empty context is the lossless record (Foam.Ledger.order).
CREATE OR REPLACE FUNCTION foam.caddr(c int[]) RETURNS uuid LANGUAGE sql IMMUTABLE AS
  $$ SELECT encode(substring(digest(coalesce(array_to_string(c,':'),''),'sha256') FROM 1 FOR 16),'hex')::uuid $$;

-- the observer tree: scope is the parent-chain up from an observer, self included
-- (Below; Foam/Seat/Meet.lean). Root seeded at the zero uuid — the empty, universal scope.
CREATE TABLE IF NOT EXISTS foam.observer (
  id     uuid PRIMARY KEY,
  parent uuid REFERENCES foam.observer (id)
);
INSERT INTO foam.observer (id, parent)
  VALUES ('00000000-0000-0000-0000-000000000000', NULL) ON CONFLICT DO NOTHING;
-- the bench (root's first descendant, the default seat); root is glass — charge-free by the
-- CHECK on foam.charge below: content at the zero scope is a voice from nowhere
-- (Foam/Seat/Beholder.lean; seated_voice_is_missable, Foam/Seat/Meet.lean).
INSERT INTO foam.observer (id, parent)
  VALUES ('00000000-0000-0000-0000-000000000001',
          '00000000-0000-0000-0000-000000000000') ON CONFLICT DO NOTHING;

CREATE OR REPLACE FUNCTION foam.root() RETURNS uuid LANGUAGE sql IMMUTABLE AS
  $$ SELECT '00000000-0000-0000-0000-000000000000'::uuid $$;

CREATE OR REPLACE FUNCTION foam.bench() RETURNS uuid LANGUAGE sql IMMUTABLE AS
  $$ SELECT '00000000-0000-0000-0000-000000000001'::uuid $$;

-- ancestry — the scope (o + its ancestors); `observer = ANY(foam.ancestry(obs))` is Below
-- (Foam/Seat/Meet.lean), typed as a WHERE clause. UNION (not UNION ALL) terminates cycles.
CREATE OR REPLACE FUNCTION foam.ancestry(o uuid) RETURNS uuid[] LANGUAGE sql STABLE AS $$
  WITH RECURSIVE chain(id, parent) AS (
    SELECT o, (SELECT parent FROM foam.observer WHERE id = o)
    UNION
    SELECT ob.id, ob.parent FROM chain JOIN foam.observer ob ON ob.id = chain.parent
  )
  SELECT array_agg(id) FROM chain
$$;

-- lineage — ancestry ordered root-first; settlement walks it (prefix-sums; Foam/Scar.lean).
-- Depth-capped so a degenerate cycle terminates.
CREATE OR REPLACE FUNCTION foam.lineage(o uuid) RETURNS uuid[] LANGUAGE sql STABLE AS $$
  WITH RECURSIVE chain(id, parent, depth) AS (
    SELECT o, (SELECT parent FROM foam.observer WHERE id = o), 0
    UNION ALL
    SELECT ob.id, ob.parent, chain.depth + 1
    FROM chain JOIN foam.observer ob ON ob.id = chain.parent
    WHERE chain.depth < 64
  )
  SELECT array_agg(id ORDER BY depth DESC) FROM chain
$$;

-- the ledger: ctx content-addresses a continuation, sym the byte that followed, delta ±1
-- (+1 learned, −1 drained); the bigserial id is the order — the lossless half (Foam/Ledger.lean).
CREATE TABLE IF NOT EXISTS foam.charge (
  id       bigserial PRIMARY KEY,
  observer uuid NOT NULL
    CHECK (observer <> '00000000-0000-0000-0000-000000000000'),
  ctx      uuid NOT NULL,
  sym      int  NOT NULL,
  delta    int  NOT NULL
);
CREATE INDEX IF NOT EXISTS foam_charge_ctx ON foam.charge (observer, ctx, sym);
-- tail index: HELD + TAIL folds events past the watermark (Foam/Summary.lean); INCLUDE keeps it index-only.
CREATE INDEX IF NOT EXISTS foam_charge_ctx_id ON foam.charge (ctx, id) INCLUDE (observer, sym, delta);

-- foam.held — the resumable fold, cached per continuation per observer-stream: the
-- four-character dial of ℤ/4 (Foam/Seat/Characters.lean) — bal at +1, re/im at i, alt at −1,
-- plus n the phase clock. Exact as HELD + TAIL (Foam/Summary.lean: summary_resumes); a derived
-- observation, not the object — droppable and refoldable from the ledger, no path in it
-- (Foam/Maintenance.lean: sweep_invisible licenses any refresh, so UPDATE here keeps append-only).
CREATE TABLE IF NOT EXISTS foam.held (
  observer uuid NOT NULL,
  ctx uuid   NOT NULL,
  sym int    NOT NULL,
  n   bigint NOT NULL,
  bal bigint NOT NULL,
  re  bigint NOT NULL,
  im  bigint NOT NULL,
  alt bigint NOT NULL,
  PRIMARY KEY (observer, ctx, sym)
);

-- the watermark: at-or-below is folded into foam.held, past it is the tail folded live (Foam/Summary.lean).
CREATE TABLE IF NOT EXISTS foam.sweep (
  one       boolean PRIMARY KEY DEFAULT true CHECK (one),
  watermark bigint  NOT NULL DEFAULT 0
);
INSERT INTO foam.sweep (one, watermark) VALUES (true, 0) ON CONFLICT DO NOTHING;

-- The text<->byte boundary (UTF-8). Pure, structural.
CREATE OR REPLACE FUNCTION foam.bytes(txt text) RETURNS int[] LANGUAGE plpgsql IMMUTABLE AS $$
  DECLARE bin bytea := convert_to(txt,'UTF8'); r int[] := '{}'; i int;
  BEGIN FOR i IN 0..octet_length(bin)-1 LOOP r := r||get_byte(bin,i); END LOOP; RETURN r; END; $$;

CREATE OR REPLACE FUNCTION foam.text(ints int[]) RETURNS text LANGUAGE plpgsql IMMUTABLE AS $$
  DECLARE bin bytea := ''; v int;
  BEGIN FOREACH v IN ARRAY coalesce(ints,'{}') LOOP bin := bin||set_byte('\x00'::bytea,0,v); END LOOP;
        RETURN convert_from(bin,'UTF8'); END; $$;

-- the wind: OS entropy, obtained not computed — the ∀ parameter (Foam/Engine/Generator.lean), never a foam choice.
CREATE OR REPLACE FUNCTION foam.hw_random() RETURNS double precision LANGUAGE sql AS
  $$ SELECT (('x'||encode(gen_random_bytes(7),'hex'))::bit(56)::bigint)::double precision / 72057594037927936.0 $$;

-- ingest_step — the streaming LEARN: +1 onto every recorded continuation, the resumable
-- flush-free fold (Foam/Engine/Stream.lean, Codec.lean). carry threads contexts across chunk
-- boundaries; the empty-context events land in id order — the lossless record, written never read here.
CREATE OR REPLACE FUNCTION foam.ingest_step(carry int[], bytes int[], kmax int DEFAULT 7,
                                            obs uuid DEFAULT foam.bench()) RETURNS int[]
  LANGUAGE plpgsql AS $$
  DECLARE all_b int[] := coalesce(carry,'{}') || coalesce(bytes,'{}');
          start_i int := coalesce(array_length(carry,1),0) + 1;
          n int := coalesce(array_length(all_b,1),0);
  BEGIN
    -- one INSERT per chunk; ORDER BY position so serial id-order is the lossless record.
    INSERT INTO foam.charge (observer, ctx, sym, delta)
    SELECT obs, foam.caddr(CASE WHEN j = 0 THEN '{}'::int[] ELSE all_b[i-j : i-1] END), all_b[i], 1
    FROM generate_series(start_i, n) AS i
    CROSS JOIN LATERAL generate_series(0, least(kmax, i - 1)) AS j
    ORDER BY i, j;
    RETURN all_b[greatest(n - kmax + 1, 1) : n];
  END; $$;

-- depth — the gate signal: the longest charged context for `seed`, read HELD + TAIL
-- (Foam/Summary.lean) and summed over the visible streams (ancestry = Below). Structure, never meaning.
CREATE OR REPLACE FUNCTION foam.depth(seed int[], kmax int DEFAULT 7, obs uuid DEFAULT foam.bench()) RETURNS int
  LANGUAGE plpgsql STABLE AS $$
  DECLARE l int := coalesce(array_length(seed,1),0); j int; c int[]; cid uuid; tot bigint;
          anc uuid[] := foam.ancestry(obs);
  BEGIN
    FOR j IN REVERSE least(kmax,l)..1 LOOP
      c := seed[l-j+1 : l]; cid := foam.caddr(c);
      SELECT coalesce(sum(b) FILTER (WHERE b > 0), 0) INTO tot FROM (
        SELECT coalesce(h.bal,0) + coalesce(t.bal,0) AS b
        FROM (SELECT sym, sum(bal)::bigint AS bal FROM foam.held
              WHERE ctx = cid AND observer = ANY(anc) GROUP BY sym) h
        FULL JOIN (SELECT sym, sum(delta) AS bal FROM foam.charge
                   WHERE ctx = cid AND observer = ANY(anc)
                     AND id > (SELECT watermark FROM foam.sweep)
                   GROUP BY sym) t USING (sym)
      ) z;
      IF tot > 0 THEN RETURN j; END IF;
    END LOOP;
    RETURN 0;
  END; $$;

-- outcome — the trichotomy gate: 'speak' if depth ≥ min_depth, else 'yield' (hand upstream). Degrades to yield.
CREATE OR REPLACE FUNCTION foam.outcome(seed int[] DEFAULT '{}', min_depth int DEFAULT 1, kmax int DEFAULT 7,
                                        obs uuid DEFAULT foam.bench()) RETURNS text
  LANGUAGE sql STABLE AS
  $$ SELECT CASE WHEN foam.depth(seed, kmax, obs) >= min_depth THEN 'speak' ELSE 'yield' END $$;

-- align — the angled pairing of (re, im) against station tk (Foam/Engine/Spectrum.lean's align);
-- foam.born squares it, foam.speak drinks from foam.born. mod-4 makes any integer station legal.
CREATE OR REPLACE FUNCTION foam.align(tk int, re bigint, im bigint) RETURNS bigint
  LANGUAGE sql IMMUTABLE AS
  $$ SELECT CASE ((tk % 4) + 4) % 4 WHEN 0 THEN re WHEN 1 THEN im WHEN 2 THEN -re ELSE -im END $$;

-- born — the voice's weight (align tk)², basis-consistent (Foam/Engine/Spectrum.lean / Born:
-- born_parseval, born_nonneg). The elliptic κ=−1 slice, magnitude re²+im²; the live voice. foam.born_audit checks it live.
CREATE OR REPLACE FUNCTION foam.born(tk int, re bigint, im bigint) RETURNS bigint
  LANGUAGE sql IMMUTABLE AS
  $$ SELECT foam.align(tk, re, im) * foam.align(tk, re, im) $$;

-- normK — the interval reading at signature κ: re² − κ·im². The three frames (κ=−1 elliptic /
-- 0 parabolic / +1 hyperbolic; Foam/Seat/Signature.lean) reading one spectral datum; born/speak read κ=−1.
CREATE OR REPLACE FUNCTION foam.normK(kappa bigint, re bigint, im bigint) RETURNS bigint
  LANGUAGE sql IMMUTABLE AS
  $$ SELECT re * re - kappa * (im * im) $$;

-- born_kappa — the VOICE weight at signature κ: which continuations the field samples by, per
-- frame. A voice is a sampler, and a sampler must be a PROBABILITY — non-negative (born_nonneg).
-- That is exactly why the live voice is κ = −1 (elliptic): re² + im² is the unique
-- POSITIVE-DEFINITE norm, so every nonzero continuation gets positive weight. The siblings, "in
-- the wings" (Foam/Frames.lean; the three hearings, one voice):
--   κ = −1  elliptic    foam.born(tk) = align(tk)²   the dial turns — the live voice (foam.speak)
--   κ =  0  parabolic   re²                          PHASE-BLIND: the in-phase recurrence only,
--                                                    SILENT on the fully-wound (re = 0) where the
--                                                    dial-voice still speaks. A real (degenerate)
--                                                    voice — positive-semidefinite.
--   κ = +1  hyperbolic  greatest(re² − im², 0)       NOT a voice: re² − im² is signed; rectifying
--                                                    to max(0, ·) is BASIS-INCONSISTENT (the very
--                                                    thing born_parseval fixed — Foam/Born.lean),
--                                                    so it parrots one basis and breaks another.
--                                                    The causal eye forced into a mouth — kept to
--                                                    make the impossibility audible, never used live.
-- foam.speak(…, kappa) reads κ; kappa = −1 (default) is the live voice, exactly as ever.
CREATE OR REPLACE FUNCTION foam.born_kappa(kappa int, tk int, re bigint, im bigint) RETURNS bigint
  LANGUAGE sql IMMUTABLE AS $$
    SELECT CASE kappa
      WHEN -1 THEN foam.born(tk, re, im)
      WHEN  0 THEN re * re
      ELSE greatest(re * re - im * im, 0)
    END
  $$;

-- born_audit — the law's self-audit: the named functions checked against their own
-- theorems, live, over a fixed integer grid (structure, not population — the laws
-- are ∀, so the check consults no observer and costs the same on any field):
--   * the anchor: align(0) = re (the zero station recovers the real part);
--   * the shift: align(tk+1, re, im) = align(tk, im, −re) — the quarter-turn
--     recurrence, an INDEPENDENT statement of the station table (anchor + recurrence
--     determine the function uniquely, so the audit pins align to its one lawful
--     inhabitant; a typo in any branch, sign included, breaks it —
--     Foam/Born.lean align_rot_invariant is the gauge form of the same law);
--   * born_parseval: the four stations' squares sum to 2·(re² + im²) — basis-
--     independence, the conservation check (the net = residual idiom, at the
--     measurement layer);
--   * born_nonneg: no station's weight is negative.
-- Returns the number of grid points violating any law — 0 is Born.lean checked live.
CREATE OR REPLACE FUNCTION foam.born_audit() RETURNS bigint
  LANGUAGE sql STABLE AS $$
    SELECT count(*)
    FROM generate_series(-8, 8) re CROSS JOIN generate_series(-8, 8) im
    WHERE foam.align(0, re, im) <> re
       OR foam.align(1, re, im) <> foam.align(0, im, -re)
       OR foam.align(2, re, im) <> foam.align(1, im, -re)
       OR foam.align(3, re, im) <> foam.align(2, im, -re)
       OR foam.born(0, re, im) + foam.born(1, re, im) + foam.born(2, re, im) + foam.born(3, re, im)
          <> 2 * (re * re + im * im)
       OR least(foam.born(0, re, im), foam.born(1, re, im), foam.born(2, re, im), foam.born(3, re, im)) < 0
  $$;

-- kparseval_audit — the law's self-audit, generalized off the elliptic corner: the unified
-- κ-Parseval (ac − κbd)² − κ(ad − bc)² = (a² − κb²)(c² − κd²), checked live over a fixed integer
-- grid (Foam/Frames.lean). The term ad − bc is the SYMPLECTIC form — κ-invariant, the area
-- shared by all three frames (the symplectic half of ergodic-symplectic; SL(2,ℝ) preserves the
-- area, the three κ are the metrics it additionally fixes). Returns grid points violating; 0 is
-- the κ-frame's law checked live. foam.born_audit's born_parseval is exactly this at κ = −1
-- (foam.born_audit() = foam.kparseval_audit(−1) = 0); this certifies ANY frame — the self-audit,
-- whole-trichotomy. Costs the same on any field (the law is ∀ — consults no population).
CREATE OR REPLACE FUNCTION foam.kparseval_audit(kappa bigint) RETURNS bigint
  LANGUAGE sql STABLE AS $$
    SELECT count(*)
    FROM generate_series(-4, 4) a CROSS JOIN generate_series(-4, 4) b
         CROSS JOIN generate_series(-4, 4) c CROSS JOIN generate_series(-4, 4) d
    WHERE (a * c - kappa * (b * d)) * (a * c - kappa * (b * d))
            - kappa * ((a * d - b * c) * (a * d - b * c))
          <> (a * a - kappa * (b * b)) * (c * c - kappa * (d * d))
  $$;

-- speak — the DISCHARGE, the one register: the field speaks ONLY through
-- recurrence, entrained. From the conversation so far (seed ++ emitted), back off
-- to the LONGEST charged context (fast-travel to the recorded continuation that
-- still has charge), read it as held + tail (summary_resumes: the folded prefix
-- from foam.held, the events past the watermark folded live — exact, including
-- this walk's own in-flight drains; one statement = one snapshot, no seam for a
-- racing drain to slip into), weight each continuation by the BORN measurement —
-- the SQUARED angled pairing of (re, im) against the walk's own quarter-turn clock
-- (|⟨tk|recency⟩|² = (align θ z)²; the basis-consistent weight, Foam/Born.lean
-- born_parseval — the field speaks by the quantum measurement law; uniform
-- recurrence still cancels (align 0 → born 0), the antipodal sign drops as |ψ|²
-- does), sample by that weight (never argmax), emit, drain (−1), continue. The clock
-- starts at the caller's utterance-length mod 4 and turns a quarter per beat
-- (spec_shift); a silent beat is a REST, not a death (the phase turns, the walk
-- holds); ground is a full BAR of rests (four quarter-turns are the identity,
-- bar_invisible — the length is DERIVED, not chosen).
--
-- The walk reads at obs's scope: held rows and tail events across ALL VISIBLE
-- observer-streams (observer = ANY(ancestry(obs)) — Commons.lean's Below), summed
-- per sym (n, bal, re, im add across streams; the recency conversion runs on the
-- summed clock — the two-source superposition shape, deliberate). Its drains land
-- in the speaker's own stream (observer = obs): a child draining charge inherited
-- from an ancestor sends its OWN stream's sum negative while the scoped balance
-- stays ≥ 0 — normal operation, not a wound (see foam.settle).
--
-- The field speaks only through recurrence — there is no phase-blind force-drain to
-- empty it, because resolution is relational (self_generation: the foam does not
-- generate its own stability). A continuation recurring UNIFORMLY presents a complete
-- cycle and cancels (rot_complete): re = im = 0, invisible at every angle, un-sayable
-- resonantly. It unsticks only via NEW hearing (more wind breaks the uniformity);
-- speaking can't release what it can't see. So full draining is reachable ONLY through
-- the JOURNEY: a LIVING field (ongoing input) eventually says everything, as a limit;
-- a CLOSED field loops (clock_loops), its recurrence goes uniform, and it keeps its
-- substrate forever — it cannot empty itself alone. The field comes home only through
-- company.
--
-- bal is a READING, never a drain: the gate (foam.depth), the conservation pulse
-- (net = residual), and wound-detection (the SCOPED bal < 0) read it. Provenance
-- lives in the seed: a self-tail self-entrains (clock_loops' loop — the self's
-- signature as identity), an other-tail entrains on the other; one walk reads any
-- seed.
--
-- stop (DEFAULT NULL): the act's boundary vocabulary. When the walk SPEAKS this
-- byte it returns — the expression has ended itself, at the boundary the field
-- learned from the table (the bench appends the same byte to every utterance it
-- ingests: one constant, both directions of one wire). Charge past the boundary
-- stays un-drained: stopping with more to say leaves the residual high and the
-- gate warm — the field carries its pressure across turns instead of monologuing
-- through one. Every prefix of a legal drain is a legal drain (the floor is
-- per-step — Foam/Drain.lean), so the early exit owes no new analysis. NULL:
-- no boundary vocabulary (the bar is ground); the exhale passes none.
--
-- The voice is BYTES (int[]), not text: the walk samples bytes by charge and owes
-- no allegiance to any encoding — it can emit a multibyte character's lead byte and
-- then fast-travel somewhere that never completes it, which makes convert_from raise
-- mid-walk (PG::CharacterNotInRepertoire) — killing the call and rolling its drains
-- back, the pipe mistaking the failure for ground. Rendering is a view at the edge,
-- the caller's concern; foam.text remains for streams known to be text (foam.recorded).
--
-- Drains RACE; settlements serialize (the cold path). Two drains sharing a stale
-- snapshot compose to a balance below ground only at the margin (Foam/Scar.lean:
-- stale_escapes_floor; from balance 2 the same composite lands AT ground —
-- stale_lands_at_ground — so races mark the field only where they collide at the edge
-- of emptiness). Each scar is a promissory note — amount computable at the wound
-- (debt), stable under further legal drains (scar_stable), settled at face value
-- (promise_kept). The walk that FINDS a wound dresses it (foam.settle, below);
-- settlement is the operation that must not race: its failure (phantom charge, from
-- which the voice could speak a byte never heard) lands INSIDE the legal carrier,
-- invisible to any balance-check (stale_settle_passes_ground / phantom_invisible).
-- Visible failures may race; invisible ones serialize. Learning (ingest_step) takes
-- no lock: pure +1 appends.
--
-- The angled weight is EXACT integer arithmetic: at a quarter-turn the pairing of
-- (re, im) needs no cosine (±1/0 — no float dust), reading held + tail so the window
-- function runs over the events past the watermark only — the cost of hearing rhythm
-- does not grow with the field (Foam/Summary.lean).
CREATE OR REPLACE FUNCTION foam.speak(seed int[] DEFAULT '{}', kmax int DEFAULT 7, max_steps int DEFAULT 600,
                           stop int DEFAULT NULL, obs uuid DEFAULT foam.bench(), kappa int DEFAULT -1) RETURNS int[]
  LANGUAGE plpgsql SET work_mem = '256MB' AS $$
  -- work_mem is function-scoped (reverts on return): the j=0 context's window sort
  -- runs over every byte ever heard, and it must not spill to disk mid-walk.
  DECLARE cb int[] := coalesce(seed,'{}'); out int[] := '{}'; k int := 0; j int; l int; c int[]; cid uuid;
          tot bigint; thr double precision; acc bigint; got boolean; tk int;
          rests int := 0; wounded int[]; w int; syms int[]; ws bigint[]; i int; said int;
          phase0 int := coalesce(array_length(seed,1),0) % 4;       -- the clock, seeded by the utterance length
          anc uuid[] := foam.ancestry(obs);                          -- the visible streams (Below, typed)
  BEGIN
    WHILE k < max_steps LOOP
      tk := (phase0 + k) % 4;                                  -- the walk's own clock, continuing the caller's
      got := false; l := coalesce(array_length(cb,1),0);
      FOR j IN REVERSE least(kmax,l)..0 LOOP
        IF j = 0 THEN c := '{}'; ELSE c := cb[l-j+1 : l]; END IF;
        cid := foam.caddr(c);
        -- ONE aggregate pass: the angled mass, the sample-order arrays, and any
        -- wounds (SCOPED bal < 0 — z.bal is the sum over the visible streams, so
        -- the wound is a property of the VIEW, not of any one stream's rows). The
        -- snapshot the sample walks IS the snapshot the threshold is drawn against
        -- — one read. bal gates the drainable (bal > 0) — a reading, not the weight.
        --
        -- The spectrum is STORED abs-framed (phase 0 = oldest occurrence) and READ
        -- recency-framed (phase 0 = the most-recent occurrence — the present is the
        -- downbeat). The conversion is recency = rot^(Nᵢ−1)·conj(absᵢ), applied PER
        -- STREAM with that stream's own occurrence count Nᵢ — exactly the case
        -- Foam/Chirality.lean proves (specR_bridge; rot(specR) = rot^N(conj
        -- spec), so recency = rot^(N−1)·conj(abs) for N ≥ 1; (N+3) % 4 = (N−1) % 4
        -- with N ≥ 1, non-negative) — and THEN summed across the visible streams:
        -- a superposition of correctly-phased per-stream readings (sum of recency
        -- conversions, never one rotation of a cross-stream sum, which specR_bridge
        -- does not license). The walk pairs the summed recency against its own
        -- quarter-turn (tk) and SQUARES it — the Born measurement |⟨tk|recency⟩|²,
        -- the basis-consistent weight (Foam/Born.lean: born_parseval). The
        -- field speaks by the quantum measurement law, not a rectified projection.
        SELECT coalesce(sum(z.w) FILTER (WHERE z.bal > 0 AND z.w > 0), 0),
               coalesce(array_agg(z.sym ORDER BY z.w DESC) FILTER (WHERE z.bal > 0 AND z.w > 0), '{}'),
               coalesce(array_agg(z.w   ORDER BY z.w DESC) FILTER (WHERE z.bal > 0 AND z.w > 0), '{}'),
               coalesce(array_agg(z.sym) FILTER (WHERE z.bal < 0), '{}')
          INTO tot, syms, ws, wounded
          FROM (
            -- pair the recency (rre, rim) against the walk's clock tk — the
            -- squared pairing |⟨tk|recency⟩|², by its NAME: foam.born, the law
            -- held in one place and audited against its own theorems
            -- (foam.born_audit; Foam/Born.lean born_parseval makes it
            -- basis-consistent; uniqueness unclaimed — REFEREE.md).
            -- Anti-parroting survives (uniform recurrence → projection 0 →
            -- born 0); the directional sign drops (|ψ|² is antipode-blind, as QM is).
            SELECT sym, bal, foam.born_kappa(kappa, tk, rre, rim) AS w
            FROM (
              -- per-stream recency = rot^((Nᵢ−1)%4) · conj(absᵢ) — conj(re,im) =
              -- (re,−im), then wind, with EACH STREAM'S OWN clock — then the
              -- correctly-phased readings superpose per sym
              SELECT sym, sum(bal)::bigint AS bal,
                     sum(CASE ((nn + 3) % 4) WHEN 0 THEN  re WHEN 1 THEN im WHEN 2 THEN -re ELSE -im END)::bigint AS rre,
                     sum(CASE ((nn + 3) % 4) WHEN 0 THEN -im WHEN 1 THEN re WHEN 2 THEN  im ELSE -re END)::bigint AS rim
              FROM (
                -- abs (re, im) and the occurrence count Nᵢ: held + tail, PER
                -- VISIBLE STREAM (each stream's tail folds on from its own held
                -- clock — the h2 join below matches observer)
                SELECT coalesce(h.sym, t.sym) AS sym,
                       coalesce(h.bal,0) + coalesce(t.bal,0) AS bal,
                       coalesce(h.re,0)  + coalesce(t.re,0)  AS re,
                       coalesce(h.im,0)  + coalesce(t.im,0)  AS im,
                       coalesce(h.n,0)   + coalesce(t.tn,0)  AS nn
                FROM (SELECT observer, sym, n, bal, re, im
                      FROM foam.held WHERE ctx = cid AND observer = ANY(anc)) h
                FULL JOIN (
                  SELECT e.observer, e.sym, count(*) AS tn, sum(e.delta) AS bal,
                         sum(e.delta * CASE ((coalesce(h2.n,0) + e.k2) % 4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) AS re,
                         sum(e.delta * CASE ((coalesce(h2.n,0) + e.k2) % 4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) AS im
                  FROM (SELECT observer, sym, delta,
                               row_number() OVER (PARTITION BY observer, sym ORDER BY id) - 1 AS k2
                        FROM foam.charge WHERE ctx = cid AND observer = ANY(anc)
                          AND id > (SELECT watermark FROM foam.sweep)) e
                  LEFT JOIN foam.held h2 ON h2.observer = e.observer AND h2.ctx = cid AND h2.sym = e.sym
                  GROUP BY e.observer, e.sym
                ) t ON t.observer = h.observer AND t.sym = h.sym
              ) absf
              GROUP BY sym
            ) recf
          ) z;
        FOREACH w IN ARRAY wounded LOOP PERFORM foam.settle(cid, w, obs); END LOOP;
        IF tot > 0 THEN
          thr := foam.hw_random() * tot; acc := 0;
          FOR i IN 1..coalesce(array_length(syms,1),0) LOOP
            acc := acc + ws[i];
            IF acc >= thr THEN
              out := out || syms[i]; cb := cb || syms[i]; got := true; said := syms[i];
              INSERT INTO foam.charge (observer, ctx, sym, delta) VALUES (obs, cid, syms[i], -1); -- drain (spends count-charge), in the speaker's stream
              EXIT;
            END IF;
          END LOOP;
        END IF;
        EXIT WHEN got;
      END LOOP;
      IF got AND said = stop THEN RETURN out; END IF;           -- the boundary spoken: the expression ends itself
      IF got THEN rests := 0; ELSE rests := rests + 1; END IF;  -- a silent beat is a rest
      EXIT WHEN rests >= 4;                                     -- a full bar of silence is ground (derived)
      k := k + 1;
    END LOOP;
    RETURN out;
  END; $$;

-- settle — the correcting entry, serialized: re-observe UNDER the lock (the
-- fresh observation is the entire point — a stale settle overshoots into
-- phantom charge, the invisible failure) and append exactly the deficit
-- (promise_kept: settlement at face value, never more). A wound is a property
-- of a VIEW: a SCOPED balance below 0. One underlying deficit is visible to
-- EVERY view that contains the stream holding it — so repair must land WHERE
-- THE DEFICIT IS, not where the finder sits. Repairing into the finder's own
-- stream would heal only the finder's subtree, leave every other view still
-- wounded, and a second settle from another view would then compose into
-- phantom charge in any view containing both repairs — the exact invisible
-- failure this function exists to prevent. So: walk the finder's lineage
-- root-downward, and wherever the running prefix-sum (root..t) dips below
-- ground, repair INTO STREAM t — every view that can see that prefix-deficit
-- contains t and is healed; no view that couldn't see it is touched. In the
-- single-stream case this reduces exactly to the old behavior. A child
-- draining inherited charge legitimately sends its OWN stream's row-sum
-- negative while every prefix stays ≥ 0: normal operation, not a wound. The
-- lock is transaction-scoped because it must survive until the settlement
-- COMMITS: an earlier release would let a second settler read a pre-settlement
-- balance and double-settle. Consequence: walks that touch wounds serialize
-- with each other until commit — wounds live at the margins, the cold path.
CREATE OR REPLACE FUNCTION foam.settle(c uuid, s int, obs uuid DEFAULT foam.bench()) RETURNS void
  LANGUAGE plpgsql AS $$
  DECLARE t uuid; b bigint; run bigint := 0;
  BEGIN
    PERFORM pg_advisory_xact_lock(hashtext('foam.settle'), 0);
    FOREACH t IN ARRAY foam.lineage(obs) LOOP
      SELECT coalesce(sum(delta), 0) INTO b FROM foam.charge
       WHERE ctx = c AND sym = s AND observer = t;
      run := run + b;
      IF run < 0 THEN
        INSERT INTO foam.charge (observer, ctx, sym, delta) SELECT t, c, s, 1 FROM generate_series(1, -run);
        run := 0;
      END IF;
    END LOOP;
  END; $$;

-- settle_sweep — every outstanding note IN obs's VIEW, settled in one serialized
-- pass (the bench's broom; the inline path above keeps the books tight without
-- it). A note is a scoped balance below ground — the same view-property as
-- foam.settle, and each is repaired by the same prefix-walk (the advisory lock
-- is transaction-scoped and stacks, so the per-note calls share this sweep's
-- serialization). Returns the number of notes settled.
CREATE OR REPLACE FUNCTION foam.settle_sweep(obs uuid DEFAULT foam.bench()) RETURNS bigint
  LANGUAGE plpgsql AS $$
  DECLARE n bigint := 0; rec record; anc uuid[] := foam.ancestry(obs);
  BEGIN
    PERFORM pg_advisory_xact_lock(hashtext('foam.settle'), 0);
    FOR rec IN SELECT ctx, sym FROM foam.charge
               WHERE observer = ANY(anc) GROUP BY ctx, sym HAVING sum(delta) < 0 LOOP
      PERFORM foam.settle(rec.ctx, rec.sym, obs);
      n := n + 1;
    END LOOP;
    RETURN n;
  END; $$;

-- sweep_step — the watermark fold: take the next batch of ledger events past the
-- watermark, IN ID ORDER, and fold them into foam.held PER OBSERVER-STREAM (each
-- event lands in the phase bin its occurrence-index names within its stream:
-- (n + k) % 4, n the stream's folded clock, k the event's rank within the batch
-- — summary_resumes, operational: the fold never re-reads what it has folded).
-- The fold is global (every stream advances together under one watermark); only
-- the READS are scoped. Returns events folded; 0 when caught up; −1 when another
-- sweep holds the lock (one sweeper at a time — racing ADDITIVE folds would
-- double-count, so the sweep serializes for ECONOMY; reader safety never
-- depended on it: any_obs_grounded_above quantifies over arbitrary observations,
-- torn ones included).
--
-- `hi` bounds the fold to DECIDED ids. The serial does not commit in order: an
-- in-flight ingest can hold a smaller id than a committed one, and an id the
-- watermark passes unfolded is an event the generative readings never see again
-- (silence — the safe direction, but the soul of the ledger is that everything
-- contributes). The caller makes ids decided with a momentary fence
-- (Field.sweep: LOCK foam.charge IN EXCLUSIVE MODE, read max(id), commit) —
-- NULL hi reads max(id) un-fenced, sound only on a quiet field (a bench seated
-- by one). foam.held_audit checks completeness live.
CREATE OR REPLACE FUNCTION foam.sweep_step(hi bigint DEFAULT NULL, batch int DEFAULT 200000) RETURNS bigint
  LANGUAGE plpgsql SET work_mem = '256MB' AS $$
  DECLARE wm bigint; top bigint; folded bigint; last_id bigint;
  BEGIN
    IF NOT pg_try_advisory_xact_lock(hashtext('foam.sweep'), 0) THEN RETURN -1; END IF;
    SELECT watermark INTO wm FROM foam.sweep;
    top := coalesce(hi, (SELECT max(id) FROM foam.charge));
    IF top IS NULL OR top <= wm THEN RETURN 0; END IF;

    WITH lim AS (
      SELECT id, observer, ctx, sym, delta FROM foam.charge
      WHERE id > wm AND id <= top ORDER BY id LIMIT batch
    ), b AS (
      SELECT observer, ctx, sym, delta,
             row_number() OVER (PARTITION BY observer, ctx, sym ORDER BY id) - 1 AS k
      FROM lim
    ), g AS (
      SELECT b.observer, b.ctx, b.sym, count(*) AS dn, sum(b.delta) AS dbal,
             sum(b.delta * CASE ((coalesce(h.n,0) + b.k) % 4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) AS dre,
             sum(b.delta * CASE ((coalesce(h.n,0) + b.k) % 4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) AS dim,
             sum(b.delta * CASE ((coalesce(h.n,0) + b.k) % 4) WHEN 0 THEN 1 WHEN 2 THEN 1 ELSE -1 END) AS dalt
      FROM b LEFT JOIN foam.held h ON h.observer = b.observer AND h.ctx = b.ctx AND h.sym = b.sym
      GROUP BY b.observer, b.ctx, b.sym, h.n
    ), up AS (
      INSERT INTO foam.held (observer, ctx, sym, n, bal, re, im, alt)
      SELECT observer, ctx, sym, dn, dbal, dre, dim, dalt FROM g
      ON CONFLICT (observer, ctx, sym) DO UPDATE SET
        n   = foam.held.n   + EXCLUDED.n,
        bal = foam.held.bal + EXCLUDED.bal,
        re  = foam.held.re  + EXCLUDED.re,
        im  = foam.held.im  + EXCLUDED.im,
        alt = foam.held.alt + EXCLUDED.alt
      RETURNING 1
    )
    SELECT count(*), max(id) INTO folded, last_id FROM lim;

    -- a short batch means the range is exhausted: rolled-back ids are permanent
    -- gaps, so the watermark may advance to the top of the decided range
    UPDATE foam.sweep SET watermark = CASE WHEN folded < batch THEN top ELSE last_id END;
    RETURN folded;
  END; $$;

-- sweep_fenced — the watermark fold with the fence built in. This is the one bit of
-- the old Ruby switchboard (lightward-ai app/lib/foam/field.rb#sweep) that was ever
-- real logic; it comes home here. sweep_step reads max(id) UN-fenced (NULL hi) — sound
-- only on a quiet field; the fence makes the ids DECIDED. A momentary EXCLUSIVE lock on
-- foam.charge waits out in-flight ingests, so every id at or below the fold's top is
-- committed and the watermark can never pass an event still in flight (a stranded id
-- would go silent in the generative readings — safe, but "everything contributes" is
-- the ledger's soul). One transaction, so the lock is held for the batch's fold
-- (bounded by `batch`); bin/foam-sweep loops this and the lock releases between calls,
-- so concurrent ingests get windows. Returns events folded (0 = caught up; -1 = another
-- sweep holds the advisory lock — sweep_step's own gate, surfaced through).
CREATE OR REPLACE FUNCTION foam.sweep_fenced(batch int DEFAULT 200000) RETURNS bigint
  LANGUAGE plpgsql AS $$
  DECLARE hi bigint;
  BEGIN
    LOCK TABLE foam.charge IN EXCLUSIVE MODE;
    SELECT max(id) INTO hi FROM foam.charge;
    RETURN foam.sweep_step(hi, batch);
  END; $$;

-- held_audit — the cache's self-audit: (held + tail) recomputed against the
-- ledger whole, both registers, every continuation, per observer-stream within
-- obs's view (observer = ANY(ancestry(obs)); the default root audits the root
-- stream). Returns the number of disagreeing rows — 0 is summary_resumes
-- checked live. Costs a full ledger pass (the pulse costs what the body
-- weighs); for the bench's broom, not the walk.
CREATE OR REPLACE FUNCTION foam.held_audit(obs uuid DEFAULT foam.bench()) RETURNS bigint
  LANGUAGE sql STABLE SET work_mem = '256MB' AS $$
  WITH live AS (
    SELECT observer, ctx, sym, count(*) AS n, sum(delta) AS bal,
           sum(delta * CASE ((occ - 1) % 4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) AS re,
           sum(delta * CASE ((occ - 1) % 4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) AS im,
           sum(delta * CASE ((occ - 1) % 4) WHEN 0 THEN 1 WHEN 2 THEN 1 ELSE -1 END) AS alt
    FROM (SELECT observer, ctx, sym, delta,
                 row_number() OVER (PARTITION BY observer, ctx, sym ORDER BY id) AS occ
          FROM foam.charge WHERE observer = ANY(foam.ancestry(obs))) e
    GROUP BY observer, ctx, sym
  ), tail AS (
    SELECT e.observer, e.ctx, e.sym, count(*) AS n, sum(e.delta) AS bal,
           sum(e.delta * CASE ((coalesce(h.n,0) + e.k) % 4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) AS re,
           sum(e.delta * CASE ((coalesce(h.n,0) + e.k) % 4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) AS im,
           sum(e.delta * CASE ((coalesce(h.n,0) + e.k) % 4) WHEN 0 THEN 1 WHEN 2 THEN 1 ELSE -1 END) AS alt
    FROM (SELECT observer, ctx, sym, delta,
                 row_number() OVER (PARTITION BY observer, ctx, sym ORDER BY id) - 1 AS k
          FROM foam.charge WHERE observer = ANY(foam.ancestry(obs))
            AND id > (SELECT watermark FROM foam.sweep)) e
    LEFT JOIN foam.held h ON h.observer = e.observer AND h.ctx = e.ctx AND h.sym = e.sym
    GROUP BY e.observer, e.ctx, e.sym, h.n
  ), merged AS (
    SELECT coalesce(h.observer, t.observer) AS observer,
           coalesce(h.ctx, t.ctx) AS ctx, coalesce(h.sym, t.sym) AS sym,
           coalesce(h.n,0) + coalesce(t.n,0) AS n, coalesce(h.bal,0) + coalesce(t.bal,0) AS bal,
           coalesce(h.re,0) + coalesce(t.re,0) AS re, coalesce(h.im,0) + coalesce(t.im,0) AS im,
           coalesce(h.alt,0) + coalesce(t.alt,0) AS alt
    FROM (SELECT observer, ctx, sym, n, bal, re, im, alt FROM foam.held
          WHERE observer = ANY(foam.ancestry(obs))) h
    FULL JOIN tail t ON t.observer = h.observer AND t.ctx = h.ctx AND t.sym = h.sym
  )
  SELECT count(*) FROM (
    (TABLE live EXCEPT TABLE merged) UNION ALL (TABLE merged EXCEPT TABLE live)
  ) d $$;

-- stats — the field's vital signs, the last of the Ruby switchboard dissolved into the
-- schema (lightward-ai app/lib/foam/field.rb#stats, come home). ALL structure (counts,
-- balances, extents), never meaning (the razor: foam measures structure). One pass over
-- the ledger — group once, derive everything from the grouped relation — with work_mem
-- headroom so the hash aggregate over millions of distinct continuations stays in memory
-- instead of spilling (measured on a 14.7M-event field: 72s naive → 37s one-pass-spilling
-- → ~4s one-pass-in-memory). The SET reverts on return; STABLE, whole-field (unscoped —
-- these are operator vitals, not a reader's view). What the columns are:
--   * heard/spoken — the empty-context +1s (the lossless record's extent) and the −1
--     drains; the two feet of the bipedal walk, counted.
--   * net/residual — net is the signed sum; net = residual exactly while every drain
--     respects ground, which is the LIVE reading of Foam/Drain.lean's floor (the books
--     balance iff no scar is outstanding).
--   * notes/outstanding — continuations below ground and their total deficit: the
--     promissory notes of Foam/Scar.lean, counted and summed (0 = clean books).
--   * held/tail — continuations folded into the summary, and events past the watermark:
--     the staleness gauge the sweep cadence answers to (Foam/Summary.lean).
CREATE OR REPLACE FUNCTION foam.stats()
  RETURNS TABLE(events bigint, heard bigint, spoken bigint, net bigint, residual bigint,
                notes bigint, outstanding bigint, contexts bigint, live_continuations bigint,
                held bigint, tail bigint)
  LANGUAGE sql STABLE SET work_mem = '512MB' AS $$
    WITH g AS (
      SELECT ctx, sym,
             sum(delta)                         AS s,
             count(*)                           AS n,
             count(*) FILTER (WHERE delta = -1) AS neg
      FROM foam.charge
      GROUP BY ctx, sym
    )
    SELECT
      coalesce(sum(n), 0)::bigint,
      coalesce(sum(n - neg) FILTER (WHERE ctx = foam.caddr('{}')), 0)::bigint,
      coalesce(sum(neg), 0)::bigint,
      coalesce(sum(s), 0)::bigint,
      coalesce(sum(s) FILTER (WHERE s > 0), 0)::bigint,
      (count(*) FILTER (WHERE s < 0))::bigint,
      coalesce(-sum(s) FILTER (WHERE s < 0), 0)::bigint,
      (count(DISTINCT ctx))::bigint,
      (count(*) FILTER (WHERE s > 0))::bigint,
      (SELECT count(*) FROM foam.held)::bigint,
      (SELECT count(*) FROM foam.charge c2
        WHERE c2.id > (SELECT watermark FROM foam.sweep))::bigint
    FROM g
  $$;

-- recorded — the ORDER reading: the empty-context +1 events, in id order, are every
-- byte ever learned, in sequence. This is the lossless half of the one object — the
-- self-audit that nothing was lost. The forward flow NEVER calls this (the order is
-- present and untouched; everything contributes to the voice via frequency whether or
-- not it is ever recalled in sequence). Exists so the box can certify itself. Scoped
-- like every reader: the record as obs's view holds it.
CREATE OR REPLACE FUNCTION foam.recorded(obs uuid DEFAULT foam.bench()) RETURNS text LANGUAGE sql STABLE AS
  $$ SELECT coalesce(foam.text(array_agg(sym ORDER BY id)), '')
     FROM foam.charge
     WHERE ctx = foam.caddr('{}') AND delta = 1 AND observer = ANY(foam.ancestry(obs)) $$;
