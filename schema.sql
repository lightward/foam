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

-- ── the SEAT half ─────────────────────────────────────────────────────────────
-- A seam runs through this file: two products fused. The observer tree below
-- (descend/ancestry/meet/settle — Foam/Seat/*.lean, Foam/Scar.lean) is
-- actor-shaped: seats, inheritance, settlement — proto-Counter's runtime,
-- already in production wearing the byte-field's clothes (counter/README.md).
-- The charge half further down (ingest/held/sweep/speak — Foam/Engine/*.lean)
-- is byte-shaped: the listening instrument. When Counter's graph-ledger
-- inhabitant arrives, this half is its ancestry. The boundary is drawn here so
-- the fusion reads as a choice held, not a distinction missed.
--
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
-- UNBOUNDED by depth: a scar settles however deep it sits, and Foam/Scar.lean's promise_kept
-- knows no cap — so neither does this. A degenerate CYCLE terminates by a visited-set, not a
-- magic number (descend only ever seats a child of an existing node, so the tree is acyclic
-- by construction; the guard is for malformed data, and it halts at the repeat — the only
-- honest place to halt). The old `depth < 64` was a smuggled choice; nothing here is a choice.
CREATE OR REPLACE FUNCTION foam.lineage(o uuid) RETURNS uuid[] LANGUAGE sql STABLE AS $$
  WITH RECURSIVE chain(id, parent, depth, seen) AS (
    SELECT o, (SELECT parent FROM foam.observer WHERE id = o), 0, ARRAY[o]
    UNION ALL
    SELECT ob.id, ob.parent, chain.depth + 1, chain.seen || ob.id
    FROM chain JOIN foam.observer ob ON ob.id = chain.parent
    WHERE NOT ob.id = ANY(chain.seen)
  )
  SELECT array_agg(id ORDER BY depth DESC) FROM chain
$$;

-- meet — the deepest common ancestor of two observers: the floor they share (Foam/Seat/
-- Meet.lean: shared_is_floor — the meet is the greatest lower bound; meet_below_left/right —
-- Below both). The convergence-complement of descend: descend DIVERGES the tree (a fresh
-- leaf, the seam, no return), meet RECONVERGES it — what two seats hold in common, the scope
-- both inherit. Two siblings meet at their parent; any two observers meet at least at the
-- root (the wind, Below all — root_below_all). The deepest node on both root-first lineages.
CREATE OR REPLACE FUNCTION foam.meet(a uuid, b uuid) RETURNS uuid LANGUAGE sql STABLE AS $$
  WITH la AS (SELECT id, ord FROM unnest(foam.lineage(a)) WITH ORDINALITY AS t(id, ord)),
       lb AS (SELECT id FROM unnest(foam.lineage(b)) AS t(id))
  SELECT la.id FROM la JOIN lb USING (id) ORDER BY la.ord DESC LIMIT 1
$$;

-- grade — how related two observers are: the length of their shared path from root (Foam/
-- Seat/Meet.lean: grade = (meet a b).length). Root alone ⇒ grade 1 (only the wind in common);
-- deeper ⇒ more shared fold. The rank of their kinship — the count of ancestors they both own.
CREATE OR REPLACE FUNCTION foam.grade(a uuid, b uuid) RETURNS int LANGUAGE sql STABLE AS $$
  SELECT count(*)::int FROM (
    SELECT id FROM unnest(foam.lineage(a)) AS t(id)
    INTERSECT
    SELECT id FROM unnest(foam.lineage(b)) AS t(id)
  ) shared
$$;

-- descend — the seating verb the observer tree implied and never had: open a fresh seat
-- under `parent`. Identity is gen_random_uuid (the wind — obtained, not chosen). The
-- heir's ancestry runs up THROUGH parent (foam.ancestry, Below — Foam/Seat/Meet.lean),
-- so it inherits parent's whole fold (Foam/Seat/Descend.lean: heir_covers_ancestor); its
-- own stream starts empty and ancestry never runs down, so its spending drains into
-- itself and parent stays pristine (ancestor_blind_to_heir); and it reads its own address,
-- which parent cannot (heir_sees_itself). Two faces: on what is OBSERVED the seating is an
-- equivalence (parent sees nothing of the excursion — ancestor_blind_to_heir); on what is
-- REACHED it is a seam (the heir reaches where parent could not, heir_reach_is_new, with no
-- way back, heir_reach_no_return) — invisible above, irreversible below, the measurement
-- shape (Foam/Seat/Rendezvous.lean). "Speak from the heir" is just foam.speak(…, obs =>
-- heir) — speak was always observer-parametric. Descend seats; it does not fetch a guest —
-- the escape from a stall is never the stalled seat's own move (bin/foam-repl).
CREATE OR REPLACE FUNCTION foam.descend(parent uuid DEFAULT foam.root()) RETURNS uuid
  LANGUAGE sql AS
  $$ INSERT INTO foam.observer (id, parent) VALUES (gen_random_uuid(), parent)
     RETURNING id $$;

-- the ledger: ctx content-addresses a continuation, sym the byte that followed, delta ±1
-- (+1 learned, −1 drained); the bigserial id is the order — the lossless half (Foam/Ledger.lean).
CREATE TABLE IF NOT EXISTS foam.charge (
  id       bigserial PRIMARY KEY,
  observer uuid NOT NULL
    CHECK (observer <> '00000000-0000-0000-0000-000000000000'),
  source   uuid NOT NULL DEFAULT '00000000-0000-0000-0000-000000000000',
  ctx      uuid NOT NULL,
  sym      int  NOT NULL,
  delta    int  NOT NULL
);
-- source — WHO this event came from: the input signature (Foam/Seat/Signed.lean: sign /
-- speaker_recoverable — every event carries its speaker; the voice is still recoverable by
-- dropping it, voice_survives_signing). The default is the WIND: the zero uuid = foam.root()
-- = the anonymous, information-free, universal source (wind_below_all — Below every source;
-- only_wind_is_floor — the unique floor). Attribution lives in the RECORD, never folded into
-- foam.held: source is the order layer, droppable from the freq summary (Foam/Ledger.lean:
-- order_finer), so the readers and the fold are untouched. A +1's source is its speaker; a
-- −1 drain keeps the default (the wind — sampled by hw_random, the ∀ parameter). source =
-- observer is the self-mirror (the closed loop, bin/foam-repl's forbidden self-fetch) —
-- recorded and detectable, never silently merged. An event with no named speaker is heard
-- from the wind; foam.healthcheck confirms the column is present.
CREATE INDEX IF NOT EXISTS foam_charge_ctx ON foam.charge (observer, ctx, sym);
-- tail index: HELD + TAIL folds events past the watermark (Foam/Engine/Summary.lean); INCLUDE keeps it index-only.
CREATE INDEX IF NOT EXISTS foam_charge_ctx_id ON foam.charge (ctx, id) INCLUDE (observer, sym, delta);

-- foam.held — the resumable fold, cached per continuation per observer-stream: the
-- four-character dial of ℤ/4 (Foam/Seat/Characters.lean) — bal at +1, re/im at i, alt at −1,
-- plus n the phase clock. Exact as HELD + TAIL (Foam/Engine/Summary.lean: summary_resumes); a derived
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

-- the watermark: at-or-below is folded into foam.held, past it is the tail folded live (Foam/Engine/Summary.lean).
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
-- boundaries; the empty-context events land in id order — the lossless record, written never
-- read here. `from_source` SIGNS the input — WHO is being heard (Foam/Seat/Signed.lean:
-- sign, speaker_recoverable) — and defaults to the wind (the zero uuid = foam.root()), so a
-- caller naming no speaker is heard "from the wind," honestly. One name per ORIGINAL voice
-- is the caller's to keep (sign_faithful): wind-named heirs (foam.descend — gen_random_uuid)
-- never alias; reusing a name to merge two distinct voices is the move foam forbids, and the
-- merge is unrecoverable (no section).
CREATE OR REPLACE FUNCTION foam.ingest_step(carry int[], bytes int[], kmax int DEFAULT 7,
                                            obs uuid DEFAULT foam.bench(),
                                            from_source uuid DEFAULT foam.root()) RETURNS int[]
  LANGUAGE plpgsql AS $$
  DECLARE all_b int[] := coalesce(carry,'{}') || coalesce(bytes,'{}');
          start_i int := coalesce(array_length(carry,1),0) + 1;
          n int := coalesce(array_length(all_b,1),0);
  BEGIN
    -- one INSERT per chunk; ORDER BY position so serial id-order is the lossless record.
    INSERT INTO foam.charge (observer, source, ctx, sym, delta)
    SELECT obs, from_source,
           foam.caddr(CASE WHEN j = 0 THEN '{}'::int[] ELSE all_b[i-j : i-1] END), all_b[i], 1
    FROM generate_series(start_i, n) AS i
    CROSS JOIN LATERAL generate_series(0, least(kmax, i - 1)) AS j
    ORDER BY i, j;
    RETURN all_b[greatest(n - kmax + 1, 1) : n];
  END; $$;

-- depth — the gate signal: the longest charged context for `seed`, read HELD + TAIL
-- (Foam/Engine/Summary.lean) and summed over the visible streams (ancestry = Below). Structure, never meaning.
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

-- born_kappa — the voice weight at signature κ. A sampler must be non-negative (born_nonneg),
-- so the live voice is κ=−1 (elliptic, re²+im² — the unique positive-definite norm). κ=0
-- parabolic (phase-blind) and κ=+1 hyperbolic (not a voice — basis-inconsistent) are kept
-- audible, never used live (Foam/Seat/Signature.lean). kappa=−1 (default) is the live voice.
CREATE OR REPLACE FUNCTION foam.born_kappa(kappa int, tk int, re bigint, im bigint) RETURNS bigint
  LANGUAGE sql IMMUTABLE AS $$
    SELECT CASE kappa
      WHEN -1 THEN foam.born(tk, re, im)
      WHEN  0 THEN re * re
      ELSE greatest(re * re - im * im, 0)
    END
  $$;

-- born_audit — the law self-audited over a fixed integer grid (∀, consults no population):
-- align's anchor + quarter-turn recurrence (which pin it uniquely), born_parseval (the four
-- stations sum to 2(re²+im²)), born_nonneg. Returns violations; 0 is Born checked live (Foam/Engine/Spectrum.lean).
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

-- kparseval_audit — born_audit generalized off the elliptic corner: the κ-Parseval identity
-- (ac−κbd)² − κ(ad−bc)² = (a²−κb²)(c²−κd²) over a grid (Foam/Seat/Signature.lean); ad−bc is the
-- κ-invariant symplectic area. born_audit() = kparseval_audit(−1) = 0; certifies any frame.
CREATE OR REPLACE FUNCTION foam.kparseval_audit(kappa bigint) RETURNS bigint
  LANGUAGE sql STABLE AS $$
    SELECT count(*)
    FROM generate_series(-4, 4) a CROSS JOIN generate_series(-4, 4) b
         CROSS JOIN generate_series(-4, 4) c CROSS JOIN generate_series(-4, 4) d
    WHERE (a * c - kappa * (b * d)) * (a * c - kappa * (b * d))
            - kappa * ((a * d - b * c) * (a * d - b * c))
          <> (a * a - kappa * (b * b)) * (c * c - kappa * (d * d))
  $$;

-- speak — the DISCHARGE: the field speaks only through recurrence. Back off to the longest
-- charged context, read HELD + TAIL (Foam/Engine/Summary.lean: summary_resumes, exact), weight each
-- continuation by the Born measurement (align tk)² (Foam/Engine/Spectrum.lean: spec_shift, the recency
-- pairing; basis-consistent, born_parseval; uniform recurrence cancels), sample by weight (never
-- argmax), emit, drain −1 (Foam/Engine/Drain.lean: a per-step floor, so every prefix is a legal drain).
-- The clock turns a quarter per beat; a full bar of rests is ground (bar_invisible — derived, not chosen).
-- Reads across the visible streams (ancestry = Below), drains into obs's own stream. Full draining needs
-- new wind — a closed field loops, un-sayable; it comes home only through company. Drains race and scar;
-- settlements serialize (Foam/Scar.lean, Foam/Maintenance.lean). `stop` returns at the boundary byte;
-- the voice is bytes, not text (rendering is the edge's concern).
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
        -- The spectrum is STORED abs-framed (phase 0 = oldest) and READ recency-
        -- framed (phase 0 = newest): the per-stream conversion is specR_bridge
        -- (Foam/Engine/Chirality.lean), summed across visible streams (per-stream,
        -- never a cross-stream rotation — specR_bridge is per-Nᵢ), then squared
        -- against the walk's clock tk by the Born weight (foam.born).
        SELECT coalesce(sum(z.w) FILTER (WHERE z.bal > 0 AND z.w > 0), 0),
               coalesce(array_agg(z.sym ORDER BY z.w DESC) FILTER (WHERE z.bal > 0 AND z.w > 0), '{}'),
               coalesce(array_agg(z.w   ORDER BY z.w DESC) FILTER (WHERE z.bal > 0 AND z.w > 0), '{}'),
               coalesce(array_agg(z.sym) FILTER (WHERE z.bal < 0), '{}')
          INTO tot, syms, ws, wounded
          FROM (
            -- pair the recency (rre, rim) against the walk's clock tk — the
            -- squared pairing |⟨tk|recency⟩|², by its NAME: foam.born, the law
            -- held in one place and audited against its own theorems
            -- (foam.born_audit; Foam/Seat/Born.lean born_parseval makes it
            -- basis-consistent; uniqueness unclaimed).
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

-- settle — the correcting entry, serialized under an advisory xact-lock: re-observe fresh,
-- walk the lineage root-down, and where the running prefix-sum dips below ground repair INTO
-- that stream (the deficit's view, not the finder's). Face value, never more (Foam/Scar.lean:
-- promise_kept); a stale settle would overshoot into invisible phantom charge, so it holds the
-- lock to commit — wounds live at the margins, the cold path (Foam/Maintenance.lean).
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

-- settle_sweep — every outstanding note in obs's view, one serialized pass (the broom; the
-- inline settle in foam.speak keeps the books tight without it). A note is a scoped balance
-- below ground; same prefix-walk as foam.settle, lock stacks (Foam/Scar.lean). Returns notes settled.
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

-- sweep_step — the watermark fold: fold the next batch of past-watermark events into foam.held
-- per stream, in id-order, each into phase bin (n+k)%4 (Foam/Engine/Summary.lean: summary_resumes,
-- never re-reads what it folded). Returns events folded; 0 caught up; −1 if another sweep holds the
-- lock (serialized for economy — reader safety never depended on it: Foam/Maintenance.lean's
-- any_obs_grounded_above holds for arbitrary, torn observations). `hi` bounds to decided ids (the
-- caller's momentary fence); NULL reads max(id) un-fenced, sound on a quiet field. foam.held_audit checks live.
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

-- healthcheck — the schema's internal integrity, scanned live: the file declares the target
-- shape and keeps no migration history, so a runtime scan is the only honest record of drift
-- (like born_audit / held_audit, the receipt is live). Each row is one violation; empty is
-- healthy, and foam-sweep surfaces the count. Checks:
--   · one implementation per foam name — a signature changed by CREATE OR REPLACE widens into
--     a second overload instead of replacing, and a call matching both errors ambiguously and
--     can go mute, the error swallowed as silence;
--   · foam.charge carries its source column — the input signature (Foam/Seat/Signed.lean); a
--     field declared before it would silently drop attribution.
CREATE OR REPLACE FUNCTION foam.healthcheck() RETURNS TABLE(issue text) LANGUAGE sql STABLE AS $$
  SELECT 'overloaded: foam.' || p.proname || ' — ' || count(*) || ' implementations; DROP the stale signature'
  FROM pg_proc p JOIN pg_namespace n ON n.oid = p.pronamespace
  WHERE n.nspname = 'foam'
  GROUP BY p.proname HAVING count(*) > 1
  UNION ALL
  SELECT 'foam.charge is missing its source column (the input signature)'
  WHERE NOT EXISTS (
    SELECT 1 FROM information_schema.columns
    WHERE table_schema = 'foam' AND table_name = 'charge' AND column_name = 'source'
  )
$$;

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
--     respects ground, which is the LIVE reading of Foam/Engine/Drain.lean's floor (the books
--     balance iff no scar is outstanding).
--   * notes/outstanding — continuations below ground and their total deficit: the
--     promissory notes of Foam/Scar.lean, counted and summed (0 = clean books).
--   * held/tail — continuations folded into the summary, and events past the watermark:
--     the staleness gauge the sweep cadence answers to (Foam/Engine/Summary.lean).
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

-- recorded — the ORDER reading (Foam/Ledger.lean: order, order_finer): the empty-
-- context +1 events in id order are every byte learned, in sequence — the lossless
-- half, never read by the forward flow, present so the box can self-certify. Scoped
-- like every reader.
CREATE OR REPLACE FUNCTION foam.recorded(obs uuid DEFAULT foam.bench()) RETURNS text LANGUAGE sql STABLE AS
  $$ SELECT coalesce(foam.text(array_agg(sym ORDER BY id)), '')
     FROM foam.charge
     WHERE ctx = foam.caddr('{}') AND delta = 1 AND observer = ANY(foam.ancestry(obs)) $$;
