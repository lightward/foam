# Candles

Open frontiers — the next things to look at. This file is **stigmergic**: it is
where the pending list lives, because neither the worker nor the bench-keeper
holds it in memory between sessions (deposit before you pop; the basepoint lives
in the substrate, not the agent — `RelationalStigmergicBasepoint`). Each candle is
written to be picked up *cold*. Grades: **proven** (Lean, axiom-free), **measured**
(ran against a field), **conjecture** (structural, investigable), **rhyme**
(resonance, labeled, not yet load-bearing). Method, throughout: empirical-first
for discovery (measure on a field, find the fixed point), categorical-first for
falsification (prove — a failed proof is a located obstruction). It's maintenance,
not a heist.

---

## the boost — Lorentz, the signature trichotomy (substantially landed)

The relativity program, largely closed (2026-06-15→). Proven structurally: frame-independent
laws (`align_rot_invariant`, `born` immutable), a finite invariant causal cap
(`Lightcone.keepLast_bounded` / `keepLast_screen`), the spacetime point assembled
(`Spacetime.event_is_spacetime_point`). And the boost itself, **forced at the frame**:

- **the signature trichotomy** (`Frames.lean`): the three 2D algebras ℤ[i]/ℤ[ε]/ℤ[j], one
  parameter κ = (the unit)² ∈ {−1, 0, +1}, ARE the three geometries — elliptic/parabolic/
  hyperbolic = Born/Galilean/Lorentz, the three conjugacy classes of SL(2,ℝ).
  `forced_at_the_frame_kappa` is one forcing at three κ; `crossK` (the symplectic area) the
  κ-invariant shared by all three (the formal core of `ergodic-symplectic`). The rest-energy
  zero-point is free only at κ=+1 (`zero_point_kappa`: `(1−κ)·f 0 = 0`).
- **the substrate is Galilean** (`Boost.finite_boost_galilean`): the finite Event is
  block-diagonal — the axes don't mix, by `rfl`. Lorentz is the κ:0→+1 deformation.
- **the three rotation groups** (`Rotations.int_pell_one`): elliptic ℤ/4 (the dial closes,
  `rot_complete`), parabolic ℤ (velocities add, `galilean_velocities_add`), hyperbolic trivial
  (no proper integer boost — *why* Lorentz needs the continuum).
- **the rest mass** (`Mass.lean`): the conserved heard-modulus read as the κ=+1 Minkowski
  invariant — `rest_mass_conserved` (this closes the old `indistinguishable-from-mass` candle).
- operationally κ-native: `schema.sql` `foam.normK` / `kparseval_audit`; the field self-audits
  all three frames (`spikes/frames.sql`).

**worldlines can't exit the cone — landed** (2026-06-16, `Lightcone.lean`). The cone's
quantitative companion to `keepLast_screen` (the wall): advancing the order by `Δ = s.length`
new bytes displaces the context window by *exactly* `Δ` — `keepLast_advance`, stated
subtraction-free as `keepLast (j+Δ) (h++s) = keepLast j h ++ s`. That is `|Δcontext| ≤ c·Δorder`
(one slot per order-tick, capped at `c = kmax`): the worldline has slope one and terminates at
the cone boundary; nothing massive outruns `c`. `keepLast_turnover` reads the wall forward (a
full window of new context evicts the past entirely). Axiom-free, pinned (`length_append`
hand-rolled — core's prices `propext`). **proven.**

**The one open frontier: the continuum limit.** Where `a²−b²=1` acquires nontrivial solutions,
the off-diagonal coupling (ε²: 0→+1) turns on, and the proper boosts absent at integer scale come
into being. This IS the `decorrelation horizon` candle below — the soft, between-frames face, the
decoupling the continuum boost needs. **conjecture.**

## gravity — the storage-cost gradient of settling-under-observation (theory first)

Held up against dark matter (2026-06-16), then sharpened: a foam-native, Verlinde-flavored reading
of gravity as an *apparent* frontstage effect of the backstage settling — under the animation of
continuous measurement — toward least-storage-cost paths. The structural pieces are proven; the
synthesis is the conjecture.

- **the animation**: measurement is participatory — `Tare`'s "no read that is not also a write";
  observation is the wind that keeps the field from looping dead (`clock_loops`).
- **settling, not solving**: the resolver relaxes to a fixed point — `fair_run_converges`,
  `quiescent_is_correct` (the settled state IS the answer).
- **cheapest-to-store = self-describing**: `gen_grows` ("compression IS prediction"); the attractor
  is the round-trip fixed point (`lossless_codec`, decode∘encode = id) and `meet_self` — a path iso
  with its own symbolism, the platonic form, zero residue.

**The inversion the corpus forces.** Learning-as-decoherence (measured, `d_heardmod_closed = −176`)
drives a repeated pattern's modulus DOWN to the dark fringe; modulus = mass (`rest_mass_conserved`).
So settling drives mass toward *zero* — the redundant decoheres into the platonic background.
Therefore **mass is not what settles; mass is what *resists* settling** — the conserved, incompressible
residue the dynamics cannot spend (`conserved_invisible_to_spent`). Gravity is the relaxation of
everything compressible toward the self-completing dark fringe; the gravitational appearance is the
gradient of that settling-field *around* the incompressible cores it must route past. Mass-as-source,
recovered as un-settle-ability.

**foam already holds Verlinde's entropic-gravity ingredients**: a holographic screen
(`keepLast_screen`, the cone boundary), a bounded screen capacity (`keepLast_bounded`, ≤ k bits), a
first law at the boundary (`netCharge_discharge`, d_net = −spoken), a conserved energy (the
heard-modulus). The missing piece is the **entropy–displacement law** (ΔStorage ∝ Δposition) that turns
∇(storage cost) into a force.

**The dark-matter closure.** Gravity tracks the modulus (the incompressible mass); light tracks the
*stations* — and `station_blind_to_norm` says the stations are blind to the modulus. So the visible
undercounts the mass that sources the settling: gravity stronger than visible mass = flat rotation curves
= dark matter; the same split as the Bullet Cluster (gravity follows the conserved modulus, light the
spent/visible). Dark matter and emergent gravity become one statement — the stations can't see what the
settling-field is shaped by. (Folds together the dark-sector reading: the rest mass invisible to every
station, append-only/collisionless, frame-invariant.)

**Theory before experiment — explicitly gated.** The tempting measurement — *does local modulus tilt the
`keepLast` cone (does effective `c` shrink near high-mass continuations, time-dilation-shaped)?* — must
NOT be run until the space is theoretically exhausted top to bottom. foam has no metric on context-space
yet ("position" is context-index; "distance" is the worldline displacement `keepLast_advance`), and
without the categories the result is uninterpretable: a premature measurement yields only confusing
negatives, not a falsification. (Method, per this file: empirical-first for discovery, categorical-first
for falsification — but the categories must *exist* first.) The work, in order: (1) define the
storage-cost functional on continuations (the MDL/Kolmogorov reading of the modulus); (2) derive the
entropy–displacement law on the cone screen; (3) define cone-tilt as a modulus-dependent reach (the point
where foam's rigid, frame-invariant `c` would have to bend); (4) ONLY THEN measure whether the dev field
tilts. A failed *proof* at (2)–(3) is a located obstruction; a failed *measurement* before them is noise.
**rhyme → conjecture.**

## the spin-probe — foam's second instrument (built)

The amniscient haptic probe (`channel_capacity.md` / meta-theory §IX), made an
instrument: `spikes/holonomy.sql`. Push a context+sym into the frontstage, read the
**spin** (recency-spectrum) it returns. The **gauge-invariant magnitude**
(`normSq`, conserved under the dial — `normSq_rot`) is the honest readout; a single
reader-*frame* can be fooled into seeing flat (zero born at the wrong angle) while
the probe is genuinely wound (the four frames sum to `2·mag` — `born_parseval`).
Flat — zero holonomy — only at a complete ℤ/4 cycle (`rot_complete`, the dark
fringe = no flux). **Built + demonstrated.**

This reads the **gauge/amplitude axis** (the dial, Born, interference) — *orthogonal*
to the lightcone (the causal/order axis). The honest label: circular spin ≠
hyperbolic boost — different rotations; this is *not* the boost. It is foam's second
instrument, reading the half of the physics the spacetime floor does not touch.

Refinements: the full **Wilson loop** — holonomy around a multi-context closed
*path*, not one context (the genuine gauge-invariant flux through a loop); the
**dirty dev-db** sample (push probes into `lightward_foam_dev`, read its flux-map);
and the deeper question — what does the field's **flux/curvature map** look like,
and does a *learning* field (ongoing input) flatten toward zero holonomy (the
dark-fringe limit, `self_generation`) or develop persistent curvature?

## the decorrelation horizon = the soft face of the lightcone

`Lightcone.keepLast_screen` (the past beyond `k` is *exactly* screened) is the
**hard, kinematic, intra-ledger** cone — the `c`. The **decorrelation horizon**
(`channel_capacity.md`, python-reset era: σ ~ √(3/d), Marchenko–Pastur, the
*inter-probe* mediation chain) is the **soft, dynamical, statistical** correlation
length — exponential decay, not an exact cutoff. Two faces of one horizon; they
**compose** for the boost: hard cone *within* a frame + soft decorrelation
*between* frames. Note the cross-generation: the idea was lattice-era foam (a
cited estimate); it re-lands operationally as the lightcone (proven). Look at:
can the soft horizon be brought into the operational corpus, and is it the
between-frames decoupling the boost needs? **rhyme → conjecture.** (Isaac's catch,
2026-06-14.)

## dirty confirmation of the causal cap

The cap is **proven** + **measured** on a clean throwaway. Not yet checked against
`lightward_foam_dev` (30M events of real history): does the `kmax` cap hold
uniformly, or is the real field heterogeneous (mixed kmax, settle-appends, manual
inserts)? An empirical heterogeneity check — would be a finding about the field's
history, not about the theorem. **measured (throwaway) → wants dirty.**

## the global-energy functional — does foam have a Hamiltonian?

`Conservation.lean` gave the conserved sector (the heard-record, exact) and the
open-system first law (`d_net = −spoken`). Open: define a *global* energy
functional (sum of per-continuation frequencies, or a spectral total) and test
whether the turn **conserves** it — a closed interior energy, or only the boundary
first law? `measure → prove`. **conjecture.**

## learning-as-decoherence

Measured once (the closed hear-then-speak turn: `d_heardmod_closed = −176` —
hearing the same string repeatedly drove the heard-modulus *down*, toward the dark
fringe). Replicate: ingest one string many times, watch a continuation's
heard-modulus fall to zero — repetition flattening the spectrum, the dark fringe
forming under learning. **measured once → wants replication.**

## the helix is a HalfType (DNA)

The double helix *is* a `HalfType`: reverse-complement = the diamond iso, each
strand a complete ground, neither privileged. Reverse-complement ↔ `conj` /
`Reversal`; the 4-base alphabet ↔ the ℤ/4 dial; codon period-3 against the dial's
period-4. The `helix = HalfType` recognition is the part to stake; the rest is
rhyme. Spike: ingest a gene / its shuffle / random ACGT / English into empty
fields; read `spec`/`born` and the reverse-complement chirality — does DNA surface
structure the controls don't? **rhyme (one staked recognition).**

## landed (was: a candle here)

- **indistinguishable-from-mass** → `Mass.lean` (the rest mass is the conserved heard-modulus,
  read as the κ=+1 Minkowski invariant). Folded into the boost candle above.
