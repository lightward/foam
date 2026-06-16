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

**Step (1) was worked, and it forced *two* corrections (2026-06-16) — the second undoing the
first.** Draft one: *storage cost = the modulus = mass*. The modulus fails as a cost — it is
**non-monotone in compressibility** (the period-4 comb `⟨3,0⟩` reads modulus **9** yet is trivially
compressible; the complete cycle `[s,s,s,s]` reads **0**, equally compressible), and it is *frame-specific*
(`normK_frame_dependent`: `⟨1,1⟩` reads `2` elliptic, `0` hyperbolic). Draft two over-corrected —
relocating storage cost to the symplectic `crossK` because that one is κ-free. **That threw out the baby:
platonic complexity is frame-invariant in its own right (Kolmogorov's invariance theorem), and the
resonance I read as a bug is a knot-theoretic signal.** The corrected picture:

**The ledger is a polynomial; the readings are evaluations.** The occurrence comb is `P(t) = Σ tᵈ` over
the depths `d` where `s` fires. foam's four characters (`Noether`) are `P` at the four 4th-roots of unity
— count `P(1)`, alt `P(−1)`, spectrum `P(i)`, conjugate `P(−i)` — the mod-4 DFT. The **order rung**
(lossless) is the whole polynomial `P`; the modulus is **one point on the unit circle**, `|P(i)|²`.

**Storage cost = the Mahler measure of `P`**, `m(P) = exp ∮ log|P(e^{2πiθ})| dθ` — the *whole-circle*
integral, frame-invariant (a property of the polynomial, machine/κ-independent — Kolmogorov-invariance in
the analytic register). The modulus `|P(i)|²` is a *single point* of that circle; mistaking the point for
the integral was draft one's error, and mistaking "the modulus is frame-specific" for "the cost isn't a
complexity" was draft two's. **Mass/energy** is the κ-metric reading (`normK_frame_dependent`,
frame-specific) — another single-point reading, not the cost.

**Platonic = cyclotomic = self-completing = cheapest (Kronecker's theorem).** A monic integer polynomial
has `m(P) = 1` (zero entropy, cheapest) **iff** it is a product of cyclotomics — iff all its roots are
roots of unity — iff it is built of complete cycles, *self-completing*. The rigorous form of "platonic
ideals are cheapest to store" and the trailer's "recordings decay entropically if they're not
self-completing": not-self-completing = a root off the unit circle = `m(P) > 1` = positive entropy = decay.
Lehmer's problem (is there a gap above 1?) is exactly "how cheap can non-platonic structure get."

**Resonance with periodicity is the knot signal, not a bug.** `P(ζₙ)` at a root of unity detects n-fold
periodicity — in knot theory the Alexander polynomial at `ζₙ` gives the order of the n-fold cyclic
branched cover's homology (Murasugi). So `P(i)` (the modulus) is the periodicity-resonance at the dial's
own order 4; the dark fringe (`P(i) = 0`) is `i` being a root — a cyclotomic factor present, the ℤ/4 cycle
closed. The modulus is a frame-specific periodicity-detector that *assembles with the other evaluations
into* the frame-invariant `m(P)` — a coordinate of the platonic complexity, not its rival. (The
metric/symplectic `align`/`cross` are the real/imag of *one* such evaluation — `conjMul_eq` — not the cost.
`crossK` stays what it is: the symplectic area / action, the `ergodic-symplectic` universal.)

**Dark matter, re-corrected.** Gravity sources from the frame-invariant complexity `m(P)` (the whole
circle); the born-voice samples a single metric point (`born = align²`, the `|P(i)|²`-grade reading) and is
blind to the rest of the circle. The visible undercounts the source: flat rotation curves, the Bullet
Cluster split (gravity follows `m(P)`, light follows the one point). Not "blind to the modulus" — *blind to
all of the circle but the point it samples.*

**Theory before experiment — still gated.** Updated work order: **(1) storage cost identified — `m(P)`,
the Mahler measure of the ledger-polynomial: frame-invariant, platonic-iff-cyclotomic (Kronecker), the
resonances its root-of-unity coordinates (knot periodicity). Residual: foam reads `P` only at the four
4th-roots (the `Noether` characters) — the full circle is the already-flagged `Spectrum` frontier ("the
other evaluation points as one parameterized family with its character theory").** (2) the
entropy–displacement law for `m(P)` on the cone screen; (3) cone-tilt as an `m(P)`-density-dependent reach
(where foam's rigid `c` would bend); (4) ONLY THEN measure. A failed *proof* at (2)–(3) is a located
obstruction; a *measurement* before them is noise. (Method: categorical-first for falsification — the
categories must exist first.) **rhyme → conjecture (step 1 corrected twice — the symplectic overreach
undone; Mahler / Kronecker / knot-periodicity, frame-invariant).**

## the engine's gearing — the spiral, golden non-resonance, gravity-as-pitch (continuum)

The continuum organs of the gravity candle, surfaced in the relativity-program thread (2026-06-16)
and gated together (φ is irrational — the same frontier as the Lorentz boost, `int_pell_one`).
`Foam/Spiral.lean` named the genus — recursive holonomy = `evalAt step` — and witnessed the integer
spiral species (×⟨1,1⟩, growth √2, `spiral_step_grows`); what follows are its continuum properties.

- **the crankshaft — `exp`/`log` as the backstage/frontstage rivet.** The log spiral is `exp` of a
  straight line on a cylinder: a slice ⊥ the fiber is a circle (the dial, at every depth), the fiber
  is the vacuum `exp` never reaches (the puncture = `forever_escapes`), the spiral is the helix
  threading the circles. So the README crux — "backstage arithmetic, frontstage kinematic" — *is*
  `log`/`exp`: backstage = the **additive** ledger (`gen_length`, linear, the cylinder axis);
  frontstage = the **multiplicative** spiral (`r = e^u`, geometric). Linear-in-the-ledger =
  geometric-in-the-experience; the backstage is arithmetic *because* it is the log of the kinematic
  frontstage. Same `exp` as rapidity→velocity — the Lorentzian "continuum limit" the crux names.
- **the golden gearing — why the engine runs.** Among growing steps, φ is the gear-ratio that
  **never resonates**: most-irrational ⟹ the last invariant torus to break (KAM / Aubry–Mather), the
  most robust quasiperiodicity, no mode-lock. The golden gearing never stalls — and *that is the
  animation.* `clock_loops` (windless → eventually periodic → locked → dead, lfp) vs `forever_escapes`
  (the wind → never locks → alive, gfp): the difference is the gearing, and the maximally-alive one is
  golden. φ keeps the engine (foam's founding word) from becoming a clock; the wind that never lets the
  state lock is the golden wind.
- **φ in three roles — the third is the animation.** radial/Pisot (storage growth, `m(x²−x−1)=φ`, the
  smallest Pisot, the lightest mass) · angular/golden-angle (packing, the most-irrational rotation,
  phyllotaxis) · **gear-ratio** (the crankshaft converting radial↔angular, the non-resonant one that
  runs). Not one optimization, not two coincidental — a *conversion between two*, geared by φ; the
  third thing rotates between the optima like engine pistons.
- **φ as the tare.** Most-irrational = never aliases under rescaling = the scale-immune ur-unit = the
  founding tare (`Tare`, three-body.md: "the only thing you can agree on is the tare"). The founding
  word and the engine-gearing are the same number.
- **gravity = the un-flattenable pitch.** The now-surface gauge (`now_surface_invariant`) flattens any
  single instant — the 90° radius ⊥ the fiber, `finite_boost_galilean` block-diagonal, flat space per
  slice — but cannot flatten the *pitch* (the across-slice tilt, the φ-growth). Gravity is precisely
  the residual the now-surface gauge cannot remove: the curvature that survives straightening every
  instant. The reachable theorem-shape — the pitch is invariant under the now-surface gauge the way
  flatness is *within* it.
- **Ulam, parked.** The square (period-4, rational, lattice) spiral is the resonant *opposite* of the
  golden; its prime diagonals are mode-locks (the `n²+n+41` quadratics). Characterized by contrast:
  the resonant pole of the axis φ is the non-resonant pole of.

Solid: φ = smallest Pisot; golden angle = optimal packing; golden mean = most robust against resonance
(KAM). Reading: that this gearing *is* `exp`/`log` / foam's engine, and locked-vs-golden *is*
`clock_loops`-vs-`forever_escapes`. Continuum throughout — gated, the boost's sibling. The next
integer-buildable rung is the platonic predicate (cyclotomic / `m=1`, decidable over ℤ), named in
`Foam/Spiral.lean`. **rhyme → conjecture.**

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
