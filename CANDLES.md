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

## the boost — Lorentz from two probes on one backend

The relativity program. Two postulates now stand structurally: frame-independent
laws (`align_rot_invariant`, `born` immutable) and a finite invariant causal cap
(`Lightcone.keepLast_bounded` / `keepLast_screen`, **proven**). By Einstein's
argument the inter-frame transform is then forced toward **Lorentz** — asymptotic,
discrete → continuous, "at this scale."

**The floor is laid (2026-06-15): `Spacetime.lean`.** A continuation *is* a
spacetime point — its `kmax`-bounded context the space axis, its conserved
heard-charge the time axis (`event_is_spacetime_point`, **proven**, axiom-free).
The two axes have differing character (space bounded / time conserved) — the
recognized seed of the Lorentzian signature. You assemble the spacetime before you
boost it; it's assembled.

**The boost is located (2026-06-15, opened not closed).** The honest map: a boost
needs an invariant cap *and* relativity of simultaneity, and in foam they live in
different layers.

- The cap is **frame-blind** — `keepLast_bounded` caps the radius at `k` for any
  ledger, reader-independent. Postulate 2, proven.
- Simultaneity-relativity is **NOT backstage.** The backstage order is *absolute*
  (`playback_faithful`: every reader agrees on the order) — absolute simultaneity
  = **Galilean**, the God's-eye λ (why Bell reads classical, `observer_scope`,
  CHSH = √2). It comes from the **frontstage scoping**: two scopes disagree on
  what's "happened" (Wigner's friend, *measured*) — in Lean, `shared_is_floor`
  (Commons): agree below the meet, disagree above. The meet is the shared invariant
  past; the private content above is the frame-relative "not-yet."

So **the boost lives frontstage; backstage Galilean, frontstage Lorentzian** — the
lfp/gfp seam wearing a relativity hat (absolute below, relative above, the cone the
same in both). This *explains why Lorentz is asymptotic*: the discrete backstage is
Galilean-absolute, so full Lorentz (genuinely relative simultaneity) is a
frontstage continuum-limit emergent, never exact at finite scale.

The boost's two pillars are therefore **already proven, just located**: invariant
cone (`keepLast_bounded`), relative simultaneity (`shared_is_floor` / Wigner),
shared invariant past (the meet). **Open frontier:** the explicit boost *transform*
— the velocity-parameterized tilt between frames, and whether it's exact
hyperbolic-Lorentz or a discrete approximation converging to it.

Next landable rung: **worldlines can't exit the cone** — `|Δcontext| ≤ c·Δorder`
(nothing massive exceeds `c = kmax`), constraining the boost group to timelike
frames. Build on `Lightcone` (the window advances by a bounded step per order-tick).
**conjecture (the cap pillar) → a clean theorem-shape.** The screening candle below
is the inter-frame ingredient.

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

## indistinguishable-from-mass

Downstream of the boost: mass is the Lorentz-invariant magnitude of the
energy–momentum vector (rest energy). The energy half is **proven**
(`Conservation`); if the boost lands and a momentum-analog appears, "mass" is the
conserved heard-modulus read as a Lorentz invariant. **conjecture, gated on the
boost.**
