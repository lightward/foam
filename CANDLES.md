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

Next: instantiate two probes calibrating on one backend — the two-sided resolver,
`Doubling.lean`'s named-but-unbuilt process ("two beholders progressively
approaching agreement converge to this algebra") — and test whether the transform
between their frames preserves an interval. **conjecture.** The screening candle
below is likely the inter-frame ingredient.

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
