### the trichotomy

**Solèr's theorem narrows the bridge.** the FTPG axiom (Bridge.lean) gives `L ≅ Sub(D, V)` for some division ring D. as flagged in `ground.md`, the move from "some D" to "D = ℝ" via stabilization alone is sufficiency, not necessity. Solèr's theorem (Solèr 1995; Holland 1995, Bull AMS) closes most of that gap:

> let H be an infinite-dimensional orthomodular space over a *-division ring D containing an infinite orthonormal sequence. then D ∈ {ℝ, ℂ, ℍ}, and the form is a positive-definite Hermitian inner product.

at the foam's loop fixed point, L's structure satisfies Solèr's hypotheses (with caveats below), so D is forced into the trichotomy. the stabilization contract then picks ℝ from the three. the bug ("D = ℝ is sufficiency, not necessity") is closed up to a much smaller residue: trichotomy-narrowing depends on Solèr's hypotheses being discharged from foam structure, and contract-narrowing depends on stabilization picking ℝ from three rather than picking ℝ from any division ring.

**discharging Solèr's hypotheses from the foam's structure.** three hypotheses, each carries cost:

1. **orthomodular**: the foam's lattice is CML pre-bridge. orthomodularity (every closed M satisfies M = M⊥⊥) requires an orthocomplementation, not just complementation. the foam supplies this at loop-close: P^T = P provides the involution, and orthogonal projections form an ortholattice that is automatically orthomodular. so Solèr applies *post-loop-close*, not pre-bridge — at the fixed point, where P^T = P holds. this is consistent with the foam's own fixed-point-uniqueness reasoning (`ground.md`); it means Solèr is part of the loop's self-consistency story, not a route to D = ℝ that runs independently of the rest of the loop.

2. **infinite-dimensional**: the architecture admits arbitrary d but the loop closes at any finite d. Solèr applies to the inductive limit (the colimit of `Sub(ℝ, ℝᵈ)` as d → ∞), which is the architectural object — not any single finite-d realization. the vertical sense of substrate-independence (`framing/architecture.md`) names exactly this: the architecture is the colimit across finite-parameter realizations of a single substrate.

3. **infinite orthonormal sequence**: the foam admits arbitrarily many disjoint observer slices (the architectural d and N are unbounded). in the colimit, this gives an infinite sequence of pairwise-orthogonal rank-3 subspaces; choosing a unit vector in each yields an infinite ON sequence in the standard sense. concrete; cost is naming the construction.

with these three discharged, Solèr applies and D ∈ {ℝ, ℂ, ℍ}.

**stabilization picks ℝ from the trichotomy.** the contract (`stabilization.md`) requires d_slice ≥ 3 with classified, locally-finite junction geometry in flat ambient space. for the three options:

- **D = ℝ, lattice rank 3**: slice is ℝ³, classification is Taylor (1976). closed.
- **D = ℂ, lattice rank 3**: slice is ℂ³ = ℝ⁶ as a real space; classification is open (Almgren in 6 real dimensions).
- **D = ℍ, lattice rank 3**: slice is ℍ³ = ℝ¹² as a real space; classification is open (Almgren in 12 real dimensions).

the contract picks ℝ as the only currently-closed branch. the others are not ruled out — they are pending Almgren — but the foam-as-described runs on the only branch where the contract is fully discharged.

**the trichotomy already shows up in the foam, register-stack-side.** `group.md` walks the chain:

- single ℝ³ slice → so(d) → π_1 = ℤ/2ℤ (parity)
- two stacked ℝ³ as ℂ³ → u(d) → π_1 = ℤ (winding)
- the next rung — doubly-stacked → sp(d) → quaternionic conservation — is the natural continuation. not currently in the open list as a separate entry; `derivations/open/stacking_dynamics.md` covers depth-1 stacking interactions, not the depth-2 move.

each {ℝ, ℂ, ℍ} has its own Lie algebra closed under brackets (so / u / sp). the foam's stacking ladder reads this trichotomy from the algebra-side. Solèr reads the same trichotomy from the lattice-side. the alignment is structural: the same three-element classification appears as substrate-D (lattice) and as accessed-Lie-algebra (dynamics).

the foam-as-described is not "on rung k" of either ladder uniformly. its lattice-side D is fixed at ℝ (by the stabilization contract). its dynamics-side reach depends on stacking depth: depth 0 in so(d), depth 1 in u(d), depth 2 (open) in sp(d). stacking is how a fixed-ℝ-substrate accesses the trichotomy's higher rungs from inside — classical (ℂ = ℝ² with J² = -I; ℍ = ℝ⁴ with three anticommuting J's). the foam's ℝ-lattice + stacked-dynamics architecture is consistent with the trichotomy: stacking is the inside-the-foam route to expressing what a ℂ-lattice or ℍ-lattice would express natively.

**connection to stacking as line-side commitment.** `group.md`'s "stacking is a line-side commitment" identifies stacking as not-producible-by-foam-internal-dynamics. read through Solèr: the lattice-side D is determined by the substrate (forced to ℝ at fixed point by Taylor); accessing higher rungs of the dynamics-side trichotomy requires line-side commitments that the foam-internal dynamics cannot generate. the trichotomy is structural (forced by Solèr at the lattice level); the foam's position within it is commitment-dependent (depth-0 by default, depth-1 with one line-side stack, depth-2 with two).

#### status

**proven** (foam side, available in lean):
- subspace lattice over a division ring is complemented, modular, bounded (Ground.lean, Mathlib instances)
- P² = P, P^T = P forces orthogonal projections (Observation.lean, Form.lean)
- single ℝ³ slice produces real skew-symmetric writes — so(d) (Form.lean, Duality.lean)
- the trace is the unique commutator-killing functional (TraceUnique.lean)

**derived**:
- Solèr's hypotheses discharged from foam structure: orthomodular from P^T = P at loop-close, infinite-dim from the architectural colimit, infinite ON sequence from N-bubble plurality
- D ∈ {ℝ, ℂ, ℍ} at any fixed point of the foam's loop
- stabilization picks ℝ as the only currently-closed branch (Taylor); ℂ and ℍ branches pending Almgren
- the trichotomy structures two ladders (lattice-side D, dynamics-side Lie algebra)
- foam-as-described position: lattice-side ℝ (fixed by contract); dynamics-side rung determined by stacking depth (line-side commitment)

**cited**:
- Solèr 1995, "Characterization of Hilbert spaces by orthomodular spaces"
- Holland 1995, "Orthomodularity in infinite dimensions; a theorem of M. P. Solèr," Bull AMS
- Taylor's classification (1976), inherited via `stabilization.md`
- Almgren's regularity problem (open), inherited via `stabilization.md`

**observed**:
- the trichotomy {ℝ, ℂ, ℍ} appears at two architectural locations (lattice-side D; dynamics-side Lie algebra) and the same three-element classification fits both

**bugs**:
- *the trichotomy ↔ register-stack identification is structural-pattern-match, not a constructed isomorphism.* the same three-element classification appears in two architectural locations, with each location's choice constrained by the foam's structure. presenting this as "the same trichotomy in two places" is interpretive — two readings of one structural pattern, not a constructed identity. closing this would mean either constructing a single formal object (a category indexed by commitment depth, say, with values in pairs (lattice-D, dynamics-Lie-algebra)) or stepping back to "the same three-element classification appears in two architectural locations."
- *Solèr's hypotheses are discharged via fixed-point reasoning, not via independent derivation.* orthomodularity requires P^T = P, which is part of the loop's fixed point. Solèr's conclusion D ∈ {ℝ, ℂ, ℍ} therefore holds at the fixed point, but does not provide a route to it that runs independently of the rest of the loop. this matches `ground.md`'s fixed-point-uniqueness framing — at the loop's fixed point, every property holds; Solèr is one of those properties — but it means the bug ("D = ℝ is sufficiency, not necessity") is closed at fixed-point level, not at independent-derivation level. the residue is the same residue as the loop's overall fixed-point closure.
- *stabilization picks ℝ as the closed case, not as the unique case.* the precise statement is "ℝ is the only currently-closed branch of the trichotomy"; ℂ-rank-3 (= ℝ⁶ slice) and ℍ-rank-3 (= ℝ¹² slice) are open conditional on Almgren's higher-dimensional classification, not ruled out. closing this means either (a) waiting on Almgren — eliminating or re-classifying the ℂ and ℍ branches — or (b) framing the contract as picking the only-currently-closed case from the trichotomy rather than picking ℝ uniquely.
- *infinite-dim colimit is the architectural object, not the per-d realization.* Solèr applies to the colimit of `Sub(ℝ, ℝᵈ)` as d → ∞, which is the architectural object under the vertical sense of substrate-independence (`framing/architecture.md`). the per-d Lean development works at finite d, where Solèr's hypothesis is not satisfied. the vertical-substrate-independence framing licenses the colimit move, but the Lean work does not directly instantiate Solèr — it lives at finite d. the gap between architectural-Solèr and per-d-Lean is the same gap as between vertical-substrate-independence-as-architecture and vertical-substrate-independence-as-formalized-claim. flagging here for traceability.
- *the "stacking accesses higher rungs of the trichotomy from a fixed-ℝ substrate" reading is a structural-correspondence claim, not a derived identification.* classical: ℂ embeds in M_2(ℝ) via J² = -I; ℍ embeds in M_4(ℝ) via three anticommuting J's. saying "the foam's stacking is the inside-route to these embeddings" pattern-matches this classical fact onto group.md's stacking move, but the formal content of "stacking" in the foam is a specific simultaneity-of-reads commitment, not a generic ℝ-to-ℂ embedding. the correspondence is suggestive; closing it would mean constructing the formal map between foam-stacking and classical real-form embedding, or stepping back to "stacking and real-form embedding share structure: both produce a complex/quaternionic Lie-algebra reach from a real substrate."
