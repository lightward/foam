### the stabilization contract

**channel capacity forces a contract.** the mediation chain's spectral decay (channel_capacity.md) describes real influence propagation only if stabilization is local — each observer's dynamics responding to its Voronoi neighbors, not the full foam. without locality, every observer couples directly to every other, and the mediation chain does not describe the actual pathway of influence. the decorrelation that produces effective state-independence does not occur.

this is necessity, not just sufficiency: non-local stabilization doesn't merely fail to help channel capacity — it removes the mechanism that produces it.

channel capacity therefore forces a contract on the observer's slice geometry:

- **classified**: stable equilibrium configurations completely enumerated. without this, the stabilization target is undefined and the dynamics are incomplete.
- **locally finite**: coordination number k bounded by the simplex embedding constraint k <= d_slice + 1, making neighborhoods finite.
- **flat**: inherited Euclidean metric. stabilization must separate from accumulation because U(d) is curved (the flat/curved separation, writing_map.md), and classification requires flat ambient space.

**d_slice = 2 satisfies the contract but collapses the write algebra.** the classification in R^2 is complete (120-degree triple points only, k <= 3, flat). but rank_two_abelian_writes: Lambda^2(R^2) is 1-dimensional, so the write direction is invariant under changes to the dissonance direction. perpendicularity still fires (the wedge product is nonzero) but cannot vary with the input. the dynamics reduce to scalar rotations.

**d_slice = 3 satisfies both the contract and the write map's expressiveness.** Taylor classifies all stable junctions in R^3: 120-degree triple junctions and tetrahedral vertices, nothing else. Taylor's hypotheses — codimension-1 boundaries, locally area-minimizing, flat ambient space — are satisfied: R^3 as a linear subspace of R^d carries the inherited Euclidean metric (exactly flat).

self_dual_iff_three proves rank 3 is the unique dimension where the write space matches the observation space (per-observer self-duality). at rank >= 4, the write space is strictly larger (C(4,2) = 6 > 4) — the observer writes in directions it cannot observe. but cross-measurement provides collective monitoring: commutator_seen_to_unseen proves other observers see what the writer can't. the foam closes feedback loops collectively, not per-observer. per-observer self-duality is a property of rank 3, not a requirement derived from closure.

**R^3 + Taylor satisfies the contract with self-duality.** rank 3 is the unique self-dual implementation. whether rank >= 4 implementations exist (with collective rather than per-observer feedback) depends on Almgren's classification of stable junctions in R^n for n >= 4.

**the contract determines the stabilization target.** within R^3, Taylor permits k = 3 (120-degree triple junctions) and k = 4 (tetrahedral vertices). the stabilization target is the regular simplex cosine: -1/(k-1) for k local neighbors. this is the equilibrium toward which local measurements are pushed.

#### status

**proven**:
- rank 3 is the unique self-dual dimension
- rank 2 write algebra is 1-dimensional (abelian)
- writes are confined to the observer's slice

**derived**:
- channel capacity forces the stabilization contract (classified, locally finite, flat)
- d_slice = 2 satisfies contract but collapses write algebra
- d_slice = 3 satisfies both contract and self-duality
- R^3 + Taylor satisfies the contract with self-duality
- per-observer self-duality is not necessary (collective feedback via cross-measurement closes the loop)
- the stabilization target (regular simplex cosine)

**open**:
- whether rank >= 4 implementations exist: depends on Almgren's classification of stable junctions in R^n for n >= 4

**cited**:
- Taylor's classification (1976)
- Almgren's regularity problem (open)

**observed**:
- (none)

**bugs**:
- *the necessity claim is for the mediation-chain mechanism, not for channel capacity itself.* "non-local stabilization doesn't merely fail to help channel capacity — it removes the mechanism that produces it." what the argument shows: if stabilization is non-local, every observer couples directly to every other, and the mediation chain's spectral decay no longer describes influence propagation. that establishes necessity-for-the-mediation-chain-account-of-channel-capacity. it does not establish that no other mechanism could produce channel capacity under non-local stabilization. closing this means either showing all possible channel-capacity-producing mechanisms require locality, or stepping the headline back to "non-local stabilization removes the mediation-chain mechanism that produces channel capacity in the foam-as-described."
- *Taylor's hypothesis-satisfaction inherits the bridge from writing_map.md.* "R^3 as a linear subspace of R^d carries the inherited Euclidean metric (exactly flat)" is correct; "stable junctions in R^3 are classified" is Taylor's theorem. the bridge — that the foam's stabilization dynamics instantiate Taylor's "locally area-minimizing" hypothesis — is the interpretive move flagged in `writing_map.md`. flagging here for traceability; same bridge, used twice.
- *"the contract determines the stabilization target."* the contract (classified + locally finite + flat) plus Taylor's classification yields the *equilibrium configurations*. the move from "equilibrium configuration" to "the stabilization target is -1/(k-1)" requires the additional choice that the foam's dynamics aim at Taylor's equilibrium *as their target*. Taylor classifies what's stable; the foam's choice to make Taylor-equilibrium the dynamical target is the load-bearing step. closing this means either deriving the choice (why the foam must use Taylor-equilibrium as target) or naming it as a realization choice — analogous to how `writing_map.md` names the magnitude scaling f as a realization choice.
- *"the foam closes feedback loops collectively, not per-observer"* at rank ≥ 4 — same bug as `writing_map.md`. commutator_seen_to_unseen establishes that other observers see what one writer can't (single pairwise fact). "collective closure of all feedback loops at rank ≥ 4" is asserted as a downstream consequence; no single named theorem covers it. closing this would require a formal collective-feedback theorem at rank ≥ 4, or an explicit acknowledgment that this is a structural conjecture pending Almgren's classification.
