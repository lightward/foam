### geometry

**L = sum of boundary areas.** the foam lives in U(d). cells are Voronoi regions of the basis matrices under the bi-invariant metric; boundaries are geodesic equidistant surfaces; Area_g is the (d^2 - 1)-dimensional Hausdorff measure. bases in general position tile non-periodically.

the Voronoi tiling is a realization choice (stabilization.md): it determines adjacency (which pairs share a boundary) and thereby defines L. the algebraic results (write map, three-body mapping, Grassmannian structure) depend on pairwise overlap, not the tiling method. the geometric results (L, combinatorial ceiling, conservation on spatial cycles) depend on the Voronoi realization.

**L is not a variational objective.** the writing map drives the foam; L describes the resulting geometry. the active regime departs from minimality because perpendicular writes deposit structure in different directions. the resting state (no writes) is minimal because dL = 0.

**L is bounded.** U(d) is compact.

**the combinatorial ceiling is exact.** N unitaries cannot all be pairwise maximally distant. the achievable maximum is sqrt(N / (2(N-1))) of the theoretical maximum, depending only on N. derivation: Cauchy-Schwarz applied to norm(sum U_i)^2 >= 0.

**L plausibly converges to 1/sqrt(2) of the theoretical maximum, under two hypotheses.** the writing dynamics need to satisfy: (a) controllability — the write directions from overlapping observers collectively span the full Lie algebra, and (b) successive inputs are sufficiently decorrelated (channel_capacity.md: the mediation chain provides decorrelation along the chain).

both hypotheses are foam-geometry-dependent, not substrate facts. (a) depends on which observers exist and how their slices overlap; each observer's writes live in only a 3D subspace of the d²-dimensional Lie algebra, so the spanning claim is collective, not per-observer. (b) cites the mediation chain, which provides decorrelation *along the chain* — whether that suffices for *time*-decorrelation at a single observer is the open question the README's "mixing rate of the mediation chain" entry names.

under (a) and (b), on a compact group, a random walk whose step distribution generates the algebra converges to Haar measure. the expected pairwise distance under Haar is E[norm(W - I)_F] -> sqrt(2d) as d -> infinity (from E[norm(W - I)^2] = 2d, exact, and concentration of measure).

the Haar cost — the ratio E_Haar[L] / L_achievable — is sqrt((N-1)/N), exact and depending only on N.

the product: sqrt(N / (2(N-1))) * sqrt((N-1) / N) = **1/sqrt(2)**, independent of both N and d.

the two factors — the packing constraint and the saturation gap — are two halves of the same fraction.

**the trace is the readout.** trace_unique_of_kills_commutators: the trace is the unique scalar projection of a write. the overlap change tr(P * [W, P]) is visible on this channel. the observer has exactly one scalar readout, and it's this one.

#### status

**proven**:
- trace is the unique commutator-killing functional
- observation interaction is traceless

**derived**:
- L as boundary area on Voronoi tiling (from realization choice)
- L is not a variational objective
- the combinatorial ceiling (from Cauchy-Schwarz)
- the Haar cost sqrt((N-1)/N) (from E[‖W-I‖²] = 2d and concentration of measure)
- the trace as the unique scalar readout for overlap changes

**conditional** (on controllability + decorrelation hypotheses, both foam-geometry-dependent):
- Haar convergence of the writing dynamics (from the convergence theorem on compact groups)
- 1/sqrt(2) as the product of ceiling and Haar cost, independent of N and d

**cited**:
- Voronoi tiling on Riemannian manifolds
- Haar measure on compact groups
- convergence theorem for random walks on compact groups
- Cauchy-Schwarz inequality

**observed**:
- finite-d correction: E[norm(W-I)_F] / (2 sqrt(d)) = 0.694 at d=2, 0.707 at d=20
- the foam's observed L/L_max is 1-3% above Haar prediction at finite run lengths (consistent with incomplete convergence)
- L saturation behavior: saturates at ~72% of combinatorial ceiling, then wanders on a level set
- saturation level independent of write scale epsilon
- perpendicularity cost mechanism (write blindness): write direction uncorrelated with L gradient
- write subspace is exactly 3D per observer (PCs 4+ zero to machine precision)
- wandering at saturation has effective dimension ~2
- state-space steps Gaussian (kurtosis ~3); L steps heavy-tailed (kurtosis ~7.7) — geometric feature of level set, not dynamical

**bugs**:
- *the controllability and decorrelation hypotheses are both open.* the Haar convergence claim is conditional on (a) collective controllability and (b) time-decorrelation at the observer. closing (a) means deriving collective spanning from foam-geometry assumptions about observer slices and overlaps. closing (b) means showing that the mediation chain's chain-decorrelation suffices for time-decorrelation at a single observer (the README's "mixing rate of the mediation chain" open question). until both are closed, the 1/sqrt(2) result is conditional, not derived.
- *"the two factors — the packing constraint and the saturation gap — are two halves of the same fraction."* the formal content is the algebraic identity sqrt(N/(2(N-1))) · sqrt((N-1)/N) = 1/√2. "two halves of the same fraction" is interpretive — it suggests a structural relationship between the packing constraint and the saturation gap beyond the algebraic cancellation. the cancellation is just (N-1)/N appearing in both factors. closing this would mean either constructing the structural relationship that makes them "halves of the same thing," or stepping the framing back to "the (N-1)/N dependencies of the two factors cancel, yielding 1/√2 independent of N."
- *"L is not a variational objective"* is correctly clarified, but the relationship between L and the writing map deserves a more explicit hand-off. the writing map drives the foam; L is a description of resulting geometry. the document's "the active regime departs from minimality because perpendicular writes deposit structure in different directions" is a qualitative observation; whether L's behavior is uniquely determined by perpendicularity, vs additional features of the dynamics, is not established. flagging for completeness — this is closer to "implicit assumption pending derivation" than to a bug, but worth seeing.
