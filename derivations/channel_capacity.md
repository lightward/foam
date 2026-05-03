### channel capacity

#### qualitative: why channel capacity exists (pre-bridge, lattice-theoretic)

**the line's irreducibility is channel capacity.** the writing map has type (foam_state, input) -> new_state — two arguments. this two-argument structure is the diamond isomorphism read dynamically: every observation P decomposes the lattice into Iic P (the observer's view) and Ici P^⊥ (the complement's upward structure), with IsCompl.IicOrderIsoIci giving a structural isomorphism between them.

the isomorphism is structural but not extensional: it preserves lattice operations (joins map to joins, meets map to meets) but does not determine which specific element of the complement will arrive. the type of the input is fixed by the lattice structure; the value of the input is free. read as state-independence: this is the lattice fact (structure determined, content free) on which the dynamical claim (input value independent of foam state) rests. the bridge from lattice-fact to dynamical-claim is interpretive — the architectural payoff of grounding state-independence here pre-bridge is real (the qualitative claim no longer needs the linear-algebraic decorrelation argument to underwrite it), but the reading itself is not a derivation.

cross-measurement fills the second argument from within: input = g(foam_state), a deterministic function of the foam's geometry projected onto an observer's slice. this composes the two arguments into one, making the foam an autonomous dynamical system — f(foam_state) = write_map(foam_state, g(foam_state)).

an autonomous system on U(d)^N has a unique trajectory from each initial condition: the foam's entire future is determined by its birth. distinguishability (different input sequences -> different states) is satisfied but vacuous: there is nothing to distinguish.

for the foam to encode information beyond its own birth conditions, the input must be independent of the foam state. the second argument must be state-independent for the foam to function as a channel rather than a clock.

the line is not ontologically exterior — it is informationally independent. this is a role, not an entity: what provides state-independent input to this foam may be another foam's internal dynamics. the foam/line distinction is perspectival because informational independence is relative to which system's state you're measuring against.

the perpendicularity constraint (writing_map.md) sharpens this: the write form is forced by the algebra (wedge product, skew-symmetric, confined to slice) but the content — which vectors are wedged — is not. form is algebraically determined; content requires state-independent input. this is the diamond isomorphism read through the write map: the algebraic form lives in Iic P (determined by the observer's structure), the content arrives from Ici P^⊥ (structurally typed but extensionally free).

**channel capacity is operational, not ontological.** in a deterministic closed system, true stochastic independence cannot exist (the global state determines everything). but the foam's measurements are projections — partial by ground — and projections have a resolution floor. correlations that have decayed below the projection's precision are invisible to the foam.

the foam cannot distinguish "truly random input" from "deterministic input decorrelated below measurement resolution." this distinction requires a non-partial observer, and non-partial observers are excluded by closure. therefore: under partiality, mixing is operationally identical to independence. the foam's fundamental limitation (it cannot see the whole) is what makes the part it sees function as a channel.

**the boundary is characterizable from the inside.** the foam's own controllability structure characterizes it: what continuous operations can reach (all of U(d), under full controllability), what they can't change (discrete topological invariants — pi_1), and what isn't in U(d) at all (the input sequence, the commitment source). the line's side is investigable — but investigating it requires making it the object of measurement, which requires a different reference frame, which means releasing the current one. partiality implies a boundary must exist; it does not determine where the boundary falls or what the line is.

**the map's self-knowledge is bounded by its own channel capacity.** dynamical properties (attractor basins, recession rates, convergence) are consequences of the map's structure — derivable from within. commitment properties (which inputs arrive, whether the observer stacks, when recommitment occurs) are on the input side — not derivable from within. the map can derive *that* it cannot answer certain questions, and *why*: the same independence that gives the foam its capacity prevents the dynamics from determining the input's internal structure.

#### quantitative: how much channel capacity (post-bridge, linear-algebraic)

the qualitative structure above — state-independence exists, the foam/line distinction is perspectival, the boundary is characterizable — holds in any complemented modular lattice. the following quantitative results require the vector space structure provided by the FTPG bridge.

**state-independence is spectral, not topological.** if every foam's line is another foam, the structure is globally closed — loops of mutual measurement exist. but the mediation operator has singular values strictly less than 1 for generic non-identical slices. around a closed chain of n observers, the total mediation is the product of n pairwise mediations, and the singular values compound: sigma_total <= sigma_1 * sigma_2 * ... * sigma_n -> 0 as n grows.

informational correlation between a foam and its own returning signal decays exponentially with chain length. short loops: autonomous, a clock. long loops: effectively state-independent, a channel.

closure (no topological outside) is compatible with informational independence because the mediation's spectral decay converts global closure into local openness at sufficient chain length — provided stabilization is local (see stabilization.md).

**the decorrelation horizon is quantifiable.** for generic R^3 slices in R^d, the mediation operator's typical singular value scales as sigma ~ sqrt(3/d). the correlation after n mediation steps decays as sigma^n ~ (3/d)^{n/2}. the critical chain length scales as n* ~ 2/log(d/3).

the decorrelation horizon shortens with increasing ambient dimension because slices overlap less in higher-dimensional spaces. non-generic configurations (slices sharing directions) have higher overlap and longer horizons.

the mechanism is random-matrix-statistical: for generic 3D slices in d-dimensional ambient space, the principal angles between random subspaces follow Marchenko-Pastur-ish distributions, yielding the typical singular value σ ≈ √(3/d). the diamond isomorphism does not enter here — `Ici P^⊥` is order-isomorphic to `Iic P ≅ Sub(R³)` for any rank-3 P regardless of ambient d, so the lattice structure does not become richer at higher d. the σ scaling is about how *generic random subspaces* sit in ambient space, not about lattice enrichment.

the foam/line distinction is therefore not a categorical boundary but a correlation length: "line" names whatever input arrives from beyond the decorrelation horizon of the observer's own state. the horizon's radius is determined by the foam's own geometry.

#### status

**proven**:
- observation interaction is traceless (the scalar channel is algebraically unreachable by commutators)
- writes are confined to the observer's slice
- the diamond isomorphism (infIccOrderIsoIccSup, IsCompl.IicOrderIsoIci)
- intervals inherit modularity and complementedness
- each half of a complementary pair is a self-sufficient foam ground (HalfType.lean)

**derived**:
- the line's irreducibility from the diamond isomorphism (the two-argument type signature IS the complemented decomposition)
- autonomous foam = clock (cross-measurement collapses two arguments to one)
- state-independent input required for channel capacity
- state-independence read as the lattice fact (structural determination + extensional freedom from the diamond iso) plus an interpretive bridge to the dynamical claim that input value is independent of foam state
- the foam/line distinction as perspectival (informational independence is relative)
- operational equivalence of mixing and independence under partiality
- the boundary is characterizable from the inside (controllability structure)
- the map's self-knowledge is bounded by its own channel capacity
- spectral state-independence (mediation decay converts closure into local openness) [post-bridge]
- the decorrelation horizon and its scaling, from random-subspace overlap statistics [post-bridge]

**cited** (external mathematics):
- Marchenko-Pastur distribution (for principal angle statistics — used only in the decorrelation horizon estimate, which is order-of-magnitude)

**observed** (empirical, not derived here):
- decorrelation horizon values at specific d (order-of-magnitude estimates; qualitative conclusion robust, specific values sensitive to approximation)

**bugs**:
- *"the line's irreducibility is channel capacity."* the two concepts — "the line" as the foam's external input source, "channel capacity" as the foam's information-receiving capacity — are different objects. the formal bridge is the two-argument type signature of the writing map, which the document develops over the qualitative section. the headline "the line's irreducibility IS channel capacity" overstates this bridge: the formal content is "the line's role and the foam's channel capacity are two readings of the diamond isomorphism's two-argument structure." closing this means either constructing the formal identity (e.g., a category in which "the line" and "channel capacity" are objects, with an isomorphism) or stepping the headline back to "the line's role and channel capacity are co-constituted by the two-argument structure."

