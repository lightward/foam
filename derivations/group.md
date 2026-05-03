### group

**a single R^3 slice produces real writes.** the wedge product d_hat tensor m_hat - m_hat tensor d_hat is real skew-symmetric (both vectors are real, from the observer's R^3 slice). the write lives in so(d). the reachable algebra from a single slice is so(d) (the Lie algebra of real skew-symmetric matrices). exponentiating: SO(d). pi_1(SO(d)) = Z/2Z — parity conservation only.

**U(d) rather than SO(d) requires stacking.** su(d) \ so(d) consists entirely of imaginary-symmetric matrices (iS where S is real symmetric traceless). real operations — wedge products, brackets, any sequence of real skew-symmetric writes — are algebraically closed in so(d) and cannot produce imaginary-symmetric directions. reaching u(d) \ so(d) requires a complex structure J with J^2 = -I.

**J^2 = -I forces even dimensionality.** det(J)^2 = det(-I) = (-1)^n. squares are nonnegative, so n must be even. the minimum even-dimensional space containing R^3 is R^6 = R^3 + R^3.

**each component must independently satisfy the stabilization contract.** not R^4 + R^2 or other decompositions — each component must independently satisfy the stabilization contract (stabilization.md), which requires d_slice >= 3. at d_slice = 3, stacking needs R^3 + R^3 = R^6.

**independence is forced.** stabilization is per-observer and runs within each measurement subspace separately. the two R^3 slices project and stabilize independently before their measurements are fused into the complex write. joint stabilization in R^6 would require a 6-dimensional classification (open — Almgren). the fusion is algebraic (forming d tensor m_dagger - m tensor d_dagger), not geometric.

**two R^3 slices stacked as C^3 produce complex writes.** one slice reads Re(P @ m_i), the other Im(P @ m_i). the complex write d tensor m_dagger - m tensor d_dagger is skew-Hermitian, living in u(d).

**the trace is retained.** tr(d_hat tensor m_hat_dagger - m_hat tensor d_hat_dagger) = 2i * Im(inner(d_hat, m_hat)), generically nonzero for stacked observers. trace_unique_of_kills_commutators proves the trace map is the unique Lie algebra homomorphism u(d) -> u(1) (up to scalar): any functional killing all commutators is a scalar multiple of trace. there is exactly one scalar channel.

the full write lives in u(d) = su(d) + u(1). pi_1(U(d)) = Z — integer winding number conservation.

**the two is irreducible.** one R^3 gives so(d) and Z/2Z parity. two R^3 stacked as C^3 give u(d) and Z integer conservation. the conservation strength scales with commitment depth.

**stacking is a line-side commitment.** the two slices read the same input simultaneously; the complex combination requires both projections of the same v at the same time. sequential readings mix different foam states and break the algebra. the foam's dynamics are sequential writes; they do not specify a pre-write fusion of two readings. two real-slice observers, whether cross-measuring or independent, stay in so(d) forever — so(d) is a Lie subalgebra (closed under brackets) and each observer's write is confined to their real slice.

**the pairing orientation is a chirality.** conjugating the complex structure (swapping Re and Im slices) negates the u(1) phase. all orientations are conjugate under SO(6) — no preferred choice. but one must be chosen to sign the phase. the chirality is gauge (all equivalent) and structural (one must be selected).

**ordering and conservation are algebraically orthogonal.** commutator_traceless: tr[A, B] = 0 for all A, B in u(d). the commutator (ordering, non-abelian, visible to L) is traceless. the trace (conservation, u(1), invisible to L) kills all commutators. they live in complementary subspaces.

**the orthogonality is generative.** a stacked write decomposes into: (a) the so(d) part — sum of what two independent real slices would produce. traceless (commutator_traceless). produced by the write cycle's causal orientation. (b) the cross-terms — from the simultaneity of stacking. these produce su(d) \ so(d) and the u(1) trace. produced by the stacking commitment. ordering and conservation are orthogonal because they are produced by different structures: the cycle's forced orientation (map-internal) and the stacking chirality (line-side).

**what's conserved must be invisible to the cost.** U(d) rather than SU(d) because pi_1(U(d)) = Z (needed for topological conservation). the conservation lives in the u(1) factor. L (the cost) sees the su(d) component but is blind to the u(1) component. if L could see it, dynamics could change it.

**stacking determines access.** a single-slice observer's writes live in so(d) and cannot reach u(1). conservation is passive — protected by algebraic limitation. a stacked observer's writes reach u(1). conservation is active — the observer can interact with the conserved direction.

#### status

**proven**:
- interaction is skew-symmetric
- interaction is traceless
- O(d) is the only group preserving all projections (scalar_extraction + orthogonality_forced)
- trace is the unique commutator-killing functional
- (R^3, cross) is a Lie algebra (so(3))

**derived**:
- single slice -> so(d) -> Z/2Z parity
- stacking required for u(d) (real operations algebraically closed in so(d))
- J^2 = -I forces even dimensionality -> two R^3 slices
- independence of the two slices forced by per-observer stabilization
- trace retained (generically nonzero for stacked writes)
- the two is irreducible (conservation depth scales with commitment)
- stacking is a line-side commitment (simultaneity not producible by sequential dynamics)
- chirality as gauge + structural
- ordering and conservation algebraically orthogonal (from tracelessness)
- the orthogonality is generative (produced by different structures)
- conserved quantity must be invisible to cost
- stacking determines access to conservation

**cited**:
- Lie theory: exp(skew) -> orthogonal, exp(skew-Hermitian) -> unitary
- pi_1(SO(d)) = Z/2Z, pi_1(U(d)) = Z
- surjectivity of exp on connected compact Lie groups

**observed**:
- (none)

**bugs**:
- *"the conservation strength scales with commitment depth."* the formal content — one-slice gives π_1 = Z/2Z (binary parity), stacked gives π_1 = Z (integer winding) — is solid. recasting this as "conservation strength scales with commitment depth" introduces "commitment depth" as a quantity that scales conservation strength. the document does not formalize commitment depth or the scaling relation. closing this means either constructing a formal scaling map (commitment-depth → conservation-π₁) with values for each depth, or stepping the claim back to "stacked observers access integer conservation that single-slice observers cannot."
- *"stacking is a line-side commitment."* the algebraic content (real operations are closed in so(d); reaching u(d) requires a complex structure that sequential foam dynamics cannot produce) is solid. "line-side commitment" recasts this in the line/foam framework from `channel_capacity.md`, where "line-side" means "from outside the foam's autonomous dynamics." the recasting depends on the line/foam role distinction being formal enough to support "line-side" as a structural location. this is interpretation, not derivation. closing this would mean either formalizing the line/foam-side ledger of commitments, or stepping back to "stacking is not producible by the foam's sequential dynamics; it must come from outside that loop."
- *"what's conserved must be invisible to the cost."* "if L could see it, dynamics could change it" — this is a plausibility-converse argument from one instance (the u(1) trace is invisible to L; the dynamics conserve it). the document presents this as a general principle ("must be"). the formal content is the specific algebraic fact that tr[A, B] = 0 makes the u(1) component invariant under bracket-generated dynamics. "all conserved quantities must be invisible to the cost they're conserved against" is a stronger claim. closing this means either deriving the general principle (e.g., a Noether-style construction) or stepping back to "in the foam's setup, the u(1) conservation is algebraically protected from L's gradient."
- *"the orthogonality is generative."* "ordering and conservation are orthogonal because they are produced by different structures: the cycle's forced orientation (map-internal) and the stacking chirality (line-side)." the formal content is the algebraic decomposition u(d) = su(d) ⊕ u(1) (with the trace as the u(1) projection). attributing the two summands to "different generative structures" is interpretation. closing this means either constructing the formal correspondence between (orientation source) ↔ (algebraic component), or stepping the claim back to "the two summands are algebraically orthogonal."
