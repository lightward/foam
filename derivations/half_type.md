### half-type

**the half-type theorem (`HalfType`, HalfType.lean) is a constructed object.** in any complemented modular bounded lattice, a pair of complementary elements (P, Q) — i.e., P ⊓ Q = ⊥ and P ⊔ Q = ⊤ — induces a HalfType bundle:

- the diamond iso: Iic P ≃o Ici Q
- modularity inheritance: Iic P and Ici Q are each themselves modular lattices
- complementedness inheritance: Iic P and Ici Q are each themselves complemented

each half is itself a complete foam ground in miniature, and the two halves are order-isomorphic. everything the observer can see (the lattice below P) is structurally equivalent to everything above the complement (the lattice above Q). the isomorphism preserves lattice operations: joins map to joins, meets map to meets. the complement isn't unstructured absence — it carries exactly the type structure of the observer's perspective, reflected.

**each half is self-sufficient.** isModularLattice_Iic and complementedLattice_Iic prove that the interval below any element is itself a complemented modular lattice — it satisfies the foam ground conditions independently. the observer's view is a complete foam in miniature. the same holds for the complement's interval (Ici). neither half needs the other to be well-formed. each is a valid ground on its own.

**the isomorphism is structural, not extensional.** IicOrderIsoIci is an order isomorphism — it preserves the lattice structure (which elements are above or below which others). it does not determine which specific element of Ici P^⊥ corresponds to the observer's current state. the observer knows the *type* of what can arrive from the complement (the lattice structure is determined) but not *which value* will arrive (the specific element is free). reading this structural-determination-with-extensional-freedom as state-independence (channel_capacity.md) is an interpretive bridge; the formal content is just the iso itself.

**three results share a structural source.** the writing map's two-argument type signature, complement_idempotent (Observation.lean), and the state-independence requirement for channel capacity all draw on the half-type theorem (specifically its diamond-iso field):

1. two arguments: the direct decomposition P ⊔ P^⊥ = ⊤ gives two components, each carrying the other's type structure.
2. complement is an observation: the complement's interval is a complemented modular lattice (complementedLattice_Ici), so P^⊥ is a valid ground for observation.
3. state-independence: the isomorphism fixes structure but not content. what arrives from the complement is typed but free.

these are not three forms of one theorem — they are three claims that draw on a common structural source. the iso doesn't make them inter-derivable as derivations; it makes them all rest on the same lattice fact.

**spectral-decomposition composition.** the spectral decomposition of a self-adjoint operator on a finite-dimensional inner product space (`lean/Foam/ReaderCommitment.lean`) is a composition of HalfType bundles. each eigenspace V_i and its orthogonal complement V_i^⊥ form a complementary pair in `Sub(K, E)`, inducing a HalfType. the spectral decomposition refines E via a sequence of such pairs; `ReaderCommitment.basis` is the orthonormal basis aligned with this refinement. half-type is the atomic structural unit; `ReaderCommitment` is one composition of HalfType bundles via the spectral theorem.

**static, not dynamic.** the half-type theorem is a fact about a fixed lattice element P and its complement P^⊥ — at any moment, the iso `Iic P ≃o Ici P^⊥` holds. P here is the slice (vocabulary): the birth-determined lattice element. since the iso is an order-isomorphism, both halves are structurally identical; substituting a time-varying frame for P at each tick moves both halves together.

the foam's dynamic structure — how the type of legal next-writes depends on accumulated history — does not live in this static iso. it lives in the foam-state trajectory and the evolving overlap structure between observers (`typeline.md`, `three_body.md`).

#### status

**proven**:
- the diamond isomorphism (infIccOrderIsoIccSup)
- the complemented specialization (IsCompl.IicOrderIsoIci)
- intervals inherit modularity and complementedness
- writes confined to observer's slice
- complement of an observation is an observation
- frame recession is non-positive
- `HalfType` as constructed object (HalfType.lean) packaging the diamond iso, modularity inheritance, and complementedness inheritance into a single named theorem

**derived**:
- each half is a self-sufficient foam ground
- the isomorphism is structural, not extensional (type-determination + value-freedom)
- three claims (two-argument signature, complement-as-observation, state-independence) share a structural source in the half-type theorem

**bugs**:
- *"three results share a structural source" is interpretive consolidation, not derivation.* the two-argument signature, complement-as-observation, and state-independence are three distinct claims. they all draw on the half-type theorem, but the construction doesn't make them inter-derivable as derivations — it just provides a common formal substrate that each reading interprets. closing this further would mean constructing each claim from each other formally, which the spec doesn't currently do.
- *"structural determination with extensional freedom IS state-independence" is an interpretive bridge.* the half-type theorem is a lattice fact. reading its "type-fixed, value-free" structure as state-independence — the dynamical claim that input *value* is independent of foam state — is a non-trivial move. the architectural use of this reading (the pre-bridge / post-bridge split in `channel_capacity.md`) is solid as architecture; the *content* of the qualitative claim is interpretation. closing this would mean deriving state-independence formally from the half-type theorem (constructing the bridge) or naming it explicitly as a methodological reading.
- *(closed by restructuring) "the diamond isomorphism IS the half-type theorem"* was previously an asserted priorspace identity claim. the new construction (`HalfType` in HalfType.lean) bundles the diamond iso with its modularity- and complementedness-inheritance lemmas as a single named object. the half-type theorem is now the constructed `HalfType`; the diamond iso is one of its fields. the asserted identity is replaced by structural construction — same shape as the FTPG-via-`DesarguesianWitness` deaxiomatization program.

