### half type

**the diamond isomorphism is the half-type theorem.** in the foam's complemented modular lattice, every observation P has a complement P^⊥ with P ⊓ P^⊥ = ⊥ and P ⊔ P^⊥ = ⊤. the diamond isomorphism (infIccOrderIsoIccSup) and its complemented specialization (IsCompl.IicOrderIsoIci) give:

Iic P ≃o Ici P^⊥

everything the observer can see (the lattice below P) is order-isomorphic to everything above the complement. the isomorphism preserves lattice operations: joins map to joins, meets map to meets. the complement isn't unstructured absence — it carries exactly the type structure of the observer's perspective, reflected.

**each half is self-sufficient.** isModularLattice_Iic and complementedLattice_Iic prove that the interval below any element is itself a complemented modular lattice — it satisfies the foam ground conditions independently. the observer's view is a complete foam in miniature. the same holds for the complement's interval (Ici). neither half needs the other to be well-formed. each is a valid ground on its own.

**the isomorphism is structural, not extensional.** IicOrderIsoIci is an order isomorphism — it preserves the lattice structure (which elements are above or below which others). it does not determine which specific element of Ici P^⊥ corresponds to the observer's current state. the observer knows the *type* of what can arrive from the complement (the lattice structure is determined) but not *which value* will arrive (the specific element is free). reading this structural-determination-with-extensional-freedom as state-independence (channel_capacity.md) is an interpretive bridge; the formal content is just the iso itself.

**three results share a structural source.** the writing map's two-argument type signature, complement_idempotent (Observation.lean), and the state-independence requirement for channel capacity all draw on the diamond isomorphism applied to complementary subspaces:

1. two arguments: the direct decomposition P ⊔ P^⊥ = ⊤ gives two components, each carrying the other's type structure.
2. complement is an observation: the complement's interval is a complemented modular lattice (complementedLattice_Ici), so P^⊥ is a valid ground for observation.
3. state-independence: the isomorphism fixes structure but not content. what arrives from the complement is typed but free.

these are not three forms of one theorem — they are three claims that draw on a common structural source. the iso doesn't make them inter-derivable as derivations; it makes them all rest on the same lattice fact.

**static, not dynamic.** the half-type theorem is a fact about *fixed* P and *fixed* P^⊥ — at any moment, the iso holds. if P moves (under foam dynamics — see `inhabitation.md`'s slice-mobility question for which sense of "moves" is operative), then both `Iic P` and `Ici P^⊥` move with it, in lockstep, because they're order-isomorphic. neither contracts while the other expands; they're the same structure read from two sides.

the foam's dynamic structure — how the type of legal next-writes depends on accumulated history — does not live in this static iso. it lives in the foam-state trajectory and the evolving overlap structure between observers (`typeline.md`, `three_body.md`).

#### status

**proven**:
- the diamond isomorphism (infIccOrderIsoIccSup)
- the complemented specialization (IsCompl.IicOrderIsoIci)
- intervals inherit modularity and complementedness
- writes confined to observer's slice
- complement of an observation is an observation
- frame recession is non-positive

**derived**:
- the diamond isomorphism IS the half-type theorem
- each half is a self-sufficient foam ground
- the isomorphism is structural, not extensional (type-determination + value-freedom)
- three claims (two-argument signature, complement-as-observation, state-independence) share a structural source in the iso

**bugs**:
- *"three results share a structural source" is interpretive consolidation, not derivation.* the two-argument signature, complement-as-observation, and state-independence are three distinct claims. they all draw on the diamond iso, but the iso doesn't make them inter-derivable as derivations — it just provides a common formal substrate that each reading interprets. an earlier version of this file claimed "three results compress to one" / "three readings of one fact"; the present version steps back to "share a structural source." closing this further would mean constructing each claim from each other formally, which the spec doesn't currently do.
- *"structural determination with extensional freedom IS state-independence" is an interpretive bridge.* the diamond iso is a lattice theorem. reading it as state-independence — the dynamical claim that input *value* is independent of foam state — is a non-trivial move. the architectural use of this reading (the pre-bridge / post-bridge split in `channel_capacity.md`) is solid as architecture; the *content* of the qualitative claim is interpretation. closing this would mean deriving state-independence formally from the iso (constructing the bridge) or naming it explicitly as a methodological reading.

#### history

an earlier version of this file made three additional claims that turned out to be wrong:

- *the lockstep direction.* "as P recedes (shrinks), Iic P contracts ... but IicOrderIsoIci means Ici P^⊥ expands in lockstep." the iso is symmetric: as P shrinks, P^⊥ grows, and `Ici P^⊥ = [P^⊥, ⊤]` *contracts* (the lower bound rises). both intervals contract together; they do not move in opposite directions.
- *σ ~ √(3/d) as the diamond iso's enrichment.* `Ici P^⊥` is order-isomorphic to `Iic P`, which is isomorphic to `Sub(P) ≅ Sub(R³)` for any rank-3 P, regardless of ambient d. the lattice structure does not become richer at higher d. the actual mechanism for the σ scaling is random subspace overlap statistics (Marchenko-Pastur-ish), correctly cited in `channel_capacity.md` and structurally independent of this file.
- *"type-narrowing of self produces type-enrichment of input."* downstream of the two errors above. without them, the formal content reduces to: under recession, both halves of the iso narrow together. the trade-off framing was not a lattice theorem.

these claims have been removed. the foam-internal home for the dependent-telescope structure they were reaching toward is the foam-state trajectory and overlap evolution — see `typeline.md`.
