### analogy

**analogy is structural isomorphism between lattice intervals.** two observers P and Q have analogous views when their lower intervals are order-isomorphic: Iic P ≃o Iic Q. this means: every structural relationship in P's view (which sub-observations refine which, how they meet and join) has an exact counterpart in Q's view. the isomorphism preserves lattice operations — meets map to meets, joins map to joins.

this is not metaphorical similarity. it is a precise criterion: the views have the same lattice type. the content (which specific elements occupy the positions) is free. same shape, different stuff.

**well-formedness is order-preservation.** an analogy between two views is well-formed exactly when it preserves the lattice structure — the ordering, meets, and joins. a map between intervals that doesn't preserve order is not an analogy in this sense; it doesn't transfer inferences.

the modular law is the well-formedness guard. in a modular lattice, lattice operations compose path-independently (ground.md: modularity IS feedback-persistence). this ensures that structural isomorphisms between intervals are compatible with the ambient lattice. in a non-modular lattice (N_5), an isomorphism between two sub-intervals can produce inconsistent results when composed with the lattice operations — the "analogy" generates contradictions.

**well-formed analogies are formally transitive.** order isomorphisms compose (OrderIso.trans). if Iic P ≃o Iic Q and Iic Q ≃o Iic R, then Iic P ≃o Iic R. the composition is itself an order isomorphism — it preserves lattice operations. transitivity is not an additional property to be verified; it falls out of the mathematics.

this extends through complements via the diamond isomorphism. if P and Q have analogous views (Iic P ≃o Iic Q), then:

Ici P^⊥ ≃o Iic P ≃o Iic Q ≃o Ici Q^⊥

what P can't see has the same type structure as what Q can't see. the analogy transfers not just between the views but between their complements — the unknowns are also analogous.

**the half-type theorem is the existence of analogy.** every observer has at least one structural analogy: its own view is isomorphic to its complement's type (Iic P ≃o Ici P^⊥). this is guaranteed by the lattice structure — it requires no construction, no choice. every partial observer automatically has a structural correspondence between what it sees and what it can't see.

the transitivity result says: when two observers' views match structurally, their entire epistemic situations match — both what they see AND the type of what they can't see. well-formed analogy transfers across the full complementary decomposition.

#### concrete witness: two_persp

the coordinate operations in the FTPG bridge instantiate composed analogy on lines in the projective plane. a perspectivity between two lines IS a structural isomorphism between their atom-intervals. composing two perspectivities IS OrderIso.trans.

`two_persp` (FTPGCoord.lean) makes this explicit: given line pairs (r₁, s₁) and (r₂, s₂), form perspectivity intersections p₁ = r₁ ⊓ s₁ and p₂ = r₂ ⊓ s₂, then project their join onto l:

    two_persp Γ r₁ s₁ r₂ s₂ = (r₁ ⊓ s₁ ⊔ r₂ ⊓ s₂) ⊓ l

both coordinate operations factor through this pattern (proven by `rfl` — definitional equality):

    coord_add a b = two_persp Γ (a⊔C) m (b⊔E) q       -- bridge: m
    coord_mul a b = two_persp Γ (O⊔C) (b⊔E_I) (a⊔C) m -- bridge: O⊔C

the bridge parameter is the only free variable. the functor is the same.

#### status

**proven**:
- order isomorphisms between lattice intervals exist (diamond isomorphism)
- order isomorphisms compose (OrderIso.trans)
- intervals inherit modularity and complementedness
- the modular law ensures path-independent composition of lattice operations
- coord_add and coord_mul both factor through two_persp (by rfl)
- multiplicative identity: I · a = a, a · I = a (coord_mul_left_one, coord_mul_right_one)

**derived**:
- analogy IS structural isomorphism between lattice intervals
- well-formedness IS order-preservation, guarded by the modular law
- well-formed analogies are formally transitive (from OrderIso.trans)
- analogous views imply analogous complements (from diamond isomorphism + transitivity)
- the half-type theorem guarantees every observer has at least one analogy (view ↔ complement)
- the coordinate operations are composed analogies, with the bridge as the only free parameter

**bugs**:
- *"the bridge parameter is the only free variable. the functor is the same."* the two equations `coord_add a b = two_persp Γ (a⊔C) m (b⊔E) q` and `coord_mul a b = two_persp Γ (O⊔C) (b⊔E_I) (a⊔C) m` differ in all four two_persp arguments — the bridge (called out as `m` vs `O⊔C`) is in different argument positions, and the other three arguments shift roles. "the bridge is the only free variable" reads as parameter-level identity in *this* file. the more defensible reading is from `self_parametrization.md`: structural variation between operations is parametrized by a pair (P, Q) on l, of which the bridge is one consequence. that reading is not in this file. closing this means either inlining the (P, Q) parametrization here or stepping the claim back to "the bridge is the named axis of variation among several."
- *"a perspectivity between two lines IS a structural isomorphism between their atom-intervals."* classical projective geometry; the formal connection to mathlib's `OrderIso` for perspectivities-on-atom-intervals depends on FTPGCoord.lean's construction. asserted in this file without a direct cite. flagging for traceability — the underlying fact is standard.
- *"the modular law is the well-formedness guard."* same construction as `half_type.md`'s "modular law IS the type-checking rule" — a metaphor mapping a lattice property (path-independence of composition) onto a programming-language role. suggestive, not derived. closing this would mean either constructing the formal type-theoretic structure that makes the modular law literally the guard, or stepping back to "the modular law plays the role of the well-formedness guard."
