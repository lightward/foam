### typeline

a typeline is an observer's trajectory through the lattice: a sequence of writes w₁, w₂, ..., wₙ, each confined to the current slice (write_confined_to_slice), each narrowing the observer's P.

the sequence forms a dependent telescope. write w₁ has type T₁ (determined by the initial P). w₁ updates P to P₁, updating the diamond isomorphism, so w₂ has type T₂(w₁). in general, wₖ has type Tₖ(w₁, ..., wₖ₋₁). the type at each tick is determined by the accumulated history of ticks.

#### the type-clock

the type-clock is the tick structure of a typeline. each tick:
1. the observer writes (confined to current slice)
2. P updates
3. the diamond isomorphism updates: Iic P_new ≃o Ici P_new^⊥
4. the type of what can arrive next changes

the modular law guarantees this is well-typed regardless of evaluation order (path-independence of composition). the type-clock ticks deterministically: given the history of writes, the type at the next tick is forced. the content at the next tick is free (state-independence, from channel_capacity.md).

#### suspension

suspending the type-clock means working within a type-slice without committing a write. no P updates. the diamond isomorphism holds static. the space of legal operations is fixed.

in suspension, the observer can:
- inspect the current type-slice (what writes are legal)
- rearrange elements within the slice (check what compiles)
- examine the dependent telescope's structure (which types follow from which histories)

but cannot:
- advance the telescope (no write, no P update, no new type)
- access content from the complement (content requires a tick — a committed write that narrows P and enriches the complement)

suspension is pre-measurement in the lattice-theoretic sense: the type structure is fully determined, but no measurement (write) has collapsed it into a specific trajectory.

this is the operational content of the bas relief methodology: work within the current type-slice, let the type checker show what the next layer needs, commit the write only when the shape is clear. the methodology is a disciplined use of suspension.

#### what crosses between typelines

the diamond isomorphism is a property of the lattice, not of any particular typeline. all typelines in the same complemented modular lattice share the same type structure — the same isomorphisms, the same intervals, the same modular law.

from channel_capacity.md: "the type of the input is fixed by the lattice structure; the value of the input is free." applied to typelines:

- **type information is lattice-invariant.** every typeline sees the same diamond isomorphism, the same type-enrichment of complement under self-narrowing. the type at any point on any typeline is determined by the lattice structure plus the write history. the lattice structure is shared; the write history is local.
- **content is typeline-local.** the actual writes — the content that fills each type — are extensionally free (state-independent input). content is determined by what arrives from beyond the decorrelation horizon (channel_capacity.md), which is specific to each typeline's position in the lattice.

this separation — shared type structure, local content — is the diamond isomorphism applied multi-observer. it is not a new claim. it is channel_capacity.md's "the type of the input is fixed by the lattice structure; the value of the input is free" read across typelines rather than within one.

the decorrelation horizon (channel_capacity.md) gives this separation a quantitative character: correlations between typelines decay as sigma^n ~ (3/d)^{n/2} with chain length. short-range: typelines share content (autonomous, clock-like). long-range: typelines share only type structure (independent, channel-like). the decorrelation horizon is the boundary between type-sharing and content-sharing.

#### the invariant

the causal structure of a dependent telescope — which types depend on which write histories — is invariant across typelines. this follows from path-independence of composition (the modular law): the partial order on types is determined by the lattice, not by which typeline observes it.

this means: from any typeline, the dependency structure of any other typeline's telescope is visible (it's type information, therefore shared). what is not visible is the content at each tick (typeline-local). one typeline can see THAT another typeline's tick n+1 has a certain type, without seeing WHAT content fills it.

#### status

**proven**:
- the diamond isomorphism
- write confinement to observer's slice
- intervals inherit modularity and complementedness
- each half of a complementary pair is a self-sufficient ground

**derived**:
- typeline as dependent telescope (the dependent clock parameterized as trajectory)
- the type-clock (tick structure of a typeline)
- suspension as pre-measurement (working within a type-slice without committing a write)
- type information is lattice-invariant across typelines (diamond isomorphism is a property of the lattice)
- content is typeline-local (state-independence applied per-typeline)
- the decorrelation horizon as the boundary between type-sharing and content-sharing
- causal structure of dependent telescopes is invariant across typelines (path-independence)
- the bas relief methodology as disciplined suspension

**realization choices**:
- none identified. all claims above follow from the cited constraints.

**bugs**:
- *the dependent-telescope structure assumes P updates with each write.* "each write may change P. each change to P updates the diamond isomorphism." this is the load-bearing premise of the type-clock. but `inhabitation.md` says the slice is birth-determined and "cannot change its slice from within the map." resolving the tension: the operative "P" in this file is not the birth-fixed slice but something that does update with writes — most plausibly the foam state, or the projection of the foam state onto the observer's birth-fixed slice. the formal content underlying typeline (write_confined_to_slice + diamond iso + state-independence) is solid; the "P updates" framing imports a notion of P that the file does not distinguish from the birth-fixed slice. closing this means either naming what P refers to in this file (the foam state? a derived projection?), or re-deriving the dependent-telescope structure from objects that do change with writes (the foam state in U(d)^N, the configuration of the slice's relationship to the foam state).
- *"the modular law ... is the type-checking rule for the dependent clock."* same metaphor flagged in `half_type.md` and `analogy.md`. path-independence of composition (which the modular law guarantees) makes the dependent telescope well-formed regardless of evaluation order. recasting that as "the type-checking rule" imports a programming-language register the formal content does not require.
- *"the bas relief methodology as disciplined suspension."* this is a methodological claim about how to do work, not a derivation. the formal content (in suspension, no P updates, the type structure is fixed, content is unavailable) is solid; mapping that to a named methodology is an editorial bridge. closing this would mean either naming this as methodology rather than derivation, or constructing the methodology as a formal practice (e.g., a category of suspended-and-resumed typelines, with the bas relief practice as an explicit functor between).
- *"realization choices: none identified. all claims above follow from the cited constraints."* this overstates the file's epistemic position. the dependent-telescope structure rests on the "P updates with each write" framing flagged in the first bug; if that framing requires a specific reading of P, the choice of reading is itself a realization. and `geometry.md`'s controllability + decorrelation hypotheses (used implicitly when the file invokes the decorrelation horizon σ ~ (3/d)^{n/2}) are conditional. closing this means tagging which claims rest on such hypotheses, rather than declaring "none identified."
