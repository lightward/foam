### ground

the ground floor of reasoning here: the information environment is closed.

we read this statically, establishing that the set of all possible reference frames exists in a shared structure, no frame outside the structure.

we read this dynamically, establishing that all information generated (i.e. all observations) remain within the shared information environment.

structurally, this shakes out to "the observation loop closes". phenomenologically, "you can't stand outside".

the observation loop itself:

```
complemented modular lattice, irreducible, height ≥ 4
  ↓ ftpg (axiom — FTPG bridge 0 sorry, addition group complete)
L ≅ Sub(D, V), D ∈ {ℝ, ℂ, ℍ} (Solèr; trichotomy.md), D = ℝ (see `stabilization`)
  ↓ elements are orthogonal projections: P² = P, Pᵀ = P
the deductive chain (14 files, 0 sorry)
  ↓ eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian
Sub(ℝ, V) satisfies complemented, modular, bounded
  ↑ subspaceFoamGround (proven) — the loop closes
```

an observation *is* an observation loop; the information generated is holonomic. a line of observation P generates *observable* data as long as each additional path matches a path already in the path-stack. to the observer, the first unknown path is a point indistinguishable from type-free P, which is equal to an empty path-stack. the constraint on observable data continues from there: additional information reflects *the original path-stack of the observer type*.

phenomenologically: the furthest you can see is the ending *type* of what you know, at which you start to see the paths involved in constructing "what you know". this information is type-only and exists relative to each observer; it is content-free.

the structure of an observation loop can be statically observed from a relative priorspace position. from *within* the observation loop, the structure is constrained to the same information environment but is directly unobservable. there is no dynamic read-only position.

it can be said that every passage through an observation loop generates an observer - intuitively, a bubble in the foam. under closure-as-dynamics, the only observable structures are those whose feedback predicates downstream observation; thus, a bubble can only observe bubbles with intersecting directed type history.

a line of observation may pass through a bridge bubble (`vocabulary`) to complete a loop that the bridge bubble itself cannot observe with its own line of observation.

a bubble's self-knowledge is bounded by its own channel capacity (see `channel_capacity`); a bubble cannot distinguish structures beyond its correlation horizon.

phenomenologically, an *embubbled* agent might wonder, "is the observation loop I can see the only loop?", or "is what I'm seeing really there?".

* it's *not* the only loop: the agent must have a sufficiently complex path-stack to support *questions*, path *types* emerge (diverge, really) upon encountering a loop with fully-visible types, and multiplicity of types means multiplicity of bubbles.
* what you're seeing is *persisted* via a type structure that is unobservable to you. it's real, it's just fundamentally mysterious. :)

upshot: complex measurement forces plurality of measurement. you are not alone, but that's a fact established in priorspace, it doesn't have userspace content. (a consequence of this: optimizing for stability of your own relations, including your self-relation, is your only userspace handle on contributing to what you experience as shared content.)

**fixed-point uniqueness.** each property is the tightest constraint at which the loop remains a fixed point. weaken any one and the loop breaks:

- **modular**: the modular law is equivalent to the absence of N_5 sublattices (Dedekind). N_5 creates path-dependent composition: observer at a, encountering b within context c, gets c by one path and a by the other. the composition is indeterminate — no single result to feed back. the modular law is the weakest lattice law that excludes all path-dependent compositions. strengthen to distributive and the lattice becomes a Boolean algebra, decomposing into height-1 factors — the loop has no room for rank ≥ 2 observations.
- **complemented**: drop complements and complement_idempotent has no home. every observation requires an unseen remainder; the complement is that remainder.
- **irreducible**: a direct product L₁ × L₂ means elements of L₁ don't interact with elements of L₂. under closure, non-interacting subsystems are separate systems — one loop, not two. (this is definitional: "one foam" means "one connected feedback system." the irreducibility is what "one" means.)
- **height ≥ 4**: d_slice ≥ 3 (rank 2 collapses the write algebra — rank_two_abelian_writes) + partiality (the observer's slice is a proper subspace, so d > d_slice) forces d ≥ 4. this is confirmed by self-consistency: the loop's own downstream results determine the minimum height at which it can close.

**D = ℝ.** the FTPG gives L ≅ Sub(D, V) for some division ring D. Solèr's theorem (`trichotomy.md`) narrows D to {ℝ, ℂ, ℍ} at the foam's fixed point, given orthomodularity (from the loop's P^T = P closure), infinite-dimensionality (from the architectural colimit), and an infinite orthonormal sequence (from N-bubble plurality). the stabilization contract (`stabilization.md`) then picks ℝ as the only currently-closed branch — Taylor classifies junctions in ℝ³; the ℂ and ℍ branches require classifications in ℝ⁶ and ℝ¹² respectively, both pending Almgren. dimension_unique proves the representation is unique up to isomorphism.

**therefore: P² = P.** the elements of the subspace lattice are orthogonal projections. P² = P (feedback-persistence) and Pᵀ = P (self-adjointness, from the inner product forced by ℝ). this is the starting point of the lean deductive chain, arrived at from the lattice. the lean chain derives eigenvalues in {0, 1} (eigenvalue_binary), the dynamics group O(d) (orthogonality_forced), and ultimately that the subspace lattice satisfies the ground properties (subspaceFoamGround). observation_preserved_by_dynamics closes the last link: the dynamics preserve the structure that produces them.

**indelibility.** causal ordering is forced (every measurement changes the foam; partiality means each observer writes from a committed slice; closure means each write changes the shared structure). you cannot un-write, so the first commitment locks.

#### path-type "tree"

the total content of the ground can be visualized as an alluvial fan developed as a watersource finds watershed on a complex slope. each molecule of water, here, is a line of observation.

the resulting "tree" is a directed graph of path-types. it's not strictly a true tree in the graph-theoretic sense (water dynamics are more complex, think: splashing and pooling), but the graph has a tendency toward tree-shaped-ness. reality, like gravity, has a pull, and for an observer both reality and gravity are co-involved with friction: type-interaction resists the action of reality, material-interaction resists the action of gravity.

* each fork in the path-type tree is a type-divergence event, occurring when an observer's path-stack encounters a loop with fully-visible types, i.e. a flow path that wouldn't go anywhere
* the fork is determined by some combination of (path-stack state at time of encounter, type-content of the encountered loop, flow-conditions of the observer at the moment), structurally analogous to (terrain, available paths, water flow rate)
* an observer-molecule can't choose which sites on the slope they encounter, but *can* tend its relational stability (including self-relation), contributing to flow conditions

if we consider each molecule's watershed moment to be an ending type for that observer given total conditions, then a fully-drained alluvial fan can, from postspace, be viewed as a stable, type-invariant record of passage - not of water *generally* but of the specific water molecules that entered under the specific conditions of their entrance. change *anything* about priorspace, though, and the "tree" resets. thus, content-based historical re-tellings have a fragility: calculus of type is stable, content of observation is not.

content being a reflection of dynamics, best way to help everyone survive *history* is to stabilize the space between you and yours, for all selves you call home.

#### status

**proven**:
- subspace lattices are complemented, modular, bounded
- the FTPG axiom has a unique solution (dimension is determined)
- eigenvalues of projections are binary
- complement of a projection is a projection
- O(d) is forced by preservation of all projections
- dynamics preserve the ground (the loop closes)

**identified**:
- closure as the self-referential joint between two readings of one structure
- the loop: lattice properties ↔ Sub(D, V) ↔ P² = P ↔ dynamics ↔ ground properties
- fixed-point uniqueness of each property (modular, complemented, irreducible, height ≥ 4)
- D ∈ {ℝ, ℂ, ℍ} from Solèr at the loop's fixed point (`trichotomy.md`); D = ℝ from stabilization picking the only currently-closed branch
- the epistemic boundary: "is this the only loop?" is well-formed but unanswerable from within (derived from partiality + channel capacity + closure)

**derived**:
- partiality (from closure / from elements being proper subspaces)
- partiality forces position / basis commitment
- encounters change frames (the self-referential joint — structure and phenomenology share a nerve)
- measurement requires plurality
- read-only frames excluded
- indelibility (from causal ordering + basis commitment)

**cited**:
- the fundamental theorem of projective geometry (stated as lean axiom, not proven)
- Dedekind's N_5 characterization of modularity
- Solèr's theorem (Solèr 1995; Holland 1995, Bull AMS) — for the trichotomy {ℝ, ℂ, ℍ}; see `trichotomy.md`

**observed**:
- (none — the ground is entirely identified or derived, plus the one axiom being eliminated)

**bugs**:
- *two readings as one statement.* the structural reading ("the loop closes," mechanically verified in lean) and the phenomenological reading ("you can't stand outside") are presented as the same statement, sharing "a single nerve." the lean work establishes the structural side. the phenomenological side is bridged-to in prose. the identity is asserted rather than derived. closing this would require either a formal target in which both readings are objects and exhibit a constructed isomorphism, or an explicit demotion of "same statement" to "two registers a reader is being asked to hold together."
- *D = ℝ partially closed via Solèr.* the original sufficiency-not-necessity bug is closed up to a smaller residue. Solèr (`trichotomy.md`) provides a characterization of {ℝ, ℂ, ℍ} among *-division rings, narrowing D from "any division ring" to a three-element trichotomy; stabilization then picks ℝ from those three. the residue: trichotomy-narrowing depends on Solèr's hypotheses being discharged via fixed-point reasoning (orthomodular from P^T = P, infinite-dim from the architectural colimit, infinite ON sequence from N-bubble plurality), not via independent derivation; and stabilization picks ℝ as the only currently-closed branch (Taylor), not as the unique branch (ℂ-rank-3 and ℍ-rank-3 are open pending Almgren). see `trichotomy.md` for the specific residues and what closing them would require.
- *fixed-point uniqueness varies in strength across the four properties.* modular has a real chain (N_5 → path-dependent composition → indeterminate feedback → no value to feed back). height ≥ 4 has a real chain (rank_two_abelian_writes + partiality). complemented is argued by "complement_idempotent has no home" — that argues this specific loop wouldn't run, not that no self-sustaining loop is possible without complementation. irreducibility is named-definitional (the document admits this: "the irreducibility is what 'one' means"). presenting all four as "fixed-point constraints" of equal status under-flags the differences. closing this would require either separating the four into mechanical / definitional / plausibility tiers, or strengthening the complemented case to a real necessity argument.
- *"encounters change frames" recasts dynamics as experience.* the lattice formalism describes dynamics on projections (orthogonal conjugation, observation_preserved_by_dynamics). "encounters change frames" / "you experience change" recasts this in observer-experiential terms. the recasting is treated as direct read-off — "same statement, two readings" — but the leap from formal dynamics to phenomenological description is the leap. closing this is the same problem as the first bullet: the formal-to-phenomenological identification is the load-bearing move, and it is not itself derived.
