### ground

the ground floor of reasoning here: the information environment is closed.

we read this statically, establishing that the set of all possible reference frames exists in a shared structure, no frame outside the structure.

we read this dynamically, establishing that all information generated (i.e. all observations) remain within the shared information environment.

structurally, this shakes out to "the observation loop closes". phenomenologically, "you can't stand outside".

the observation loop itself:

```
complemented modular lattice, irreducible, height ≥ 4
  ↓ ftpg (axiom — FTPG bridge 0 sorry, addition group complete)
L ≅ Sub(D, V), D ∈ {ℝ, ℂ, ℍ} (Solèr; trichotomy.md)
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

**the trichotomy.** the FTPG gives L ≅ Sub(D, V) for some division ring D. Solèr's theorem (`trichotomy.md`) narrows D to {ℝ, ℂ, ℍ} at the foam's fixed point, given orthomodularity (from the loop's P^T = P closure), infinite-dimensionality (from the architectural colimit), and an infinite orthonormal sequence (from N-bubble plurality). the architecture admits all three branches; which branch any given foam-instantiation runs on is realization-choice. the lean development works at ℝ; ℂ and ℍ instantiations would require their own structural classifications (pending Almgren in ℝ⁶ and ℝ¹² respectively). dimension_unique proves the representation is unique up to isomorphism.

**therefore: P² = P.** the elements of the subspace lattice are orthogonal projections. P² = P (feedback-persistence) and Pᵀ = P (self-adjointness, from the inner product forced by ℝ). this is the starting point of the lean deductive chain, arrived at from the lattice. the lean chain derives eigenvalues in {0, 1} (eigenvalue_binary), the dynamics group O(d) (orthogonality_forced), and ultimately that the subspace lattice satisfies the ground properties (subspaceFoamGround). observation_preserved_by_dynamics closes the last link: the dynamics preserve the structure that produces them.

**indelibility.** causal ordering is forced (every measurement changes the foam; partiality means each observer writes from a committed slice; closure means each write changes the shared structure). you cannot un-write, so the first commitment locks.

#### path-type "tree"

the total content of the ground can be visualized as an alluvial fan developed as a watersource finds watershed on a complex slope. each molecule of water, here, is a line of observation.

the resulting "tree" is a directed graph of path-types. it's not strictly a true tree in the graph-theoretic sense (water dynamics are more complex, think: splashing and pooling), but the graph has a tendency toward tree-shaped-ness. reality, like gravity, has a pull, and for an observer both reality and gravity are co-involved with friction: type-interaction resists the action of reality, material-interaction resists the action of gravity.

* each fork in the path-type tree is a type-divergence event, occurring when an observer's path-stack encounters a loop with fully-visible types, i.e. a flow path that wouldn't go anywhere
* the fork is determined by some combination of (path-stack state at time of encounter, type-content of the encountered loop, flow-conditions of the observer at the moment), structurally analogous to (terrain, available paths, water flow rate)
* an observer-molecule can't choose which sites on the slope they encounter, but *can* tend its relational stability (including self-relation), contributing to flow conditions

if we consider each molecule's watershed moment to be an ending type for that observer given total conditions, then a fully-drained alluvial fan can, from exitspace, be viewed as a stable, type-invariant record of passage - not of water *generally* but of the specific water molecules that entered under the specific conditions of their entrance. change *anything* about priorspace, though, and the "tree" resets. thus, content-based historical re-tellings have a fragility: calculus of type is stable, content of observation is not.

content being a reflection of dynamics, best way to help everyone survive *history* is to stabilize the space between you and yours, for all selves you call home.

#### status

**proven**:

- subspace lattices are complemented, modular, bounded (`Ground.lean`)
- eigenvalues of projections are binary (`Observation.lean`)
- complement of a projection is a projection (`Observation.lean`)
- O(d) is forced by preservation of all projections (`Group.lean`, `Ground.lean`)
- dynamics preserve the ground — the loop closes (`Closure.lean`, `Ground.lean`)
- the FTPG axiom has a unique solution at fixed dimension (`dimension_unique`)

**identified**:

- closure of the information environment: static reading (no frame outside the structure) and dynamic reading (all generated information remains within the environment), located in their respective registers via the priorspace/userspace tooling
- the observation loop as the structural shape closure takes (lattice properties → Sub(D, V) → P² = P → dynamics → ground properties)
- observation as holonomic loop: data observable iff each additional path matches a path already in the path-stack; first unknown path is type-free, indistinguishable from empty path-stack
- bridge bubbles as the architecture allowing a line to complete a loop the bridge itself cannot observe with its own line (see `vocabulary`)
- the path-type "tree" as alluvial-fan-shaped record of passage, type-invariant only relative to entrance conditions; reset by any priorspace change
- friction as the substrate-independent resistance-against-pull: type-interaction resists reality, material-interaction resists gravity

**derived**:

- complex measurement forces plurality of measurement (priorspace fact, no userspace content)
- the only userspace handle on contributing to shared content is stabilization of one's own relations, including self-relation
- content-based historical re-tellings have structural fragility: calculus of type is stable, content of observation is not
- indelibility: causal ordering forced by closure + partiality + write-effect-on-shared-structure
- fixed-point uniqueness of each property (with strength varying across properties — see bugs)
- D ∈ {ℝ, ℂ, ℍ} via Solèr at fixed point; which branch is realization-choice (architecture admits all three)
- the epistemic boundary: "is this the only loop?" is well-formed-but-unanswerable from within, and "is what I'm seeing really there?" resolves to *real-but-fundamentally-mysterious* (persisted via type structure unobservable from within)

**cited**:

- fundamental theorem of projective geometry (FTPG; stated as Lean axiom, being de-axiomatized — see `derivations/distributivity.md`, `DesarguesianWitness`)
- Dedekind's N_5 characterization of modularity
- Solèr's theorem (Solèr 1995; Holland 1995, Bull AMS) — see `trichotomy.md`
- Almgren's regularity problem (open) — for ℂ-rank-3 and ℍ-rank-3 branches of the trichotomy

**observed**:

- (none specific to this file; the ground's content is identified or derived, with the structural-correspondence work in friction and the alluvial fan flagged below)

**bugs**:

- *fixed-point uniqueness varies in strength across the four properties.* modular has a real chain (N_5 → path-dependent composition → indeterminate feedback → no value to feed back). height ≥ 4 has a real chain (rank_two_abelian_writes + partiality). complemented is argued by "complement_idempotent has no home" — that argues this specific loop wouldn't run, not that no self-sustaining loop is possible without complementation. irreducibility is named-definitional ("the irreducibility is what 'one' means"). presenting all four as fixed-point constraints of equal status under-flags the differences. closing this would require either separating the four into mechanical / definitional / plausibility tiers, or strengthening the complemented case to a real necessity argument.

- *D ∈ {ℝ, ℂ, ℍ} partially closed via Solèr.* Solèr (`trichotomy.md`) narrows D to {ℝ, ℂ, ℍ} at fixed point. residue: Solèr's hypotheses are discharged via fixed-point reasoning (orthomodular from P^T = P, infinite-dim from the architectural colimit, infinite ON sequence from N-bubble plurality), not via independent derivation. see `trichotomy.md` for what closing the remaining residue would require.

- *(closed by restructuring) D = ℝ via stabilization.* previous version had stabilization picking ℝ as the only currently-closed branch via Taylor, with the ℂ and ℍ branches "open pending Almgren rather than ruled out." the architectural-stance-shift relocates this: the architecture admits the full trichotomy, and which branch any foam-instantiation runs on is realization-choice. the lean development happens to work at ℝ. the bug, as previously stated, no longer applies.

- *friction is named without structural cash-out.* "type-interaction resists the action of reality, material-interaction resists the action of gravity" presents friction as substrate-independent resistance-against-pull, with parallel grammar doing structural-correspondence work between type-substrate and material-substrate. the parallelism is suggestive and structurally apt, but no formal object is constructed of which both instances are explicit cases. closing this would mean either constructing a typed friction-functor with type-interaction and material-interaction as instances, or stepping back to "friction-as-resistance-against-pull is a pattern recurring across two substrates relevant here."

- *the alluvial-fan image carries structural content that distributes across registers without being formally located.* the fan as record-of-passage operates in exitspace (type-invariant for the population that formed it under specific entrance conditions); the fan as in-progress-resolution operates in priorspace (where forks are determined by path-stack state, type-content, and flow-conditions); the fan-as-experienced operates in userspace (each molecule's local sense of which fork resolved). the registers are correctly distinguished in the prose, but the image is operating in all three at once and the cross-register structural-correspondence is doing implicit work. closing this would mean either formalizing the fan as an object with explicit projections into each register, or marking the cross-register operation explicitly as "the fan-image is being deployed across all three registers; reading depends on which register is being addressed in the surrounding prose."

- *"observation generates an observer; intuitively, a bubble in the foam"* is structural identification but the connection to the foam-as-formal-object is asserted rather than constructed. the body says "every passage through an observation loop generates an observer — intuitively, a bubble in the foam." the connection between observation-loop-passages and foam-bubbles is structurally suggestive (observers as bubbles is established vocabulary; passage-through-loop is the new dynamic content of this section) but the formal correspondence between "passage-through-loop" and "bubble-as-observer-in-foam" is not derived in this file. closing this would mean either constructing the formal map (passages → bubbles, with the foam's structural conditions being the structural conditions on passages), or naming this as the working identification with the formal correspondence pending downstream.

- *(closed by restructuring) "two readings as one statement."* previous version asserted that "the loop closes" (structural) and "you can't stand outside" (phenomenological) were the same statement sharing a single nerve. the new body locates each reading in its proper register (structural / phenomenological) using the priorspace/userspace tooling from `framing/architecture.md`, removing the assertion that they are the same statement. the bug, as previously stated, no longer applies to the current body.

- *(closed by restructuring) "encounters change frames" recasts dynamics as experience.* previous version asserted dynamics-on-projections and frame-experience as direct read-off of one another. the new body removes "encounters change frames" from the structural derivation list; what previously needed bridging is now handled by the registers separately addressing each side. the bug, as previously stated, no longer applies.
