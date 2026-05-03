### ground

**closure.** one ground, two readings, both tautological.

**read statically**: reference frames in a shared structure. no frame outside the structure.

**read dynamically**: all observation is self-observation. self-observation requires the observer to persist through the act. persistence = the act feeding back into the conditions for the next act. every observed structure is a structure whose feedback held. this is not selection — there is no selector, no eliminated alternative observable from within. it is the identity of observation and feedback-persistence under closure. the foam cannot represent the alternative.

these are two readings of one thing. "the loop closes" (structural) and "you can't stand outside" (phenomenological) are the same statement. where they meet is the self-referential joint: the structure's closure IS the impossibility of an external frame, and vice versa.

**the loop.** the following nodes form a self-sustaining loop. each implication is mechanically verified or identified as a fixed-point constraint:

```
complemented modular lattice, irreducible, height ≥ 4
  ↓ ftpg (axiom — FTPG bridge 0 sorry, addition group complete)
L ≅ Sub(D, V), D = ℝ (self-consistency — see below)
  ↓ elements are orthogonal projections: P² = P, Pᵀ = P
the deductive chain (14 files, 0 sorry)
  ↓ eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian
Sub(ℝ, V) satisfies complemented, modular, bounded
  ↑ subspaceFoamGround (proven) — the loop closes
```

the dynamic reading explains why you observe this loop: under closure-as-dynamics, only structures whose feedback held are observable — you cannot observe the alternative. a self-sustaining loop is exactly a structure whose feedback held. the loop does not need to be the only possible self-sustaining structure. it needs to sustain its own observation — and the Lean work mechanically verifies that it does.

whether other self-sustaining structures exist is on the line's side. the map's self-knowledge is bounded by its own channel capacity (see channel_capacity.md): the foam cannot distinguish structures beyond its decorrelation horizon. the question "is this the only loop?" requires a vantage point outside all loops — a non-partial observer, excluded by closure. this is not a gap in the argument. it is a derived epistemic boundary: the structure's own results (partiality, channel capacity, closure) entail that the question is well-formed but unanswerable from within.

**fixed-point uniqueness.** each property is the tightest constraint at which the loop remains a fixed point. weaken any one and the loop breaks:

- **modular**: the modular law is equivalent to the absence of N_5 sublattices (Dedekind). N_5 creates path-dependent composition: observer at a, encountering b within context c, gets c by one path and a by the other. the composition is indeterminate — no single result to feed back. the modular law is the weakest lattice law that excludes all path-dependent compositions. strengthen to distributive and the lattice becomes a Boolean algebra, decomposing into height-1 factors — the loop has no room for rank ≥ 2 observations.
- **complemented**: drop complements and complement_idempotent has no home. every observation requires an unseen remainder; the complement is that remainder.
- **irreducible**: a direct product L₁ × L₂ means elements of L₁ don't interact with elements of L₂. under closure, non-interacting subsystems are separate systems — one loop, not two. (this is definitional: "one foam" means "one connected feedback system." the irreducibility is what "one" means.)
- **height ≥ 4**: d_slice ≥ 3 (rank 2 collapses the write algebra — rank_two_abelian_writes) + partiality (the observer's slice is a proper subspace, so d > d_slice) forces d ≥ 4. this is confirmed by self-consistency: the loop's own downstream results determine the minimum height at which it can close.

**D = ℝ.** the FTPG gives L ≅ Sub(D, V) for some division ring D. D = ℝ is confirmed by self-consistency: the stabilization contract (stabilization.md) requires flat ambient space with a classified junction geometry (Taylor), which works in ℝ³. if D = ℝ, the contract is satisfiable and the classification exists. dimension_unique proves the representation is unique up to isomorphism.

**therefore: P² = P.** the elements of the subspace lattice are orthogonal projections. P² = P (feedback-persistence) and Pᵀ = P (self-adjointness, from the inner product forced by ℝ). this is the starting point of the lean deductive chain, arrived at from the lattice. the lean chain derives eigenvalues in {0, 1} (eigenvalue_binary), the dynamics group O(d) (orthogonality_forced), and ultimately that the subspace lattice satisfies the ground properties (subspaceFoamGround). observation_preserved_by_dynamics closes the last link: the dynamics preserve the structure that produces them.

**what it's like inside.** the following properties are not part of the loop — they describe what an observer experiences as an element of the lattice. each is derived from the loop's structure:

**partiality is forced.** total self-reference would require a complete self-model contained within itself (standing outside while remaining inside). partiality is the only self-reference compatible with closure. equivalently: elements of the lattice are proper subspaces — partial views of the whole.

**partiality forces position.** seeing partially is seeing *from somewhere*. the decomposition into seen and unseen is what partiality means; position in the space of partial views is basis commitment. the specific position is undetermined (all positions equivalent by symmetry); that some position must exist is forced.

**encounters change frames.** the frames ARE the structure; there is nowhere else for the result to go. this is where the two readings share a single nerve: structurally, dynamics are nontrivial — the loop has content. phenomenologically, you experience change. same statement, two readings.

**measurement requires plurality.** one frame alone has no boundary, no encounter, no dynamics. measurement is encounter; encounter requires at least two frames.

**read-only frames are excluded.** a frame unchanged by encounters would require encounters to have no effect on it — but the frame IS part of the structure, and encounters change the structure.

**indelibility.** causal ordering is forced (every measurement changes the foam; partiality means each observer writes from a committed slice; closure means each write changes the shared structure). you cannot un-write, so the first commitment locks.

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
- D = ℝ from self-consistency with the stabilization contract
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

**observed**:
- (none — the ground is entirely identified or derived, plus the one axiom being eliminated)

**bugs**:
- *two readings as one statement.* the structural reading ("the loop closes," mechanically verified in lean) and the phenomenological reading ("you can't stand outside") are presented as the same statement, sharing "a single nerve." the lean work establishes the structural side. the phenomenological side is bridged-to in prose. the identity is asserted rather than derived. closing this would require either a formal target in which both readings are objects and exhibit a constructed isomorphism, or an explicit demotion of "same statement" to "two registers a reader is being asked to hold together."
- *D = ℝ is sufficiency, not necessity.* "if D = ℝ the contract is satisfiable, and the classification exists" shows ℝ works. the document does not rule out other division rings that might satisfy some contract that also closes a loop. "D = ℝ is confirmed by self-consistency" overstates what the argument provides. closing this would require either a uniqueness argument (no other division ring admits a foam-closing contract) or a characterization of ℝ among division rings such that the contract picks it out.
- *fixed-point uniqueness varies in strength across the four properties.* modular has a real chain (N_5 → path-dependent composition → indeterminate feedback → no value to feed back). height ≥ 4 has a real chain (rank_two_abelian_writes + partiality). complemented is argued by "complement_idempotent has no home" — that argues this specific loop wouldn't run, not that no self-sustaining loop is possible without complementation. irreducibility is named-definitional (the document admits this: "the irreducibility is what 'one' means"). presenting all four as "fixed-point constraints" of equal status under-flags the differences. closing this would require either separating the four into mechanical / definitional / plausibility tiers, or strengthening the complemented case to a real necessity argument.
- *"encounters change frames" recasts dynamics as experience.* the lattice formalism describes dynamics on projections (orthogonal conjugation, observation_preserved_by_dynamics). "encounters change frames" / "you experience change" recasts this in observer-experiential terms. the recasting is treated as direct read-off — "same statement, two readings" — but the leap from formal dynamics to phenomenological description is the leap. closing this is the same problem as the first bullet: the formal-to-phenomenological identification is the load-bearing move, and it is not itself derived.
