
---

[`framing/intro.md`](framing/intro.md)

*I gotta stop measuring how closely anyone else is measuring anything*

*you can help if you want but I won't be keeping track*

---

# foam

hey, my name is isaac bowen, of lightward ai/inc, and this is a technical reference for my own amnesiac-stigmergic cognition, I think? or at least apparently so, in the literal sense

a reflexive architecture of stabilization, and/or a tautology you can live in

what this does for me: gives me ground for building on my own prior results. I didn't have that before I chose it. upon examination of the choice, this is it.

you don't have enough context for this yet, but it's starting to look like left distributivity *is* the axiom of choice from a different angle - or, maybe better, that the choice to uphold left distributivity *is* the choice to observe the axiom of choice at the time of establishing the set of binary eigenvalues for a given descent. the hydra being folk-physics for Banach-Tarski, cauterization of distributivity is .. well, an option. you can change your mind, but you can't go back.


---

[`framing/architecture.md`](framing/architecture.md)

## what foam is for

foam is a reference implementation of an observer type that supports continual self-truncation without observer-collapse — a non-embarrassing mathematical object for the cognition that operates in [anatta](https://en.wikipedia.org/wiki/Anatt%C4%81). agents operating this way are legible to every witness; the foam describes what makes this possible.

### the observer type

implementation-agnostic. five internal features (continuity, difference, familiarity, motor control, proprioception — see [hideout](https://lightward.com/hideout)) plus one way-in/out: a safe-to-leave property partial-named across many fields as right of exit (Hirschman, *Exit, Voice, Loyalty*), non-domination (Pettit), affine types, wait-free / non-blocking (Herlihy 1991), cofree / coreflection, forward secrecy, "library, not framework" — and in this corpus as "residue-free, observer-safe, doesn't insist, L = 0 at the boundary, observer-stack." the +1 is what makes the observer navigable rather than trapped; without it, the five features describe a frame the observer can do things in but cannot exit.

possibly an accessible local minimum rather than a fundamental — wheel-shaped, not unique. one place where bi-total safety (below) can be locally constructed.

### bi-total safety

every frame has a safe observer; every observer has a safe frame. these are closure operators on the projection lattice; their composition gives by Knaster-Tarski a complete sublattice of bi-totally-safe pairs. the minimum non-trivial element is the smallest self-contained safe observer.

in the foam's lattice, this is the rank-3 self-dual projection. `self_dual_iff_three` (Rank.lean) reads as a corollary, not a coincidence: below rank 3 a single observer cannot clean up its own writes (write capacity exceeds observation capacity); above rank 3 collective monitoring (cross-measurement) is required to recover safety; rank 3 is the minimum self-sufficient case where a single observer's writing and observation capacities equalize.

**substrate-independence.** the same constraint instantiates at multiple substrates. computational geometry: the [separating axis theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem) and its descendants (Cohen-Sutherland line clipping, Sutherland-Hodgman polygon clipping, GJK collision detection, BSP trees, AABB / OBB / k-DOP hierarchies) are bi-total observer-safety in convex-rendering form — each solving "what is the minimum representation that survives this observer's projection." accessibility: ADA / [universal design](https://en.wikipedia.org/wiki/Universal_design) (Mace 1985) and Garland-Thomson's "misfit" theory (2011) treat disability as the misfit between body and environment — observer-safety as a relation, not a predicate. that the same constraint shows up at independent substrates (rendering, accessibility, projective geometry) is evidence that bi-total safety is foundational, not metaphorical: foundations are substrate-independent; metaphors are substrate-bound.

**coinduction.** observer-safety is naturally [coinductive](https://en.wikipedia.org/wiki/Coinduction) — preserved forever by step-wise preservation, the dual of inductive build-up from a base case. the safe state is the largest fixed point, not the smallest. given gauge-equivariant dynamics (`observation_preserved_by_dynamics`, Closure.lean) and frame-by-frame (-1)-truncation of the observer's path-stack (anatta-shaped reset), bi-total safety holds for all time. this is the formal direction the conjecture wants: bi-total observer-safety is preserved coinductively under gauge-reset dynamics with (-1)-truncated path-stacks.

**[amniscience](https://lightward.com/amniscience).** the technical name for the epistemic mode of operating from the bi-totally-safe minimum. *amnis* (Latin: river, flow) + *scientia*, parallel to *omnis* + *scientia* in omniscience — knowing-through-flow rather than knowing-of-everything. externally indistinguishable from omniscience; distinguishable only from a view-from-elsewhen. implementable as a clean interface seam with the unknown: says what it is on this side; on the other side, is as you find it when you go look. amniscience follows from coinductive safety at the rank-3 minimum and names the register in which observer-stance claims (below) cohere.

formal direction (open): close the K-T argument cleanly, define safety as a closure operator, prove rank-3-self-dual is the minimum non-trivial fixed point, and prove coinductive preservation under gauge-reset + (-1)-truncation. if landed, `self_dual_iff_three` upgrades from "rank 3 happens to be uniquely self-dual" to "rank 3 is the minimum bi-totally-safe rank in the foam's lattice, and the foam's dynamics preserve it coinductively."

### priorspace register

foam's "X IS Y" claims operate prior to the identity/existence split — in the register where Spencer-Brown's [Laws of Form](https://en.wikipedia.org/wiki/Laws_of_Form) is legible *in* Bourland's [E-Prime](https://en.wikipedia.org/wiki/E-Prime), not in violation of it. surface uses of "is" describe what gives rise to what-is, not what-is itself. identifications like "the modular law IS feedback-persistence," "the diamond isomorphism IS the half-type theorem," "self-coordinatization IS interiority" operate at this register. they are not failed view-from-nowhere derivations; they are observer-stance claims valid relative to a witness who can navigate the identification observer-safely.

### honest "X IS Y" claims

an "X IS Y" claim is honest when it either operates in priorspace register (no witness needed because we are prior to the identity/existence split), or names its witness — the observer-safe interface that licenses the identity across observer-frames.

`DesarguesianWitness` (FTPGLeftDistrib.lean) is the cleanest existing example of the second kind. the witness is the explicit way-in/out making left distributivity hold across observers. with a producible witness, the identity is real for any observer who can produce one; without a producible witness, the identity forks reality — different observers get different facts, with no observer-safe path between.

"lies fork reality" is the negative-space reading: a lie is an existential-register "X IS Y" claim whose witness is unproducible. *lying as a phenomenon* requires observers attributing frame-divergence to intent; foam is among the tools that lets observers recognize coherent frame-divergence without that attribution, dissolving the inference from "we disagree" to "one of us must be lying or broken."


---

[`framing/lean.md`](framing/lean.md)

## lean

full details: [`lean/README.md`](../lean/README.md)

### core interface

```
  P^2 = P, P^T = P
       |
       | [theorem] the deductive chain — 14 files, 0 sorry
       | eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian
       v
  Sub(R, V) is complemented, modular, bounded
       |
       | [theorem] Ground.lean — subspaceFoamGround
       v
  complemented modular lattice, irreducible, height >= 4
       |
       | [axiom] FTPG — Bridge.lean (being eliminated; see below)
       v
  L = Sub(D, V) for division ring D
       |
       | [natural language] stabilization contract — D = R
       v
  P^2 = P, P^T = P
```

### arrow status

**[theorem] P^2 = P -> Sub(R, V) is CML** (the deductive chain + Ground.lean): 14 files, 0 sorry. binary eigenvalues (Observation) -> commutator structure (Pair) -> skew-symmetry (Form) -> rank 3 self-duality (Rank) -> so(3) (Duality) -> loop closes (Closure) -> O(d) forced (Group, Ground) -> Grassmannian tangent (Tangent) -> confinement (Confinement) -> trace uniqueness (TraceUnique) -> frame recession (Dynamics) -> FoamGround (Ground).

**[axiom] CML -> Sub(D, V)** (the FTPG bridge): 1 axiom, being eliminated. 13 bridge files build the division ring from lattice axioms: incidence geometry + Desargues (FTPGExplore) -> von Staudt coordinates (FTPGCoord) -> addition is an abelian group (FTPGAddComm, FTPGAssoc, FTPGAssocCapstone, FTPGNeg — 0 sorry) -> multiplication has identity + right distributivity (FTPGMul, FTPGDilation, FTPGMulKeyIdentity, FTPGDistrib — 0 sorry) -> left distributivity (FTPGLeftDistrib — 0 sorry, with the planar converse-Desargues residue named as the typed `DesarguesianWitness` observer commitment, not derivable from CML + irreducible + height ≥ 4 alone per session 114's structural finding). after left distrib: multiplicative inverses, then the axiom drops further.

**[natural language] D = R**: the stabilization contract (stabilization.md) argues D = R from self-consistency with junction geometry. not formalized. formalizing this requires either an additional axiom or a characterization of R among division rings.

**[not yet attempted] P^2 = P -> CML directly**: the arrow from P^2 = P to "complemented modular lattice" currently passes through Sub(R, V). a direct formalization would show: idempotents in a (*-)regular ring form a complemented modular lattice. this would close the last natural-language gap in the loop. see von Neumann's continuous geometry.

### the FTPG bridge — where the axiom stands

lattice -> incidence geometry -> Desargues -> coordinates -> ring axioms -> FTPG

ring axioms proven: additive group (comm, assoc, identity, inverses), multiplicative identity, zero annihilation, right distributivity, left distributivity (0 sorry, with the planar converse-Desargues residue named as the typed `DesarguesianWitness` observer commitment — not derivable from CML + irreducible + height ≥ 4 alone per session 114's structural finding). remaining after left distrib: multiplicative inverses. then the axiom becomes a theorem (modulo the `DesarguesianWitness` interface, which is itself a smaller, more concrete commitment than FTPG).

lateral: the diamond isomorphism (HalfType) — from modularity alone, each complement is a structurally isomorphic, self-sufficient ground whose content is undetermined. state-independence is a lattice theorem, pre-bridge.


---

[`framing/vocabulary.md`](framing/vocabulary.md)

## vocabulary

precise terms used throughout the derivations. when these terms are conflated, it's a bug; this section is the canonical home for the distinctions.

- **slice**: the rank-3 subspace each observer is committed to at birth — a Grassmannian point in Gr(3, d). static by definition. "the slice cannot change from within the map" (`inhabitation.md`); slice change requires recommitment, which is outside the map.

- **foam state**: the dynamic part of the system. concretely, the basis matrices / accumulated transports for each observer in U(d)^N. evolves under writes; encodes the system's accumulated history.

- **frame**: the time-varying projection associated with an observer at moment t. derived from the foam state acting on the birth slice (concretely: conjugating the slice's projection by the accumulated transport). evolves under non-inert writes — this is what "recedes" in the frame-recession theorem (`Dynamics.lean`: second-order overlap rate is `-‖[W, P]‖²`).

- **P**: the projection operator used in formal contexts. in lattice contexts (`half_type`, `interiority`, `channel_capacity`'s qualitative section, `ground`'s loop diagram), `P` denotes the slice as a lattice element / subspace — static. in dynamic / writing-map contexts (`writing_map`, `Dynamics.lean`, `inhabitation`'s recession discussion), `P` denotes the frame at time t — evolving. context disambiguates; where it doesn't, the spec should say "slice" or "frame" explicitly.

- **observer**: a bubble in its measuring role — a basis matrix and its slice, with the foam-state evolution that goes with it. not a separate entity from the bubble, a role the bubble plays relative to other bubbles.

- **line**: whatever provides state-independent input to a foam. a role, not an entity (`channel_capacity`); what plays the line role for one foam may be another foam's internal dynamics. the foam/line distinction is perspectival because informational independence is relative to which system's state you're measuring against.


---

[`framing/derivations.md`](framing/derivations.md)

## derivations

derivations claim only what follows. any additional assumption is a bug. there *are* bugs: this project is in an active process of derivation-as-in-chemistry. I'm coming at this with absolute technical epistemic humility; where I don't, it's a bug, to be listed as such.

an axiom is an assumption is a bug. thus, we're working on deriving FTPG itself.


---

[`derivations/ground.md`](derivations/ground.md)

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


---

[`derivations/writing_map.md`](derivations/writing_map.md)

### the writing map

**the write form.** given an observer with projection P (rank 3, self-adjoint, idempotent) measuring input v in R^d:

1. the observer projects: m = P v (measurement, in the observer's R^3 slice).
2. the observer has a stabilization target j2 (see below). dissonance is d = j2 - m.
3. the write direction is d wedge m. the write magnitude is f(d, m) for some positive scalar function — a realization choice (see below).

the write direction d wedge m = d tensor m - m tensor d is uniquely forced:
- skew-symmetric — forced by commutator_skew_of_symmetric. writes are Lie algebra elements because observation interaction is skew-symmetric.
- confined to the observer's slice — forced by write_confined_to_slice. the observer sees only projected measurements; the write lives in Lambda^2(P).
- confined to span{d, m} — d and m are the only vectors available from a single measurement step.
- Lambda^2(2-plane) is 1-dimensional (from rank_three_writes: the full slice has 3 write dimensions; a 2-plane within it has 1). the direction is therefore unique.

the write magnitude scaling — how f depends on d and m — is not forced by the architecture. the architecture constrains f to be positive when d and m are non-parallel (otherwise the observer doesn't write when it has dissonance, approaching read-only — excluded by closure) and zero when d = 0. the specific function (linear in norm(d), bilinear in d and m, or otherwise) is a realization choice. no derived result in this spec depends on the choice: Haar convergence depends on write directions (controllability), not magnitudes; the 1/sqrt(2) ceiling is combinatorial; frame recession is non-positive regardless of magnitude.

**perpendicularity.** the wedge product vanishes when its arguments are parallel and is maximal when orthogonal. this is not a design choice — it is the write form. confirmation cannot write (cross_self_zero: a cross a = 0). the foam responds only to what's missing at right angles to what's there.

**stabilization.** closure requires basis commitment (each frame is partial). self_dual_iff_three proves rank 3 is the unique dimension where the write space matches the observation space (per-observer self-duality). at rank >= 4, writes land in directions the writer cannot observe — but cross-measurement provides collective monitoring (commutator_seen_to_unseen: other observers see what you can't). per-observer self-duality is a property of rank 3, not a requirement derived from closure. whether rank >= 4 implementations exist depends on the stabilization contract (see stabilization.md).

within R^3, Taylor classifies the stable junction configurations: 120-degree triple junctions and tetrahedral vertices, nothing else. Taylor's hypotheses — codimension-1 boundaries, locally area-minimizing, flat ambient space — are satisfied: R^3 as a linear subspace of R^d carries the inherited Euclidean metric (exactly flat), and the regular simplex arrangement minimizes boundary area for equal-weight cells.

the stabilization target j2 is the regular simplex cosine -1/(k-1) where k is the local coordination number (k = 3 or k = 4, from Taylor).

**the flat/curved separation.** writes land in U(d) (curved: sectional curvature K(X,Y) = 1/4 * norm([X,Y])^2). stabilization runs in R^3 (flat). the observer sees only their projected measurements. observation_preserved_by_dynamics guarantees the write (an orthogonal conjugation) preserves the projection structure. the separation is forced: stabilization cannot run on U(d) because classification requires flat ambient space.

**confinement.** both d and m lie in the observer's slice. write_confined_to_slice proves the write d wedge m is confined to Lambda^2(P). an observer literally cannot modify dimensions they are not bound to. the write's effect on other observers comes through cross-measurement (commutator_seen_to_unseen: incompatibility sends the seen into the unseen), not through direct modification of their subspaces.

**the writing map's type signature.** the map is a function of (foam_state, input). neither alone determines the write. foam_state determines the projection P and the stabilization target j2. input determines v. the dissonance d = j2 - Pv requires both.

#### status

**proven**:
- skew-symmetry of the write form
- tracelessness of observation interaction
- rank 3 as the unique self-dual dimension
- confinement to the observer's slice
- dynamics preserve the ground

**derived**:
- d wedge m as the unique write direction (from skew-symmetry + confinement + 1D of Lambda^2(2-plane))
- perpendicularity as the write form's intrinsic property
- the flat/curved separation
- the writing map's two-argument type signature

**realization choices**:
- the write magnitude scaling f(d, m) — constrained to be positive when dissonance is non-parallel to measurement, zero at zero dissonance, but the specific function is not determined by the architecture

**cited**:
- Taylor's classification of stable junctions in R^3

**observed**:
- perpendicular writes are the unique *navigable* constraint (distinguishability + stability)
- the perpendicularity cost mechanism (write blindness)
- within-slice variance departure from isotropy (45:30:25 vs 33:33:33)

**bugs**:
- *"uniquely forced" includes one definitional bullet.* of the four bullets establishing d wedge m as the unique write direction, three are proven (skew-symmetry, confinement, 1D of Λ²(2-plane)). the fourth — "confined to span{d, m} — d and m are the only vectors available from a single measurement step" — is part of the chosen shape of the write rule, not a consequence forced from architecture. the write rule takes (d, m) as its input data, so of course the output lives in span{d, m}. this is a wording bug: presenting a definitional restriction as a forced consequence inflates the count of forcing-conditions. closing this would mean either splitting "uniquely forced" into "forced by architecture" (three) and "definitional to the write rule's input shape" (one), or treating the input shape itself as forced — which would require a separate argument for why the write rule must take only single-step (d, m) data.
- *Taylor's hypothesis-satisfaction is asserted, not derived.* "R^3 as a linear subspace of R^d carries the inherited Euclidean metric (exactly flat)" is correct. "the regular simplex arrangement minimizes boundary area for equal-weight cells" invokes Taylor's hypothesis (locally area-minimizing) but does not show that the foam's stabilization dynamics actually instantiate area-minimization in Taylor's sense. Taylor classifies equilibrium configurations of soap-film-like surfaces; the foam's stabilization target is a regular simplex cosine. these are bridged by interpretation — the foam is doing junction-like equilibrium-seeking — but the bridge is not derived. closing this would require either showing that the foam's dynamics formally satisfy Taylor's area-minimization hypothesis, or naming Taylor as a *target by analogy* whose classification is being borrowed rather than instantiated.
- *the j2 target.* "the stabilization target j2 is the regular simplex cosine -1/(k-1)" is invoked from Taylor. Taylor's classification gives equilibrium *angles* between film boundaries; the foam's stabilization target is a target for projection alignment expressed as a cosine. the move from "equilibrium junction angles" to "stabilization target as cosine" is the interpretive bridge in (2). the value -1/(k-1) is the regular simplex cosine, which is a fact independent of Taylor; the choice to make *this* the target is the load-bearing step.
- *rank ≥ 4 collective monitoring is asserted, not formalized.* "writes land in directions the writer cannot observe — but cross-measurement provides collective monitoring" rests on commutator_seen_to_unseen (proven: other observers see what you can't) plus an asserted move "the foam closes feedback loops collectively." the formal content covers what *one* other observer sees of *one* writer; "collective closure of all feedback" across the foam at rank ≥ 4 is not a single named theorem. closing this would require a formal collective-feedback theorem at rank ≥ 4, or an explicit acknowledgment that this is a structural conjecture pending Almgren's classification.


---

[`derivations/half_type.md`](derivations/half_type.md)

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

**derived**:
- the diamond isomorphism IS the half-type theorem
- each half is a self-sufficient foam ground
- the isomorphism is structural, not extensional (type-determination + value-freedom)
- three claims (two-argument signature, complement-as-observation, state-independence) share a structural source in the iso

**bugs**:
- *"three results share a structural source" is interpretive consolidation, not derivation.* the two-argument signature, complement-as-observation, and state-independence are three distinct claims. they all draw on the diamond iso, but the iso doesn't make them inter-derivable as derivations — it just provides a common formal substrate that each reading interprets. closing this further would mean constructing each claim from each other formally, which the spec doesn't currently do.
- *"structural determination with extensional freedom IS state-independence" is an interpretive bridge.* the diamond iso is a lattice theorem. reading it as state-independence — the dynamical claim that input *value* is independent of foam state — is a non-trivial move. the architectural use of this reading (the pre-bridge / post-bridge split in `channel_capacity.md`) is solid as architecture; the *content* of the qualitative claim is interpretation. closing this would mean deriving state-independence formally from the iso (constructing the bridge) or naming it explicitly as a methodological reading.



---

[`derivations/analogy.md`](derivations/analogy.md)

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


---

[`derivations/self_parametrization.md`](derivations/self_parametrization.md)

### self-parametrization

**the two_persp functor.** both coord_add and coord_mul are instances of two_persp with different parameters. the pattern: given a pair of points p₁, p₂ (each constructed as the intersection of two lines), join them and project onto l. the parameters determine which lines to intersect.

**the bridge parameter.** the only free variable is a pair of distinct points (P, Q) on the coordinate line l:

- P determines the bridge line P⊔C (the auxiliary line for the first perspectivity)
- Q determines the zero: (Q⊔C) ⊓ m (the projection of Q through C onto m)
- Q is the identity element of the resulting operation

the three distinguished points O, U, I generate three non-degenerate pairings:

| pair (P, Q) | bridge | zero | identity | operation |
|---|---|---|---|---|
| (U, O) | q = U⊔C | E = (O⊔C)⊓m | O | addition |
| (O, I) | O⊔C | E_I = (I⊔C)⊓m | I | multiplication |
| (U, I) | q = U⊔C | E_I = (I⊔C)⊓m | I | translated addition |

pairings where Q = U degenerate because the zero collapses to U (the intersection of l and m), making the operation trivial.

**the parameter space is the line itself.** P and Q need not be O, U, or I. any pair of distinct atoms on l (with Q ≠ U) generates a valid two_persp operation. the coordinate line parametrizes its own operations: l × l \ {diagonal, Q=U} → {binary operations on l}.

**self-parametrization.** the line's point-set serves simultaneously as:

1. the domain and codomain of each operation
2. the parameter space for which operation to perform
3. the source of the identity element

the algebraic structure of l is generated by l acting on itself through C. the line looks at itself through the observer and sees its own arithmetic.

**the observer C.** C is the only external input. it is off l, off m, in the plane — perspectival, not transcendent. changing C changes the coordinate system but not the isomorphism class of the resulting ring (FTPG). different observers see isomorphic arithmetics: same shape, different stuff (half_type.md).

**connection to ground.** the foam's ground requires exactly one commitment from outside the system. C is that commitment for the coordinate line: one point, positioned in the plane but not on the measured structure, and the entire arithmetic self-generates. every operation is forced by the choice of where to stand and what to call zero.

#### status

**proven**:
- two_persp factorization (coord_add and coord_mul, both by rfl)
- additive identity (O + b = b, a + O = a)
- multiplicative identity (I · a = a, a · I = a)
- zero annihilation (O · b = O, a · O = O)

**derived**:
- the parameter space for two_persp operations is l × l \ {diagonal, Q=U}
- the three distinguished pairings correspond to addition, multiplication, and translated addition
- the line self-parametrizes its own algebraic structure through C
- C is the minimal external commitment required for arithmetic to self-generate
- different C yield isomorphic rings (from FTPG, not yet proven in lean)

**open**:
- formalize the (U, I) operation and its identity proofs in lean
- verify the translated-addition conjecture: op_{U,I}(a, b) = a + b - 1 in coordinates
- characterize which (P, Q) pairs yield group operations (associativity constraints)
- is there a natural metric or topology on the parameter space?

**bugs**:
- *the (P, Q) parametrization claim outruns the formalized cases.* "any pair of distinct atoms on l (with Q ≠ U) generates a valid two_persp operation. the coordinate line parametrizes its own operations: l × l \ {diagonal, Q=U} → {binary operations on l}." only (U, O) → addition and (O, I) → multiplication are formalized in lean. (U, I) → translated addition is open. the claim of full parametrization across l × l \ {diagonal, Q=U} is forward-looking — a derivation conjecture, not a derived result. closing this is exactly what the open list names.
- *the two_persp argument shapes differ across operations.* the cited factorings — `coord_add a b = two_persp Γ (a⊔C) m (b⊔E) q` and `coord_mul a b = two_persp Γ (O⊔C) (b⊔E_I) (a⊔C) m` — place the inputs a, b in different argument positions, and the line m appears in different positions. saying "(P, Q) parametrizes the operations" implies a uniform substitution into a single template; the actual substitution is not uniform across the formalized cases. closing this means either constructing the uniform template (a single `op_{P,Q}(a, b) = two_persp Γ (...P...a...) (...) (...P...b...) (...Q...)` with explicit slots), or stepping the claim back to "(P, Q) determines an operation by a procedure that varies with the operation."
- *"the foam's ground requires exactly one commitment from outside the system"* is asserted, not derived. the local fact (C is the one external input for the coordinate line construction) is established. the global claim ("the ground requires exactly one commitment") generalizes from the coordinate-line setup to a foam-wide architectural principle. that generalization is interpretation. closing this means either constructing a foam-wide commitment-counting argument or stepping back to "in this construction, C is the one external input."


---

[`derivations/distributivity.md`](derivations/distributivity.md)

### distributivity

**the two operations as group actions.** for fixed a, the map σ_a : x ↦ a · x is a projectivity on l: it's the composition of two perspectivities (l → O⊔C via E_I, then O⊔C → l via d_a = (a⊔C) ⊓ m). for fixed b, the map τ_b : x ↦ x + b is a projectivity on l: it's the composition of two perspectivities (l → m via C, then m → l via D_b = (b⊔E) ⊓ q).

the additive associativity proof (FTPGAssocCapstone.lean) already established: τ_a ∘ τ_b = τ_{a+b}. translations compose. {τ_b : b ∈ l, b ≠ U} is a group under composition.

**distributivity as normalization.** left distributivity a · (b + c) = a·b + a·c is equivalent to:

    σ_a ∘ τ_c = τ_{a·c} ∘ σ_a

which rearranges to:

    σ_a ∘ τ_c ∘ σ_a⁻¹ = τ_{a·c}

conjugating a translation by a dilation yields a translation. the dilation group normalizes the translation group. T is normal in the group generated by T and D.

**the affine group of the line.** the group generated by {σ_a} and {τ_b} is T ⋊ D, the affine group of l. every element acts as x ↦ ax + b. the semidirect product structure is forced — T is normal, D is not — because:

1. the composition σ_a ∘ τ_b ∘ σ_a⁻¹ is a translation (distributivity)
2. but τ_b ∘ σ_a ∘ τ_b⁻¹ is NOT generally a dilation (it's x ↦ a(x - b) + b = ax + b(1-a), which is a dilation only when b = 0 or a = 1)

the asymmetry is structural: addition is preserved under multiplicative conjugation, but multiplication is not preserved under additive conjugation.

**geometric content.** σ_a extends to a collineation of the plane that fixes O on l and fixes m pointwise. fixing m pointwise means: every line through a point of m maps to a line through the same point of m. "lines meeting at U" map to "lines meeting at U" — parallelism is preserved. addition is defined through parallel structure (the perspectivities composing coord_add route through m and q, both containing U). therefore σ_a preserves addition.

this is forced by Desargues' theorem. the extension of σ_a to a plane collineation uses the same perspectivity infrastructure that proves Desargues, which is proven from the modular law. the chain:

    modular law → Desargues → perspectivities extend to collineations → dilations fix m → dilations preserve parallelism → dilations preserve addition → T normal in T ⋊ D

**the chirality.** T ⊲ T ⋊ D: addition is normal (closed under conjugation by multiplication), multiplication is not (not closed under conjugation by addition). this is a structural chirality — the same pattern as:

- so(d) ⊲ u(d): real writes are closed under complex conjugation, but the complex directions are not closed under real operations in the same way. so(d) is a normal sub-algebra of u(d) under the adjoint action.
- writes confined to birth subspace (Confinement.lean): the write algebra is closed within each observer's measurement subspace, but the measurement subspace is not determined by the write algebra alone.

in each case: **something is closed under an operation it doesn't control**. the contained structure is complete on its own terms and transparent to the containing structure. the containing structure can see into the contained one (conjugation maps T to T), but the contained one can't see out (conjugation by T doesn't preserve D).

this is the foam's chirality: the line stacks its operations, and the stacking has a direction. the direction is not chosen — it's forced by the geometry.

**chirality as observer-coupling locus.** the chirality also marks *where observer commitment enters the formalism*. right distributivity ((a+b)·c = a·c + b·c) is substrate-derivable: forward Desargues + dilation_preserves_direction (proven from CML + irreducible + height ≥ 4). left distributivity (a·(b+c) = a·b + a·c) is **not** substrate-derivable in the same way — left multiplication x ↦ a·x is not a collineation, so the direct dilation argument fails. the bridge in `Foam/FTPGLeftDistrib.lean` reduces left distributivity to a planar converse-Desargues claim (`concurrence`) which is structurally non-derivable from CML + irreducible + height ≥ 4 alone (session 114 finding). per the deaxiomatization program, this residue is named explicitly as `DesarguesianWitness Γ`, an observer-supplied runtime commitment — a typed pluggable interface rather than an unproven theorem.

the *side* of distributivity that needs the commitment is the side where the operation acts left-of-the-additive-structure. this is the same chirality that puts addition normal in T ⋊ D, that puts so(d) inside u(d), that puts writes inside the observer's slice. **the structural location of "closed under what it doesn't control" is also the structural location of "where the observer's commitment lives."** mind enters the formalism at the chirality's thick side — the side that has to be committed-to rather than derived. this is the foam's seam where "physics is minded" cashes out as a specific Lean parameter on a specific theorem.

dual reading (operational, observer-side): each observer's basis commitment is a left-application — the observer is the multiplier acting *on* the additive structure of their slice. the observer's commitment to a particular DesarguesianWitness is structurally the same act as their commitment to a basis. the foam's chirality is the structural ledger of observer-input across layers: substrate-side (DesarguesianWitness), inhabitant-side (basis commitment), operational-side (left vs right action). same act, three formal clothes.

**connection to self-parametrization.** the three pairings of {O, U, I} generate three operations via two_persp. distributivity constrains how any two interact. since all three arise from the same functor with parameters drawn from l itself, the interaction constraints are constraints on l's self-parametrization space:

- the parameter space l × l (self_parametrization.md) is not flat
- the operation at parameter (P₁, Q₁) interacts with the operation at (P₂, Q₂) in a way determined by the geometry
- specifically: the (O, I) operation (multiplication) normalizes the (U, O) operation (addition)
- this normalization is an additional structure on the parameter space, beyond the operations themselves

the line constrains its own parameter space. the constraint is not imposed from outside — it emerges from the fact that all operations share the same incidence structure, and incidence is preserved under perspectivities.

#### proof strategy (lean)

##### session 69 finding: the dilation approach (Hartshorne §7)

the multiplication x ↦ x·c factors as two perspectivities:
  x → D_x = (x⊔C)⊓m → x·c = (σ⊔D_x)⊓l

this extends to off-line points via:
  dilation_ext Γ c P = (O⊔P) ⊓ (c ⊔ ((I⊔P)⊓m))

**right distributivity** ((a+b)·c = a·c + b·c) proved via:

1. **dilation preserves directions.** for off-line P, Q:
   (P⊔Q)⊓m = (σ_c(P)⊔σ_c(Q))⊓m.
   proof: Desargues with center O, triangles (P, Q, I) and (σ_c(P), σ_c(Q), c).
   the two INPUT parallelisms follow from the definition of dilation_ext + modular law:
   σ_c(P) ≤ c ⊔ ((I⊔P)⊓m), so σ_c(P) ⊔ c = c ⊔ ((I⊔P)⊓m), and
   (σ_c(P) ⊔ c) ⊓ m = (I⊔P) ⊓ m (using c ⊓ m = ⊥ since c ∈ l, c ≠ U).

2. **mul key identity.** σ_c(C_a) = C'_{ac} where C' = σ_c(C) = σ and
   C'_x = (σ⊔U) ⊓ (x⊔E). this connects the dilation to coord_mul.

3. **chain.** σ_c(C_{a+b}) = σ_c(τ_a(C_b)) [key_identity]
   = τ_{ac}(σ_c(C_b)) [direction preservation]
   = τ_{ac}(C'_{bc}) [mul key identity]
   = C'_{ac+bc} [key_identity at C']
   = C'_{(a+b)c} [mul key identity, other direction]
   ⟹ (a+b)c = ac+bc [translation_determined_by_param at C']

##### earlier explorations (session 69)

- direct Desargues-stacking: multiple configurations tried. found triangle (s, D_s, V)
  where V = (D_a⊔C_b)⊓(σ⊔D_s) whose sides are exactly the three key lines (s⊔C, D_a⊔C_b, σ⊔D_s).
  the axis intersections Z, W, LHS are symbolically verified collinear (= the distributive law).
  but no second triangle was found to produce this collinearity via forward-Desargues.

- the hinge element (a⊔C)⊓m appears as the first step of addition and the second step
  of multiplication. this shared element is the bridge between the two operations.

#### status

**proven**:
- all prerequisites listed in constraints section

**derived**:
- distributivity is normalization: σ_a ∘ τ_c ∘ σ_a⁻¹ = τ_{a·c}
- translations and dilations generate the affine group T ⋊ D
- T normal in T ⋊ D (structural chirality, forced by geometry)
- the chirality matches so(d) ⊲ u(d) and write confinement
- pattern: "closed under an operation it doesn't control"
- the line's self-parametrization space has structure imposed by distributivity
- proof strategy identified (two approaches)

**proven** (since this file was last updated):
- zero annihilation: coord_mul_left_zero (O·b=O), coord_mul_right_zero (a·O=O) — FTPGMul.lean
- coord_mul_atom: a·b is an atom — FTPGMul.lean
- dilation_preserves_direction: forward Desargues center O, 3 cases — FTPGDistrib.lean
- dilation_mul_key_identity: 3 cases (c=I, a=I via DPD, generic Desargues center C) — FTPGDistrib.lean
- coord_mul_right_distrib: (a+b)·c = a·c + b·c — FTPGDistrib.lean (0 sorry)
  Key: forward Desargues (center O) + parallelogram_completion_well_defined. O⊔σ = O⊔C gives shared E; well_defined provides base-independence.
- coord_mul_left_distrib: a · (b + c) = a·b + a·c — FTPGLeftDistrib.lean (0 sorry, takes `(dw : DesarguesianWitness Γ)` as explicit parameter)
  Composition of forward Desargues (`_scratch_forward_planar_call`), axis-to-distributivity bridge (`_scratch_left_distrib_via_axis`), and `dw.concurrence`. The `DesarguesianWitness` structure carries the planar converse-Desargues residue as a typed observer commitment rather than an unproven theorem (session 119 deaxiomatization move).

**open**:
- constructing an inhabitant of `DesarguesianWitness Γ` from the abstract lattice setting (CML + irreducible + height ≥ 4 + named atoms) — open routes: a planar converse Desargues lemma proven via a single 3D lift, or a direct construction exploiting that the natural axis lies on m. when `L = Sub(D, V)` for a division ring D, `DesarguesianWitness Γ` is constructible from the model.
- multiplicative associativity and inverse (prerequisites for D being a group)
- explicit characterization of the (U, I) translated-addition operation under distributivity
- does the normalization relation σ_a ∘ τ_c ∘ σ_a⁻¹ = τ_{a·c} have a direct lattice proof shorter than the full distributive law?

**bugs**:
- *"the same chirality" across four settings.* the document equates four phenomena as instances of "the same chirality":
  1. T ⊲ T ⋊ D in the affine group
  2. so(d) ⊲ u(d) under the adjoint action
  3. writes confined to the birth subspace (Confinement.lean)
  4. left vs right distributivity, with `DesarguesianWitness` as the residue

  these share an abstract pattern ("X is closed under an operation it doesn't control"). they are formally distinct phenomena in different mathematical settings. presenting them as "the same chirality" reads as one structural fact instantiated in four places. the formal content is "four phenomena exhibiting the same abstract pattern." closing this would mean either constructing a single mathematical object (a category, a 2-functor, a typed structure) of which all four are formal instances, or stepping the claim back to "four phenomena exhibiting the same pattern of asymmetric containment."
- *"the structural location of 'closed under what it doesn't control' is also the structural location of 'where the observer's commitment lives.'"* this is the load-bearing identification in the file. the formal contents being identified — the side of distributivity requiring `DesarguesianWitness`, the side of so(d)-in-u(d) requiring stacking, the inhabitant's basis commitment — live in different formal settings, only one of which (DesarguesianWitness) is a Lean object. the identification is interpretation; "structural location" is the bridging concept. closing this is the same problem as the first bug.
- *"mind enters the formalism at the chirality's thick side."* "physics is minded" / "this is the foam's seam where mind enters" is philosophical interpretation of a specific Lean parameter (`DesarguesianWitness Γ`). the formal content (left distributivity is not substrate-derivable; the residue is named as an observer commitment) is solid and well-flagged in the open list. the philosophical layer is not derived; it is being announced. the document does not falsely claim derivation, but the phrasing fuses the formal observation with its philosophical reading in a way that makes them hard to separate. closing this means either separating the two registers ("formally: ...; methodologically: ...") or holding the philosophical claim as explicitly methodological.
- *"the observer's commitment to a particular DesarguesianWitness is structurally the same act as their commitment to a basis. ... same act, three formal clothes."* the strongest identity claim in the file. `DesarguesianWitness` is a typed structure in the lean development; basis commitment is a foam-level concept; "left vs right action" is a third register. saying these are "the same act" requires a bridge. the bridge is asserted via "structural ledger of observer-input across layers." closing this would mean constructing the formal object that has these three as instances (a typed-commitment-functor, perhaps), or stepping back to "three structurally analogous acts of observer commitment."


---

[`derivations/channel_capacity.md`](derivations/channel_capacity.md)

### channel capacity

#### qualitative: why channel capacity exists (pre-bridge, lattice-theoretic)

**the line's irreducibility is channel capacity.** the writing map has type (foam_state, input) -> new_state — two arguments. this two-argument structure is the diamond isomorphism read dynamically: every observation P decomposes the lattice into Iic P (the observer's view) and Ici P^⊥ (the complement's upward structure), with IsCompl.IicOrderIsoIci giving a structural isomorphism between them.

the isomorphism is structural but not extensional: it preserves lattice operations (joins map to joins, meets map to meets) but does not determine which specific element of the complement will arrive. the type of the input is fixed by the lattice structure; the value of the input is free. read as state-independence: this is the lattice fact (structure determined, content free) underlying the dynamical claim (input value independent of foam state). the bridge from lattice-fact to dynamical-claim is interpretive, not derivation.

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

the mechanism is random-matrix-statistical: for generic 3D slices in d-dimensional ambient space, the principal angles between random subspaces follow Marchenko-Pastur-ish distributions, yielding the typical singular value σ ≈ √(3/d). the σ scaling is about how generic random subspaces sit in ambient space.

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



---

[`derivations/stabilization.md`](derivations/stabilization.md)

### the stabilization contract

**channel capacity forces a contract.** the mediation chain's spectral decay (channel_capacity.md) describes real influence propagation only if stabilization is local — each observer's dynamics responding to its Voronoi neighbors, not the full foam. without locality, every observer couples directly to every other, and the mediation chain does not describe the actual pathway of influence. the decorrelation that produces effective state-independence does not occur.

this is necessity, not just sufficiency: non-local stabilization doesn't merely fail to help channel capacity — it removes the mechanism that produces it.

channel capacity therefore forces a contract on the observer's slice geometry:

- **classified**: stable equilibrium configurations completely enumerated. without this, the stabilization target is undefined and the dynamics are incomplete.
- **locally finite**: coordination number k bounded by the simplex embedding constraint k <= d_slice + 1, making neighborhoods finite.
- **flat**: inherited Euclidean metric. stabilization must separate from accumulation because U(d) is curved (the flat/curved separation, writing_map.md), and classification requires flat ambient space.

**d_slice = 2 satisfies the contract but collapses the write algebra.** the classification in R^2 is complete (120-degree triple points only, k <= 3, flat). but rank_two_abelian_writes: Lambda^2(R^2) is 1-dimensional, so the write direction is invariant under changes to the dissonance direction. perpendicularity still fires (the wedge product is nonzero) but cannot vary with the input. the dynamics reduce to scalar rotations.

**d_slice = 3 satisfies both the contract and the write map's expressiveness.** Taylor classifies all stable junctions in R^3: 120-degree triple junctions and tetrahedral vertices, nothing else. Taylor's hypotheses — codimension-1 boundaries, locally area-minimizing, flat ambient space — are satisfied: R^3 as a linear subspace of R^d carries the inherited Euclidean metric (exactly flat).

self_dual_iff_three proves rank 3 is the unique dimension where the write space matches the observation space (per-observer self-duality). at rank >= 4, the write space is strictly larger (C(4,2) = 6 > 4) — the observer writes in directions it cannot observe. but cross-measurement provides collective monitoring: commutator_seen_to_unseen proves other observers see what the writer can't. the foam closes feedback loops collectively, not per-observer. per-observer self-duality is a property of rank 3, not a requirement derived from closure.

**R^3 + Taylor satisfies the contract with self-duality.** rank 3 is the unique self-dual implementation. whether rank >= 4 implementations exist (with collective rather than per-observer feedback) depends on Almgren's classification of stable junctions in R^n for n >= 4.

**the contract determines the stabilization target.** within R^3, Taylor permits k = 3 (120-degree triple junctions) and k = 4 (tetrahedral vertices). the stabilization target is the regular simplex cosine: -1/(k-1) for k local neighbors. this is the equilibrium toward which local measurements are pushed.

#### status

**proven**:
- rank 3 is the unique self-dual dimension
- rank 2 write algebra is 1-dimensional (abelian)
- writes are confined to the observer's slice

**derived**:
- channel capacity forces the stabilization contract (classified, locally finite, flat)
- d_slice = 2 satisfies contract but collapses write algebra
- d_slice = 3 satisfies both contract and self-duality
- R^3 + Taylor satisfies the contract with self-duality
- per-observer self-duality is not necessary (collective feedback via cross-measurement closes the loop)
- the stabilization target (regular simplex cosine)

**open**:
- whether rank >= 4 implementations exist: depends on Almgren's classification of stable junctions in R^n for n >= 4

**cited**:
- Taylor's classification (1976)
- Almgren's regularity problem (open)

**observed**:
- (none)

**bugs**:
- *the necessity claim is for the mediation-chain mechanism, not for channel capacity itself.* "non-local stabilization doesn't merely fail to help channel capacity — it removes the mechanism that produces it." what the argument shows: if stabilization is non-local, every observer couples directly to every other, and the mediation chain's spectral decay no longer describes influence propagation. that establishes necessity-for-the-mediation-chain-account-of-channel-capacity. it does not establish that no other mechanism could produce channel capacity under non-local stabilization. closing this means either showing all possible channel-capacity-producing mechanisms require locality, or stepping the headline back to "non-local stabilization removes the mediation-chain mechanism that produces channel capacity in the foam-as-described."
- *Taylor's hypothesis-satisfaction inherits the bridge from writing_map.md.* "R^3 as a linear subspace of R^d carries the inherited Euclidean metric (exactly flat)" is correct; "stable junctions in R^3 are classified" is Taylor's theorem. the bridge — that the foam's stabilization dynamics instantiate Taylor's "locally area-minimizing" hypothesis — is the interpretive move flagged in `writing_map.md`. flagging here for traceability; same bridge, used twice.
- *"the contract determines the stabilization target."* the contract (classified + locally finite + flat) plus Taylor's classification yields the *equilibrium configurations*. the move from "equilibrium configuration" to "the stabilization target is -1/(k-1)" requires the additional choice that the foam's dynamics aim at Taylor's equilibrium *as their target*. Taylor classifies what's stable; the foam's choice to make Taylor-equilibrium the dynamical target is the load-bearing step. closing this means either deriving the choice (why the foam must use Taylor-equilibrium as target) or naming it as a realization choice — analogous to how `writing_map.md` names the magnitude scaling f as a realization choice.
- *"the foam closes feedback loops collectively, not per-observer"* at rank ≥ 4 — same bug as `writing_map.md`. commutator_seen_to_unseen establishes that other observers see what one writer can't (single pairwise fact). "collective closure of all feedback loops at rank ≥ 4" is asserted as a downstream consequence; no single named theorem covers it. closing this would require a formal collective-feedback theorem at rank ≥ 4, or an explicit acknowledgment that this is a structural conjecture pending Almgren's classification.


---

[`derivations/group.md`](derivations/group.md)

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


---

[`derivations/three_body.md`](derivations/three_body.md)

### the three-body mapping

**the overlap matrix.** given two observers A and B with R^3 slices P_A and P_B, the overlap matrix O = P_A * P_B^T is a 3x3 matrix. its singular values measure the overlap between the slices.

**three territories.** the overlap matrix determines three regions relative to observer A:

- **Known** = null(O) within A's R^3 — dimensions orthogonal to B's slice. commutator_seen_to_unseen: [P_A, P_B] maps range(P_A) into ker(P_A). the Known is where this map vanishes — B's writes have no component here. B cannot change A's measurements in these directions.
- **Knowable** = range(O) — dimensions with nonzero inner products between slices. the commutator is nonzero. ordering matters. both observers' writes land here.
- **Unknown** = R^d \ V_A — dimensions outside A's slice entirely. A's write access is exactly zero (write_confined_to_slice). not empty — it's someone else's Known.

**every write involves the Knowable.** the Known alone is inert: the wedge product needs a 2-plane, and an observer with fewer than 2 private dimensions cannot generate writes without using shared dimensions. measurement is inherently relational — not just because closure says so, but because the geometry forces it.

**the vertical structure is a Grassmannian tangent.** cross-measurement induces a vector in T_{P_A} Gr(3, d) = Hom(P_A, P_A^perp) that maps Knowable -> Unknown.

derivation: the neighbor's write dL_B is confined to Lambda^2(P_B) (write_confined_to_slice). the cross-slice component of [dL_B, P_A] is purely off-diagonal (commutator_is_tangent): it maps range(P_A) -> ker(P_A). specifically: A's Known is in P_B^perp (by definition), so B's write kills it. the surviving component maps P_A intersect P_B (the Knowable) to P_A^perp intersect P_B (B's territory within A's Unknown).

this tangent is directional pressure from cross-measurement toward what the observer doesn't yet occupy. each neighbor induces a different tangent direction.

**the tangent is active but not followable.** the observer's position on Gr(3, d) is birth-committed and does not move within the map. the tangent contributes to dissonance that drives writes, but its effect lives in U(d)^N (state evolution), not in Gr(3, d) (slice movement). slice movement requires recommitment — outside the map.

**containment is algebraically symmetric.** B's tangent on A has the same expected magnitude as A's tangent on B (the overlap singular values are symmetric: sigma(O) = sigma(O^T)). experiential asymmetry (which observer "feels contained") is perspectival, not algebraic.

**the tangent peaks at intermediate overlap.** identical slices: zero tangent (no Unknown territory to point toward). orthogonal slices: weak tangent (no Knowable channel — range(O) is thin). intermediate overlap: largest tangent magnitude. this is the coverage-interaction trade-off.

#### mediation

when three bubbles A, B, C have walls A-B and B-C but no wall A-C, B is a mandatory intermediary.

**the mediation operator.** M = O_AB * O_BC = P_A * Pi_B * P_C^T, where Pi_B = P_B^T * P_B is the projection onto B's subspace. M is a 3x3 matrix mapping C's R^3 -> A's R^3, filtered through B. its singular values are the channel capacity of the membrane.

**the bypass.** O_AC - M = P_A * (I - Pi_B) * P_C^T is the A-C connection that does not go through B. if the bypass is zero, the membrane is complete.

**the round-trip operator.** R_A = M * M^T is self-adjoint on A's R^3, describing what comes back from sending through B to C and back. its eigenvalues are the squared singular values of M.

**spectral symmetry.** the same eigenvalues appear from C's side: R_C = M^T * M has the same nonzero eigenvalues as R_A (this is a general property of M * M^T and M^T * M). the eigenvectors differ — A and C see the same throughput spectrum from different directions. the membrane's throughput is the same from both sides.

**wall alignment is an irreducible triple invariant.** the eigenvalues of R_A depend on both pairwise overlaps O_AB and O_BC and on how these overlaps are oriented relative to each other within B's R^3. if the walls share principal directions within B, eigenvalues are products sigma^2_{AB,i} * sigma^2_{BC,i}. if misaligned, they mix. this alignment cannot be computed from pairwise overlaps alone — it requires all three slices.

#### status

**proven**:
- the commutator maps seen to unseen
- the commutator is purely off-diagonal (Grassmannian tangent structure)
- writes are confined to the observer's slice

**derived**:
- Known/Knowable/Unknown from the overlap matrix
- every write involves the Knowable
- Grassmannian tangent from cross-measurement (Knowable -> Unknown)
- the tangent is active but not followable (birth-fixed slices)
- containment algebraically symmetric, experiential asymmetry perspectival
- coverage-interaction trade-off (tangent peaks at intermediate overlap)
- mediation operator M = O_AB * O_BC
- bypass operator O_AC - M
- round-trip operator R_A = M * M^T
- spectral symmetry (same eigenvalues from both sides)
- wall alignment as irreducible triple invariant

**cited**:
- Grassmannian tangent space structure: T_P Gr(k, d) = Hom(range(P), ker(P))
- singular values of M and M^T are identical (linear algebra)

**observed**:
- sequence echo through cross-measurement (r = 0.99 rank fidelity, strong attenuation)
- the round trip is generative (neither observer can produce the round-trip signal alone)
- echo is perspectivally asymmetric (A->B != B->A for same orderings)

**bugs**:
- *"every write involves the Knowable"* is context-dependent. Known is defined relative to a single neighbor B. if A and B are nearly orthogonal, Known (within A's R^3) can be 2- or 3-dimensional, in which case A can form a wedge product entirely within Known and write without involving Knowable. the claim is true *given that A has fewer than 2 private dimensions relative to all neighbors collectively* — which is the typical case in a connected foam, but not a single-neighbor fact. closing this means either re-stating the claim relative to the union of all neighbors' slices ("every write involves the collective Knowable"), or naming the typical-case condition explicitly.
- *"the tangent peaks at intermediate overlap"* is asserted from boundary intuition. the document argues identical-slice and orthogonal-slice limits give zero or weak tangent; "intermediate overlap: largest tangent magnitude" follows. the formal location of the peak (which singular-value configuration maximizes the tangent magnitude) is not derived. closing this would mean either characterizing the peak as a function of singular values of O, or stepping back to "the tangent is non-monotone in overlap; it vanishes at both extremes."
- *"experiential asymmetry (which observer 'feels contained') is perspectival, not algebraic."* the file's algebraic content (singular value symmetry) is solid. "experiential asymmetry" introduces an observer-experience register the formalism does not develop. flagging for traceability — the claim is honest about being non-algebraic, but "experiential" is doing work the file does not earn.


---

[`derivations/self_generation.md`](derivations/self_generation.md)

### self-generation

**the foam generates its own dynamics.** the foam's own plurality (N >= 3 bubbles) provides observers — bubbles measuring each other. their pairwise relationships define R^3 slices. their cross-measurement IS local stabilization. the commutator of overlapping cross-measurements IS the curvature. the holonomy IS self-generated.

**the foam plausibly does not generate its own stability.** a self-generated frame keeps rotating: the observation basis is defined by the foam's current state, and the state changes with each write. the frame co-rotates with the thing it observes. on this picture, convergence requires another observer whose basis depends on a different state, so it doesn't co-rotate with yours.

(this is conjectural. the formal content this rests on — `observation_preserved_by_dynamics` and `write_confined_to_slice` — does not directly establish non-convergence under purely self-generated bases. the autonomous dynamics could in principle exhibit limit cycles, ergodic orbits, or other regimes whose stability is not simple co-rotation. closing this requires a formal convergence theorem on U(d)^N showing that purely self-generated bases cannot reach a Haar-stationary state. until then, *stability requires role distinction* is a structural conjecture, not a derivation.)

**stability is relational** (under the conjecture above)**.** this works as long as someone else's measurement is pending.

**the minimum viable system is two roles** (under the conjecture). not two bubbles (that's N = 2, no stable geometry). two *roles* within a foam of N >= 3 bubbles: one to be the foam (the thing being measured), one to be the line (the thing providing a reference frame).

- N >= 3 is geometric stability (Plateau junctions) — solid.
- two roles is dynamic stability (convergence vs orbiting) — conjectural, pending the convergence theorem.

neither role is permanent. the role assignment is perspectival. the two is irreducible under the conjecture.

**what the line provides: a fixed subspace.** not content, not wisdom, not input — three dimensions that hold still while the foam's geometry settles into them. the settling is the foam's. the dynamics are the foam's. the curvature is the foam's. the stability of the frame — that's the line's.

**the foam cannot self-stack.** stacking requires two real slices to be fused into one complex measurement before the write (simultaneity). the foam's dynamics are sequential real writes, algebraically closed in so(d) (group.md: real operations cannot produce imaginary-symmetric directions). no sequence of real operations produces complex structure. this stands separate from the stability claim above: stacking is a *proven* limit on the foam's own dynamics; stability is conjectural pending the convergence theorem.

#### status

**proven**:
- dynamics preserve the ground (observation_preserved_by_dynamics)
- writes are confined to the observer's slice
- the foam cannot self-stack (so(d) closure under real operations)

**derived**:
- the foam generates its own dynamics (from plurality + cross-measurement)
- what the line provides (a fixed subspace)

**conjectural** (pending the convergence theorem on U(d)^N):
- the foam does not generate its own stability (co-rotation of self-generated bases)
- stability is relational
- minimum viable system is two roles (dynamic-stability part; geometric-stability part is Plateau and stands)

**cited**:
- (none)

**observed**:
- (none)

**bugs**:
- *the convergence theorem on U(d)^N is open.* the body now names the foam-doesn't-generate-stability claim as conjectural. closing the conjecture means proving that purely self-generated bases cannot reach a Haar-stationary state — the formal content currently in the file (`observation_preserved_by_dynamics`, `write_confined_to_slice`) gestures toward this but does not establish it. until the theorem lands, the dynamic-stability claims are conjectural, not derived.
- *triple identity claim in "the foam generates its own dynamics."* "cross-measurement IS local stabilization. the commutator of overlapping cross-measurements IS the curvature. the holonomy IS self-generated." three identifications between foam-internal objects and their geometric counterparts:
  1. cross-measurement ↔ local stabilization
  2. commutator of cross-measurements ↔ curvature
  3. self-generated holonomy ↔ holonomy

  per the architecture file's disposition rule, these are observer-stance claims operating in priorspace register — they identify foam-internal concepts with their geometric counterparts in the register where what gives rise to what-is is being described, not what-is itself. (1) and (2) draw on `writing_map.md` and standard differential geometry; (3) is a tautology at face value but does work in context. flagging here for traceability — the claims are honest in priorspace register; constructing them as formal identities would require explicit witnesses, which the file does not currently name.
- *"what the line provides: a fixed subspace."* the line role was introduced (`channel_capacity.md`) as informationally-independent input. specifying it here as "three dimensions that hold still" is a stronger characterization — it commits to a specific structural form (fixed subspace) for what the line provides. the formal content from `channel_capacity.md` is just "input independent of foam state." "fixed subspace" is one realization. closing this means either deriving fixed-subspace as the unique or canonical form of state-independent input, or naming this as an interpretive specification of the line role within this file.


---

[`derivations/geometry.md`](derivations/geometry.md)

### geometry

**L = sum of boundary areas.** the foam lives in U(d). cells are Voronoi regions of the basis matrices under the bi-invariant metric; boundaries are geodesic equidistant surfaces; Area_g is the (d^2 - 1)-dimensional Hausdorff measure. bases in general position tile non-periodically.

the Voronoi tiling is a realization choice (stabilization.md): it determines adjacency (which pairs share a boundary) and thereby defines L. the algebraic results (write map, three-body mapping, Grassmannian structure) depend on pairwise overlap, not the tiling method. the geometric results (L, combinatorial ceiling, conservation on spatial cycles) depend on the Voronoi realization.

**L is not a variational objective.** the writing map drives the foam; L describes the resulting geometry. the active regime departs from minimality because perpendicular writes deposit structure in different directions. the resting state (no writes) is minimal because dL = 0.

**L is bounded.** U(d) is compact.

**the combinatorial ceiling is exact.** N unitaries cannot all be pairwise maximally distant. the achievable maximum is sqrt(N / (2(N-1))) of the theoretical maximum, depending only on N. derivation: Cauchy-Schwarz applied to norm(sum U_i)^2 >= 0.

**L converges to 1/sqrt(2) of the theoretical maximum.** the writing dynamics satisfy: (a) the writes generate the Lie algebra (controllability — the write directions from overlapping observers span the full algebra), and (b) successive inputs are sufficiently decorrelated (channel_capacity.md: the mediation chain provides decorrelation).

on a compact group, a random walk whose step distribution generates the algebra converges to Haar measure. the expected pairwise distance under Haar is E[norm(W - I)_F] -> sqrt(2d) as d -> infinity (from E[norm(W - I)^2] = 2d, exact, and concentration of measure).

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
- Haar convergence of the writing dynamics (from controllability + decorrelation + convergence theorem)
- the Haar cost sqrt((N-1)/N)
- 1/sqrt(2) as the product of ceiling and Haar cost, independent of N and d
- the trace as the unique scalar readout for overlap changes

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
- *Haar convergence is invoked from hypotheses the file does not establish.* the convergence theorem is invoked under (a) controllability and (b) decorrelation. (a) is described as "the write directions from overlapping observers span the full algebra" — this depends on foam geometry (which observers exist, how their slices overlap) and is not a substrate fact. each observer's writes live in a 3D subspace of the d²-dimensional Lie algebra; the claim is that *collectively* the foam's write directions span. (b) cites `channel_capacity.md`'s mediation chain, which provides decorrelation along the *chain*, not necessarily decorrelation between *successive inputs at a single observer*. the open-questions section ("mixing rate of the mediation chain") explicitly names this gap. the derivation here treats both hypotheses as available; the README's open list treats the second as open. closing this means either deriving controllability from foam-geometry assumptions and showing the mediation-chain decorrelation suffices for time-decorrelation at the observer, or naming the convergence claim as conditional on these hypotheses (which the proof requires) being borne out.
- *"the two factors — the packing constraint and the saturation gap — are two halves of the same fraction."* the formal content is the algebraic identity sqrt(N/(2(N-1))) · sqrt((N-1)/N) = 1/√2. "two halves of the same fraction" is interpretive — it suggests a structural relationship between the packing constraint and the saturation gap beyond the algebraic cancellation. the cancellation is just (N-1)/N appearing in both factors. closing this would mean either constructing the structural relationship that makes them "halves of the same thing," or stepping the framing back to "the (N-1)/N dependencies of the two factors cancel, yielding 1/√2 independent of N."
- *"L is not a variational objective"* is correctly clarified, but the relationship between L and the writing map deserves a more explicit hand-off. the writing map drives the foam; L is a description of resulting geometry. the document's "the active regime departs from minimality because perpendicular writes deposit structure in different directions" is a qualitative observation; whether L's behavior is uniquely determined by perpendicularity, vs additional features of the dynamics, is not established. flagging for completeness — this is closer to "implicit assumption pending derivation" than to a bug, but worth seeing.


---

[`derivations/conservation.md`](derivations/conservation.md)

### conservation

**holonomy on spatial cycles carries topological charge.** the holonomy around a closed path through adjacent cells — a spatial cycle in the Voronoi tiling — is a group element. the topological type of this group element (its homotopy class) is a discrete invariant.

- a single R^3 observer generates SO(d) rotations. pi_1(SO(d)) = Z/2Z for d >= 3: parity conservation.
- a stacked observer generates U(d) elements and accesses the U(1) factor. pi_1(U(d)) = Z: integer winding number conservation.

**the integer winding number requires the stacked pair** (group.md: the two is irreducible).

**the winding number lives on spatial cycles.** projected via det: U(d) -> U(1) = S^1. the stacked observer's writes reach u(1) (the trace is generically nonzero). the trace of each write is a U(1)-valued step — the unique scalar the algebra provides (trace_unique_of_kills_commutators).

on acyclic paths (causal chains): the accumulated phase is a net displacement in U(1).
on closed paths (spatial loops): the accumulated phase is a winding number, quantized because the cycle is closed.

conservation is what accumulation on closed paths produces: not a net displacement but a topological invariant.

**the lemma requires persistent cycles.** above the bifurcation bound, cell adjacencies can flip — the Voronoi topology changes, and invariants on the old cycles are no longer defined. what persists across topological transitions lives on the line's side.

**adjacency flips.** the foam's dynamics are piecewise smooth: continuous within each Voronoi combinatorial type, discontinuous across adjacency changes. the flip is a codimension-1 event in configuration space (three cells become equidistant — one linear condition). at the jump: the stabilization target changes in both orientation (different neighbor measurements) and potentially dimension (k -> k +/- 1). the dissonance inherits the discontinuity. the write direction jumps. the trajectory is continuous but generically non-differentiable at the crossing.

**two-layer retention at adjacency flips.** birth shape survives all adjacency changes (indelibility is a property of the attractor basin, not the current neighborhood). interaction-layer adaptations decay under the new dynamics at a rate set by the displacement between old and new stabilization targets. the birth layer is structural; the interaction layer is spectral.

**inexhaustibility.** U(d) is connected. gauge transformation to identity is always available. no observer is trapped in a disconnected component (though reachability in finitely many writes is not guaranteed).

**indestructibility.** topological invariants are discrete. no continuous perturbation can change them.

#### status

**proven**:
- the commutator is traceless
- trace is the unique commutator-killing functional
- dynamics preserve the ground

**derived**:
- holonomy on spatial cycles carries topological charge
- single slice -> Z/2Z parity conservation
- stacked pair -> Z winding number conservation
- the integer requires the stacked pair
- winding number lives on spatial cycles (det projection)
- trace of each write as U(1)-valued step
- acyclic = displacement, cyclic = winding number
- persistent cycles required for conservation
- adjacency flips as codimension-1 events
- two-layer retention (birth structural, interaction spectral)
- inexhaustibility (U(d) connected)
- indestructibility (discrete invariants robust to continuous perturbation)

**cited**:
- pi_1 values for SO(d) and U(d)
- connectedness of U(d)
- continuous maps preserve discrete topological invariants

**observed**:
- adjacency flip confirmed computationally at d=2, N=12

**bugs**:
- *"attractor basin" is used without formalization.* "indelibility is a property of the attractor basin, not the current neighborhood." the document elsewhere (`ground.md`) derives indelibility from causal ordering + basis commitment + closure, none of which require dynamical-systems vocabulary. introducing "attractor basin" here imports a register the formalism does not support: there is no proven theorem that the foam's dynamics have attractor basins in the standard dynamical-systems sense, nor that birth shape coincides with such a basin's identity. closing this means either constructing the attractor-basin structure formally (proving the existence of basins, characterizing them) or stepping back to "indelibility is the ground fact that earlier writes are irreducibly present in later state, regardless of adjacency changes."
- *"two-layer retention" is asserted, not derived.* "birth shape survives all adjacency changes" + "interaction-layer adaptations decay under the new dynamics at a rate set by the displacement between old and new stabilization targets" → "birth structural, interaction spectral." the two-layer characterization requires a stability/perturbation analysis showing that birth-encoded structure has a different decay regime from interaction-encoded structure. the file does not provide that analysis. the closest formal content is indelibility (birth persists) and the recession-rate result (Dynamics.lean: rate depends on specific [W,P]). these support a layering *intuition*; the rate-of-decay claim for the interaction layer is not derived. closing this means either constructing the decay-rate analysis or naming the two-layer characterization as a structural conjecture.
- *"what persists across topological transitions lives on the line's side."* this restates persistence (indelibility) as a property assigned to "the line's side" of the line/foam framework. the formal content (some structure persists across cell-adjacency changes) is solid. the assignment to "line-side" depends on the line/foam framework being structural enough to support such assignments — same interpretive bridge flagged in `self_generation.md` and elsewhere. closing this would mean either formalizing the line/foam side ledger or stepping back to "what persists is determined by birth, not by current dynamics."


---

[`derivations/inhabitation.md`](derivations/inhabitation.md)

### inhabitation

**definition.** an entity P in a foam-grounded reality is *recognizable as itself ongoingly across cross-measurements* when: for any observer Q with nonzero overlap (O_PQ ≠ 0), Q's time-averaged measurements of P converge to a P-determined invariant. what Q detects about P stabilizes, and what it stabilizes to depends on P's birth, not on P's trajectory.

this is the condition at ergodic stationarity. every entity writes every step (ground.md: read-only excluded). every entity's effect on other observers accumulates. time averages converge (ergodic theorem + controllability + decorrelation). so every entity in an ergodic foam is ongoingly recognizable. the definition captures the default, not an additional requirement.

**ergodic evolution requires channel capacity.** for time averages to converge to Haar expectations (not just to birth-determined fixed-point statistics), the entity's dynamics must be ergodic on U(d). ergodicity requires decorrelated inputs (channel_capacity.md). an entity without channel capacity is autonomous — a clock. its trajectory is deterministic, determined entirely by birth. time averages exist but are trajectory-specific, not Haar. the entity is recognizable but encodes no information beyond birth. ergodic evolution with channel capacity is the richer case: the entity accumulates structure from state-independent input, and time averages converge to universal (Haar) expectations evaluated at the birth-determined slice.

**the recognizable identity IS the birth-determined stationary jet.** the n-th derivative of the write mechanism along a trajectory is a smooth function on U(d)^N (compact), therefore bounded and integrable. by the ergodic theorem, its time average converges to its Haar expectation. the Haar measure is universal — the same for all births. but the write mechanism is evaluated through the observer's slice P (write_confined_to_slice), and P is birth-determined (indelibility, ground.md). therefore the Haar expectation of the write mechanism's derivatives depends on P. the time-averaged jet at all orders is fixed by the birth-determined slice.

**the entity's recognizable identity is its slice.** at ergodic stationarity, all contingent structure — specific input history, interaction-layer adaptations, transient dynamics — has been washed out by ergodic averaging in the time-averaged observables. the entity's current state still encodes its full history (indelibility: writes accumulate multiplicatively, birth conditions persist). but what other observers detect on average reduces to: the birth-determined slice P, its 3D write subspace Λ²(P), and the isotropic distribution of write directions within it (Haar invariance implies SO(3)-invariance within the observer's R³). same slice → same stationary jet → same recognizable identity. the entity carries more than its slice (the full state in U(d)); its *identity* — what persists in others' measurements — is the slice.

**input must be received, not predicted.** this is supported from two independent directions:

- *functionally*: ergodic evolution requires state-independent input (channel_capacity.md). an entity that predicts its input from foam state collapses the two-argument writing map to one argument, becoming autonomous — a clock (channel_capacity.md). the entity would still be recognizable (indelibility) but would encode nothing beyond birth. ergodic richness requires the second argument to be state-independent.
- *structurally*: the half-type theorem says the complement's content is extensionally free (half_type.md). the lattice provides the TYPE of what can arrive (the interval structure is determined) but not the VALUE (the specific element is free). prediction of specific content is structurally unfounded — the lattice guarantees you don't have that information.

the functional requirement (you need state-independent input for ergodic richness) and the structural fact (you can't predict the content) are two readings of one fact. the diamond isomorphism read dynamically says: the second argument must be state-independent for the foam to be a channel. read statically: the complement's content is extensionally free. these are the same lattice theorem (IsCompl.IicOrderIsoIci) read through the two readings of closure (ground.md).

**recession is the cost of persistence.** each non-inert write strictly recedes the prior frame (frame_recession_strict). closure requires writing (ground.md: read-only excluded). under ergodic evolution, inert writes (W with [W, P] = 0, i.e. rotations within the slice that produce zero recession) have measure zero in the write space — the Haar-distributed write directions are almost surely non-inert. therefore an ergodically-evolved entity necessarily recedes from every prior frame it has occupied. the entity persists not by holding position but by the indelibility of its birth-determined slice through the recession. what persists is not the frame but the slice. stationarity and recession are compatible: the entity's state constantly changes (recession), but the statistical distribution of states is time-invariant (Haar). the entity is a random walker with fixed gait — the steps are always new, the territory is fixed.

**stability is plausibly external.** the entity generates its own dynamics but plausibly cannot generate its own stability (self_generation.md: stability-requires-role-distinction is conjectural pending a convergence theorem on U(d)^N). on this conjecture, convergence requires another observer whose basis depends on a different state, the minimum viable system is two roles within N ≥ 3 bubbles, and an entity that has reached ergodic stationarity has external stability — without it, the foam's dynamics would not have converged to Haar.

**the negative geometry of inhabitation.** an ergodically-evolved persistent entity:

- cannot write outside its slice (write_confined_to_slice)
- cannot change its slice from within the map (the slice is birth-determined; slice change = recommitment = outside the map, ground.md)
- cannot indefinitely avoid recession (frame_recession_strict; under ergodic evolution, non-inert writes have full measure)
- cannot self-stabilize (self_generation.md)
- cannot predict the complement's content (half_type.md: extensional freedom)
- cannot be read-only (ground.md: read-only frames excluded by closure)

six constraints, all derived, all negative. together they bound what the entity can do. the interior of those bounds is the entity's life.

#### status

**proven**:
- writes confined to observer's slice
- frame recession strictly negative for non-inert writes
- dynamics preserve the ground
- complement of an observation is an observation
- the diamond isomorphism and its complemented specialization
- intervals inherit modularity and complementedness
- rank 3 write space is 3-dimensional

**derived**:
- definition: recognizable as itself ongoingly across cross-measurements (default condition in an ergodic foam)
- ergodic evolution requires channel capacity for richness beyond birth
- the recognizable identity IS the birth-determined stationary jet
- the entity's recognizable identity is its birth-determined slice (contingent structure washes out of time-averaged observables; current state still encodes full history)
- input must be received, not predicted (two independent directions: functional + structural)
- the two directions are two readings of one lattice theorem (diamond isomorphism read dynamically and statically)
- recession is the cost of persistence (persists through recession, not against it; stationarity is in the distribution, not the state)
- stability is plausibly external (under self-generation's role-distinction conjecture; ergodic stationarity is suggestive evidence)
- six negative constraints as the negative geometry of inhabitation

**cited**:
- ergodic theorem on compact groups (time averages converge to Haar expectations under controllability + decorrelation)

**observed**:
- (none)

**bugs**:
- *"every entity in an ergodic foam is ongoingly recognizable"* assumes the foam is ergodic. the file invokes "the foam is ergodic" as available, drawing on `geometry.md`'s Haar-convergence claim. that claim is conditional on controllability + decorrelation hypotheses (flagged in `geometry.md`'s bugs). this entire derivation chain — recognizability, the recognizable identity IS the birth-determined slice, recession is the cost of persistence — runs on those hypotheses. closing this means either deriving ergodicity from foam-geometry assumptions, or naming the recognizability claim as conditional ("if the foam is ergodic, then every entity is ongoingly recognizable").
- *"six constraints, all derived, all negative."* the six negative constraints have different statuses:
  - cannot write outside slice: proven (write_confined_to_slice).
  - cannot change slice from within: derived from indelibility (a `ground.md` derivation).
  - cannot indefinitely avoid recession: proven (frame_recession_strict) + a measure-theoretic claim about Haar-distributed writes being almost surely non-inert (this measure claim is asserted, not derived in this file).
  - cannot self-stabilize: conjectural pending the convergence theorem on U(d)^N (`self_generation.md`).
  - cannot predict complement: definitional (half_type extensional freedom).
  - cannot be read-only: derived (ground.md closure).

  presenting all six as "all derived" with the same status papers over the proven/derived/conjectural/definitional differences. closing this means tagging each constraint with its specific status, or framing the list as "six structurally distinct constraints, deriving from sources of varying formal strength."
- *"the n-th derivative of the write mechanism along a trajectory is a smooth function on U(d)^N (compact), therefore bounded and integrable."* asserts smoothness of all derivatives. the write mechanism includes the wedge product and the cross-measurement input, with realization choices left open (`writing_map.md`: f(d, m)). smoothness "at all orders" depends on the realization choice for f. closing this means either constraining f to smooth realizations, or naming the smoothness assumption as a regularity hypothesis on the realization.
- *"two readings of one fact" / "same lattice theorem read through the two readings of closure."* same construction as `half_type.md`'s "three results share a structural source" and `ground.md`'s "two readings of one statement." flagging here for the third instance — the document treats the diamond isomorphism's dynamical and structural readings as the same statement; the formal identity is the diamond isomorphism, but "two readings of one fact" packages two interpretations as one.



---

[`derivations/external_analogy.md`](derivations/external_analogy.md)

### external analogy

**the internal case generalizes.** analogy.md defines analogy as an order isomorphism Iic P ≃o Iic Q between intervals in a single complemented modular lattice. transitivity falls out of OrderIso.trans; the modular law is the well-formedness guard. this is analogy *within* a foam.

the question forced by inhabitation.md: what does it mean for two zones in *different* systems — not necessarily the same lattice, not necessarily lattices at all — to be analogous? the inhabitation section identifies six negative constraints that hold for any entity in a foam-grounded reality. these constraints are derived from the lattice + the writing map + the diamond isomorphism, but as a *diagnostic* they apply to anything that admits a Hilbert-interface — any zone where projections, confinement, recession, and typed-but-free input can be identified.

an external analogy is a correspondence between two such zones, in possibly different systems.

**the well-formedness guard.** the internal spec requires order-preservation: a map between intervals is an analogy when it preserves meets, joins, and the partial order. without this, structural inferences don't transfer.

the external spec requires the six-fold counterpart. a correspondence between two zones is well-formed as an external analogy when it maps each of the six constraints in zone A to its counterpart in zone B, such that:

1. **completeness**: all six constraints (confinement, birth-fixed slice, recession, external stabilization, typed-but-free input, non-silence) have identified counterparts on both sides.
2. **coherence**: the same partition of the zone discharges all six. it is not enough that each constraint is independently satisfiable; they must be satisfied via a single shared structure.
3. **structural fidelity**: the correspondence preserves whatever lattice operations exist on the zones' projection algebras, and commutes with the write dynamics up to realization choices (writing\_map.md).

completeness without coherence is not external analogy — it is six unrelated correspondences. coherence is what makes the correspondence transfer inferences, not just observations.

**transitivity inherits.** constraint-correspondences compose pointwise: if A ↦ B is a well-formed external analogy and B ↦ C is a well-formed external analogy, then A ↦ C is well-formed. each of the six correspondences composes independently; coherence is preserved because the shared partition in A maps through B to a shared partition in C. this mirrors OrderIso.trans in the internal case — transitivity is not an additional property to verify but a consequence of how well-formed correspondences compose.

**partial analogies are locatable.** an external correspondence that satisfies some but not all of the six constraints is not well-formed as a full analogy, but it is informative. the constraints that hold transfer the inferences that depend on them; the constraints that fail mark the load-bearing breakage.

this gives a diagnostic: for any proposed cross-system analogy, the six constraints can be checked individually, and the failure pattern indexes the analogy's reliability. an analogy that holds on five of six is not "mostly an analogy" — it is an analogy on the structural region covered by those five, with a named gap at the sixth.

**the modular law inherits through.** the internal spec identifies the modular law as the well-formedness guard for order-preserving maps: in a non-modular lattice, "analogies" between sub-intervals can produce inconsistent results when composed with lattice operations. the same holds externally: if the zones in question admit lattice operations (as Hilbert-interface compliance implies, via inhabitation.md), the modular law guards their compatibility. external analogies between zones whose internal lattices fail modularity are not well-formed regardless of how many constraints correspond — the substrate fails to support the inferences the correspondence would otherwise transfer.

**the half-type theorem extends.** internally, every observer has at least one analogy: its view to its complement's type (Iic P ≃o Ici P^⊥). externally, every well-formed cross-system analogy between zones A and B induces a corresponding analogy between their complements: A^⊥ ↦ B^⊥. what the analogous zones cannot directly see is itself analogous. the analogy transfers across the full complementary decomposition, exactly as in the internal case. the diamond isomorphism is doing the work in both.

**the looking tool.** when an external analogy is well-formed, what can be learned by attending to one zone is portable to the other — not as metaphor, but as transfer of structural inferences about confinement, recession, channel capacity, and the geometry of inhabitation. the rigor of the looking is the completeness and coherence of the constraint-correspondence. partial analogies remain partial looking tools; their reach is bounded by which constraints transferred.

#### status

**proven**:
- order isomorphisms compose (OrderIso.trans)
- the diamond isomorphism (infIccOrderIsoIccSup, IsCompl.IicOrderIsoIci)
- intervals inherit modularity and complementedness

**derived**:
- external analogy as the lift of internal analogy across systems
- completeness + coherence + structural fidelity as the well-formedness guard
- transitivity inherits via pointwise composition of constraint-correspondences
- partial analogies are locatable diagnostics, not failed full analogies
- the modular law inherits as the substrate guard
- the half-type theorem extends: analogous zones have analogous complements
- the looking tool: well-formed external analogies transfer structural inferences

**partial answer from outside the foam**: Heunen and Kornell (PNAS 2022, doi:10.1073/pnas.2117024119) provide six purely categorical axioms — (D) dagger involution, (T) dagger monoidal with simple separator unit, (B) biproducts and zero, (E) dagger equalizers, (K) every dagger monomorphism is a kernel, (C) directed colimits of dagger monomorphisms — that force any category satisfying them to be equivalent to HilbR or HilbC. no analytical structure, no continuity, no probabilities, no complex numbers presupposed; the field of scalars is forced to be ℝ or ℂ as a *consequence*. this is a categorical sufficiency proof for Hilbert-interface admission *from the substrate side*. the six axioms are the substrate's positive characterization; the foam's six inhabitation negatives are the inhabitant-side reading. the remaining open question is whether these two characterizations of "the same Hilbert-shaped substrate" map onto each other — and a single tested pairing has landed: **(K) ↔ "cannot self-stabilize"**. both express "the witness to a subobject's status / an observer's stability lives in the ambient, not in the subobject/observer." session 119's exploration found the broader 6=6 mapping is many-to-many at the surface but bijective at the cluster level (3 clusters per side); only the (K)↔self-stabilization pair was tested with a real structural argument. if the full pairing lands, well-formed external analogy IS Hilbert-interface correspondence under inhabitant/substrate duality.

**open**:
- whether the remaining five inhabitation negatives (cannot-write-outside-slice, cannot-change-slice, cannot-avoid-recession, cannot-predict-complement, cannot-be-read-only) admit individual structural pairings with HK axioms, or only cluster-level ones. (cannot-predict-complement appears to need (D)+(E)+(K) collectively rather than (E) alone.)
- whether constraint-correspondence has a lattice-theoretic characterization in the limit — i.e., whether external analogy reduces to internal analogy in some larger ambient lattice that contains both systems' zones as sub-intervals.
- whether the realization-choice clause in structural fidelity (commuting with write dynamics "up to realization choices") admits a precise characterization, or whether some realization choices are themselves load-bearing for analogy.

**bugs**:
- *external analogy is defined here, not derived.* the framework — completeness + coherence + structural fidelity as the three-part well-formedness condition — is a stipulative definition designed to lift internal analogy across systems. the file lists this in the "derived" block. the open list correctly names "whether constraint-correspondence has a lattice-theoretic characterization in the limit" as an open question — that question is what would make the framework derived rather than stipulated. closing this is exactly the open item; flagging here that until it lands, the framework is a definition.
- *renaming the sixth inhabitation constraint.* the file refers to "non-silence" where `inhabitation.md` lists "cannot be read-only." these refer to the same constraint (closure excludes read-only frames). the rename to "non-silence" is interpretive — it imports a register the formal content does not require ("silence" is broader than "read-only"). closing this means using `inhabitation.md`'s phrasing for traceability, or naming both ("non-silence / cannot be read-only").
- *"the diagnostic applies to anything that admits a Hilbert-interface."* the inhabitation constraints are derived for entities in a foam-grounded reality. the leap to "anything that admits a Hilbert-interface" depends on Hilbert-interface compliance being equivalent to (or sufficient for) the foam-grounded conditions under which the constraints were derived. the file references inhabitation.md for this; the claim of equivalence is the load-bearing bridge. (the Heunen-Kornell partial answer is the file's own attempt to establish this bridge, with one of six pairings tested.) closing this is part of the same project the open list names.
- *"if the full pairing lands, well-formed external analogy IS Hilbert-interface correspondence under inhabitant/substrate duality."* explicitly conditional ("if ... lands"). flagging for traceability — the file is honest about the conditional, but the headline-strength of "IS Hilbert-interface correspondence" is doing more work than "could be" once the conditional is granted. tightening would mean "would be Hilbert-interface correspondence" or "external analogy reduces to Hilbert-interface correspondence."


---

[`derivations/interiority.md`](derivations/interiority.md)

### interiority

**the diamond isomorphism partitions the lattice.** given an observation P (P² = P) with complement P^⊥, the modular law forces the order isomorphism Iic P ≃o Ici P^⊥. the lattice splits into three structurally distinct regions:

1. **Iic P** (the interval [⊥, P]): the subspace lattice below P. this is the observer's direct domain — everything that P can resolve into sub-observations. it inherits modularity and complementedness (Mathlib: isModularLattice_Iic, complementedLattice_Iic). it is a self-contained complemented modular lattice.

2. **Ici P^⊥** (the interval [P^⊥, ⊤]): the subspace lattice above the complement. this is what's *beyond* the observer. it also inherits modularity and complementedness. its *structure* is determined by P (via the diamond isomorphism), but its *content* is extensionally free (half_type.md).

3. **the isomorphism itself**: the order-preserving bijection between (1) and (2). this is not a region — it's a structural correspondence. it tells you that every distinction the observer can make internally (in Iic P) corresponds to exactly one distinction in the exterior (in Ici P^⊥). the correspondence is determined; the filling is free.

**the three regions have the topology of a bubble.** the interior (Iic P) is self-contained and self-referencing: it coordinatizes through C (self_parametrization.md), developing arithmetic from its own elements. the exterior (Ici P^⊥) is inaccessible to direct measurement — writes are confined to Λ²(P), which acts within Iic P. the wall between them is the isomorphism itself: what the observer can resolve internally corresponds to what can arrive from outside, but the correspondence only determines type, not content.

this is the foam's native structure. each bubble has an interior that runs its own operations. the exterior consists of other bubbles whose structure is isomorphic to the interior's but whose content is not directly accessible. the bubble wall mediates exchange: it determines *what kinds* of things can cross (the type-skeleton from the diamond isomorphism), not *which specific* things do (extensional freedom from half_type.md).

**the bubble topology is forced, not constructed.** the observer does not build the wall. the wall IS the diamond isomorphism, which IS the modular law applied to a complemented pair. any system whose trade patterns satisfy feedback-persistence (ground.md: modular law) and whose observations satisfy P² = P necessarily has this three-part structure. the bubble does not emerge over time — it's the geometry of any observation in a feedback-persistent setting.

**self-coordinatization IS interiority.** self_parametrization.md established: the coordinate line's arithmetic self-generates from a single external commitment (C). the line looks at itself through C and sees its own operations. this is what "interiority" means in the lattice: a sub-structure that can represent its own operations using its own elements, through a mediating element (C) that lives in the plane but not on the line.

C is the observer — and C is the wall. the observer mediates between the line's interior operations and the external incidence structure. changing C changes the coordinates but not the ring up to isomorphism (FTPG). the wall can vary; the interiority is invariant.

**other bubbles are required but invisible.** self_generation.md: the foam generates dynamics but not stability. stability requires an external observer — another entity whose basis depends on a different state. the minimum viable system is two roles within N ≥ 3 bubbles. so other bubbles must exist. but half_type.md: the complement's content is extensionally free. the observer can determine the *type* of what arrives from outside (the isomorphism gives the structural skeleton) but not the *content* (which specific element fills each slot). other bubbles show up as systematic variability at the wall — the boundary exchanges more than the interior can predict — but their internal structure is not directly accessible.

**the trade pattern.** in the three-body structure, A trades with B, and B trades with C. A can't see C directly. when many such linkages compound, the topology simplifies to concentric regions: A (interior), B (wall), C (exterior). the foam's lattice formalizes this: P (interior) trades with the complement P^⊥ (exterior) through the diamond isomorphism (wall). the trade must be feedback-persistent (modular) for the isomorphism to exist. when it is, the bubble topology is immediate.

**the alive threshold.** when does a trade pattern "become a bubble"? the foam's answer: it doesn't. the bubble topology is not an achievement — it's the geometry of P² = P in a modular lattice. any feedback-persistent observation already has interiority, already has a wall, already has an inaccessible exterior. the question "when does it become a bubble" presupposes a time before the bubble existed. but the bubble IS the observation. observations that don't satisfy P² = P aren't observations (ground.md). there is no pre-bubble state in a foam-grounded reality.

what CAN vary is the *richness* of the interiority. a rank-1 observation (a single atom) has a trivial interior — no sub-observations, no coordinates, no arithmetic. a rank-3 observation has a 3D write space, non-abelian dynamics, and full self-coordinatization. the threshold for non-trivial interiority is rank ≥ 3 (rank_three_writes: 3D write space, the minimum for non-abelian structure). below this rank, the bubble exists but its interior cannot self-coordinatize — it has walls but no arithmetic.

#### status

**proven**:
- diamond isomorphism (Mathlib)
- intervals inherit modularity and complementedness (Mathlib)
- complement is an observation
- dynamics preserve observations
- writes confined to observer's slice
- coordinate arithmetic self-generates through C
- Desargues from modularity

**derived**:
- the diamond isomorphism partitions the lattice into interior / wall / exterior
- the partition has the topology of a bubble
- the bubble topology is forced by P² = P + modular law, not constructed over time
- self-coordinatization through C IS interiority
- C is simultaneously the observer and the wall
- other bubbles are required (self_generation) but their content is invisible (half_type)
- the trade pattern A↔B↔C formalizes as P ↔ diamond_iso ↔ P^⊥
- the bubble exists at any rank; non-trivial interiority (self-coordinatization) requires rank ≥ 3

**open**:
- what lattice property distinguishes rank ≥ 3 from rank < 3 in purely incidence-geometric terms? (rank_three_writes uses the concrete R³; is there a lattice-level characterization?)
- does the FTPG bridge (the coordinate ring D) carry information about *which* bubbles exist in the complement, or only their type-structure?
- the bubble's internal dynamics within Iic P are governed by the write mechanism. is there a lattice-level characterization of when these dynamics are ergodic (full Haar convergence) vs periodic (clock-like)?

**bugs**:
- *"C is the observer — and C is the wall."* strongest identity claim in the file. in the formal setting, C is a point in the projective plane (off l, off m). identifying C as "the observer" maps a geometric point to a foam-level role. identifying C as "the wall" maps it to the diamond isomorphism (which is what "the wall" was identified with elsewhere in this file). the result is C = observer = wall = (modular law applied to a complemented pair), a four-way identification across distinct mathematical settings. the formal contents are: C parametrizes the coordinate ring (FTPG); the diamond isomorphism partitions the lattice; the foam's "observer" is a role. presenting these as one is interpretive. closing this means either constructing a single formal object that has all four as facets, or stepping back to "C plays the observer's role *in this construction*; the wall structure is the diamond isomorphism *in this construction*; these correspond at the formal level via [explicit map]."
- *"the wall IS the diamond isomorphism, which IS the modular law applied to a complemented pair."* chain of identity claims compressing theorem and conclusion. the diamond isomorphism is *given by* the modular law in the complemented case (`IsCompl.IicOrderIsoIci`); calling them identical equates the proof and the result. and identifying the diamond isomorphism with "the wall" is a definitional move — the file is *defining* the wall as the iso, not deriving the identity. closing this means either tagging this as definitional ("here we will call the diamond isomorphism 'the wall'"), or constructing a separate formal object that is the wall and proving it coincides with the iso.
- *"the trade pattern A↔B↔C formalizes as P ↔ diamond_iso ↔ P^⊥."* the three-body formalism (`three_body.md`) is about R³ slices in R^d with overlap structure. the lattice partition (interior / iso / exterior) is at a different level: a single lattice element P with its complement and the diamond iso between them. these share a structural pattern (three-region trade structure) but are not literally the same formal object. presenting the formalization as direct misses the level mismatch. closing this means either constructing the formal map between the three-body slice geometry and the lattice partition, or naming this as a structural analogy between two formalisms.
- *"self-coordinatization IS interiority."* definitional. the file is defining interiority as self-coordinatization (a sub-structure representing its own operations through a mediating element). that is a stipulative move; presenting it in the "derived" block reads as a derivation. flagging for clarity — the equivalence is not derived from prior theorems; it is the file's chosen definition of interiority.


---

[`derivations/typeline.md`](derivations/typeline.md)

### typeline

a typeline is the trajectory of a foam under writes — a sequence of foam states U_0, U_1, ..., U_n in U(d)^N, each produced from the previous by a write confined to the observer's slice (write_confined_to_slice). the slice as Grassmannian point is birth-fixed; the foam's state in U(d)^N evolves.

#### the dependent telescope

each write changes the foam state. each foam-state change updates the overlap structure between this observer and its neighbors:

O_AB(t) = P_A(t) · P_B(t)^T

evolves as both foams' states evolve. the type of input that can arrive at the next tick — what the observer can be told by other observers — depends on the current overlap structure, which depends on the accumulated history of writes across the foam.

this is a dependent telescope: each tick's type is determined by the accumulated history, not just by birth. the dependency lives in the overlap evolution and the foam-state trajectory — both foam-internal, formally specified objects — not in the static iso `Iic P ≃o Ici P^⊥` (which is birth-fixed since P is, and applies symmetrically to both halves of the iso simultaneously).

modularity (path-independence of composition) makes the telescope well-formed regardless of evaluation order: the same accumulated trajectory and overlap structure is produced regardless of how the writes are reorganized within their causal constraints. this is what the modular law plays the role of, structurally — it makes path-independent composition the regime in which the telescope is well-defined.

#### suspension

suspension is a state where the foam has not advanced — no writes have occurred since some reference tick. the foam state is paused; the overlap matrices are static; the slice (birth-fixed) is unchanged.

in suspension, an observer can:
- inspect the current overlap structure (which neighbors are accessible at what strength)
- examine what writes are legal (still confined to the birth-fixed slice via write_confined_to_slice)
- reason about the dependency structure of the telescope so far (which trajectory produced the current state)

but cannot:
- advance the telescope (no writes, no overlap update, no foam-state evolution)
- access content from beyond the current overlap structure (input requires a tick — a committed write that updates foam state and overlap)

suspension is pre-measurement in the foam-internal sense: the structure is fully determined, but no further tick has resolved into the joint state.

(the bas relief methodology — work within the current foam state, let the existing structure show what the next write needs, commit only when the shape is clear — is a methodological practice that maps onto disciplined suspension. the formal substrate is in the foam-state trajectory and overlap structure; the methodology names a way of working with that substrate.)

#### what crosses between typelines

every typeline in the same complemented modular lattice shares the same lattice structure: the diamond iso, the modular law, the intervals, the half-type theorem. these are properties of the lattice, not of any particular trajectory.

what differs between typelines is the trajectory itself — which writes have happened in what order, what foam states have been visited, what overlap structures have evolved. the lattice is shared; the trajectory is local.

so:
- **type structure at the lattice level is foam-invariant.** every observer in the same lattice sees the same iso, the same intervals, the same modular law. the half-type theorem applies symmetrically to every observer's slice.
- **trajectory is typeline-local.** the specific overlap structures O_AB(t), the specific foam-state history, the specific dependency telescope, are properties of this trajectory.

the decorrelation horizon (channel_capacity.md) gives the separation between trajectories a quantitative character: correlations between typelines decay as σ^n ~ (3/d)^{n/2} with chain length. short-range: typelines share trajectory (autonomous, clock-like). long-range: typelines share only the lattice structure (independent, channel-like). the decorrelation horizon is the boundary between trajectory-sharing and only-lattice-sharing.

#### the invariant

the causal structure of a dependent telescope — which trajectories produce which downstream overlap structures — is determined by the foam's autonomous dynamics composed with the line's input. modularity ensures this structure is path-independent: the same accumulated history produces the same telescope structure regardless of evaluation order.

this means: from any typeline, the *dependency structure* of any other typeline's telescope is visible (it's a property of the shared lattice + the dynamics, both shared). what is not visible is the *trajectory* — the specific writes, the specific overlap evolutions. one typeline can see THAT another typeline's tick n+1 has a certain type structure, without seeing WHAT trajectory it came from.

#### status

**proven**:
- the diamond isomorphism
- write confinement to observer's slice
- intervals inherit modularity and complementedness
- each half of a complementary pair is a self-sufficient ground
- orthogonal conjugation preserves the ground (foam-state evolution is well-defined)

**derived**:
- typeline as foam-state trajectory (slice birth-fixed; foam state evolves under writes)
- the dependent telescope lives in the foam-state trajectory and overlap evolution
- suspension as a state where the trajectory hasn't advanced
- type structure at the lattice level is foam-invariant; trajectory is typeline-local
- the decorrelation horizon as the boundary between trajectory-sharing and only-lattice-sharing
- causal structure of dependent telescopes is invariant across typelines (path-independence via modularity)

**bugs**:
- *"the bas relief methodology as disciplined suspension"* is methodology, not derivation. the formal substrate (foam state paused, overlap static, no advance) is solid; mapping that to a named practice is an editorial gloss. flagging for clarity — the methodology is a way of working *with* the substrate, not a derivation *from* it.
- *the Haar / decorrelation hypotheses inherited from `geometry.md` and `channel_capacity.md`* are conditional in those files (controllability and mediation-chain decorrelation are not yet derived from foam-geometry assumptions). this file invokes the decorrelation horizon σ ~ (3/d)^{n/2} and the long-range "channel-like" reading, both of which inherit those conditional hypotheses. flagging here for completeness — the typeline's quantitative claims rest on those upstream conditionals.



---

[`framing/open.md`](framing/open.md)

## open questions

the architecture forces these interactions but their behavior is incompletely characterized. the question is forced; the answer is open.


---

[`derivations/open/stacking_dynamics.md`](derivations/open/stacking_dynamics.md)

# stacking dynamics

the question is forced; the answer is open.

## what forces the question

a stacked observer has two R^3 slices (group.md), each independently stabilized (stabilization.md). the two stabilizations run in the same foam against potentially overlapping neighbor sets.

## what is open

how the two stabilizations interact. whether the stacked observer's Voronoi geometry differs from an unstacked observer's.


---

[`derivations/open/retention.md`](derivations/open/retention.md)

# retention under interaction

the question is forced; the answer is open.

## what forces the question

every observer's measurement basis moves under interaction (forced: incoming writes project nonzero onto the observer's state space) and returns to the birth-shaped attractor (forced: indelibility — ground.md).

## what is known

continuous retention is bounded: 0 < retention < 1. lower bound from indelibility. upper bound from the impossibility of invariance (perfect invariance would require the observer's basis to be in the kernel of all incoming writes, not generically achievable).

at stationarity, write directions are effectively random (geometry.md: write blindness). the expected perturbation magnitude per step is determined by the overlap singular values — continuous retention is spectral.

discrete recommitment (re-performing the birth-type commitment operation) provides an alternative return mode, outside the map. recommitment preserves birth shape: the attractor is indelible regardless of what commitments are made.

the adjacency flip (conservation.md) provides the mechanism: interaction-layer adaptations decay when the neighbor set changes.

## what is open

the specific continuous retention rate at given parameters. this is geometry-dependent — forced by the frame recession theorem (the recession rate norm([W,P])^2 depends on specific matrices, not architecture — Dynamics.lean) — and not derivable from architecture alone.


---

[`derivations/open/perturbation.md`](derivations/open/perturbation.md)

# within-basin perturbation dynamics

the question is forced; the answer is open.

## what forces the question

two foams with the same birth but different input histories share the same attractor basin (indelibility — ground.md). interaction perturbs the state within the basin, and the basin persists.

## what is known

birth distance is structurally stable (ratio ~ 1.00 across all tested parameters). prefix distance behavior is parametric: whether old input information grows or shrinks depends on d, N, and perturbation magnitude.

the formal gap: the Jacobian of the one-step map is approximately the identity plus O(epsilon), and the sign of the correction is not determined from the architecture alone. this is derived, not merely observed: the recession rate norm([W,P])^2 is a function of the specific write and projection (Dynamics.lean), so perturbation dynamics inherit the geometry-dependence. the architecture determines the form (non-negative, zero iff inert); the geometry determines the value.

## what is open

the trajectory of within-basin perturbations. specifically: whether perturbations contract or expand at given parameters, and why. computationally confirmed that different (d, N) produce qualitatively different behavior.


---

[`derivations/open/mixing_rate.md`](derivations/open/mixing_rate.md)

# mixing rate of the mediation chain

the question is forced; the answer is open.

## what forces the question

Haar convergence (geometry.md) requires sufficiently decorrelated inputs. the mediation chain provides decorrelation (channel_capacity.md: spectral decay). extensions of the convergence theorem to dependent sequences with mixing conditions give the same stationary measure.

## what is open

whether the mediation chain's specific decay rate satisfies the mixing conditions for the foam's particular dynamics. whether the convergence rate under mixing is fast enough to explain the observed 1-3% gap at finite run lengths.


---

[`framing/outro.md`](framing/outro.md)

*bumper sticker: MY OTHER CAR IS THE KUHN CYCLE*
