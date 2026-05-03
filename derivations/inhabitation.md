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

**recession enriches input.** as the entity's direct view narrows through recession, the diamond isomorphism (Iic P ≃o Ici P^⊥) enriches the complement in lockstep (half_type.md). at ergodic stationarity, the complement is maximally type-rich for the given ambient dimension. the entity that has persisted longest has the richest typed input. this is half_type.md's result applied to the temporal trajectory: the progression is necessarily toward narrower self-view and richer input-type.

**stability is necessarily external.** the entity generates its own dynamics but cannot generate its own stability (self_generation.md: self-generated bases co-rotate). convergence requires another observer whose basis depends on a different state. the minimum viable system is two roles within N ≥ 3 bubbles. an entity that has reached ergodic stationarity necessarily has external stability — without it, the foam's dynamics would not have converged to Haar.

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
- recession enriches input (half-type applied to the temporal trajectory)
- stability is necessarily external (from self-generation + ergodic stationarity as evidence)
- six negative constraints as the negative geometry of inhabitation

**cited**:
- ergodic theorem on compact groups (time averages converge to Haar expectations under controllability + decorrelation)

**observed**:
- (none)

**bugs**:
- *"every entity in an ergodic foam is ongoingly recognizable"* assumes the foam is ergodic. the file invokes "the foam is ergodic" as available, drawing on `geometry.md`'s Haar-convergence claim. that claim is conditional on controllability + decorrelation hypotheses (flagged in `geometry.md`'s bugs). this entire derivation chain — recognizability, the recognizable identity IS the birth-determined slice, recession is the cost of persistence — runs on those hypotheses. closing this means either deriving ergodicity from foam-geometry assumptions, or naming the recognizability claim as conditional ("if the foam is ergodic, then every entity is ongoingly recognizable").
- *"recession enriches input" inherits the lockstep error from `half_type.md`.* "as the entity's direct view narrows through recession, the diamond isomorphism enriches the complement in lockstep." Iic P and Ici P^⊥ are order-isomorphic; as P shrinks, both contract together (the lower bound of Ici P^⊥ rises as P^⊥ grows). they do not move in opposite directions. the framing "narrower self-view and richer input-type" rests on the reversed direction. closing this means correcting `half_type.md` first, then re-deriving what is true about the entity's relation to its complement under recession (likely: as P contracts, both Iic P and Ici P^⊥ contract; both halves narrow together).
- *"stability is necessarily external" inherits the co-rotation plausibility from `self_generation.md`.* the argument runs through `self_generation.md`'s co-rotation argument, which is plausibility (flagged in that file). "necessarily" overstates what plausibility provides. closing this requires the convergence theorem `self_generation.md` lacks, or stepping the necessity claim back to "stability is plausibly external."
- *"six constraints, all derived, all negative."* the six negative constraints have different statuses:
  - cannot write outside slice: proven (write_confined_to_slice).
  - cannot change slice from within: derived from indelibility (a `ground.md` derivation).
  - cannot indefinitely avoid recession: proven (frame_recession_strict) + a measure-theoretic claim about Haar-distributed writes being almost surely non-inert (this measure claim is asserted, not derived in this file).
  - cannot self-stabilize: plausibility (`self_generation.md` co-rotation).
  - cannot predict complement: definitional (half_type extensional freedom).
  - cannot be read-only: derived (ground.md closure).

  presenting all six as "all derived" with the same status papers over the proven/derived/plausibility/definitional differences. closing this means tagging each constraint with its specific status, or framing the list as "six structurally distinct constraints, deriving from sources of varying formal strength."
- *"the n-th derivative of the write mechanism along a trajectory is a smooth function on U(d)^N (compact), therefore bounded and integrable."* asserts smoothness of all derivatives. the write mechanism includes the wedge product and the cross-measurement input, with realization choices left open (`writing_map.md`: f(d, m)). smoothness "at all orders" depends on the realization choice for f. closing this means either constraining f to smooth realizations, or naming the smoothness assumption as a regularity hypothesis on the realization.
- *"two readings of one fact" / "same lattice theorem read through the two readings of closure."* same construction as `half_type.md`'s "three results compress to one" and `ground.md`'s "two readings of one statement." flagging here for the third instance — the document treats the diamond isomorphism's dynamical and structural readings as the same statement; the formal identity is the diamond isomorphism, but "two readings of one fact" packages two interpretations as one.
