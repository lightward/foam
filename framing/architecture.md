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
