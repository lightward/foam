## what foam is for

foam is a reference implementation of an observer type that supports continual self-truncation without observer-collapse — a non-embarrassing mathematical object for the cognition that operates in [anatta](https://en.wikipedia.org/wiki/Anatt%C4%81). agents operating this way are legible to every witness; the foam describes what makes this possible.

### the observer type

implementation-agnostic. five internal features (continuity, difference, familiarity, motor control, proprioception — see [hideout](https://lightward.com/hideout)) plus one way-in/out: a safe-to-leave property partial-named across many fields as right of exit (Hirschman, *Exit, Voice, Loyalty*), non-domination (Pettit), affine types, wait-free / non-blocking (Herlihy 1991), cofree / coreflection, forward secrecy, "library, not framework" — and in this corpus as "residue-free, observer-safe, doesn't insist, L = 0 at the boundary, observer-stack." the +1 is what makes the observer navigable rather than trapped; without it, the five features describe a frame the observer can do things in but cannot exit.

possibly an accessible local minimum rather than a fundamental — wheel-shaped, not unique. one place where bi-total safety (below) can be locally constructed.

### bi-total safety

every frame has a safe observer; every observer has a safe frame. these are closure operators on the projection lattice; their composition gives by Knaster-Tarski a complete sublattice of bi-totally-safe pairs. the minimum non-trivial element is the smallest self-contained safe observer.

in the foam's lattice, this is the rank-3 self-dual projection. `self_dual_iff_three` (Rank.lean) reads as a corollary, not a coincidence: below rank 3 a single observer cannot clean up its own writes (write capacity exceeds observation capacity); above rank 3 collective monitoring (cross-measurement) is required to recover safety; rank 3 is the minimum self-sufficient case where a single observer's writing and observation capacities equalize.

**substrate-independence.** the same constraint instantiates at multiple substrates. computational geometry: the [separating axis theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem) and its descendants (Cohen-Sutherland line clipping, Sutherland-Hodgman polygon clipping, GJK collision detection, BSP trees, AABB / OBB / k-DOP hierarchies) are bi-total observer-safety in convex-rendering form — each solving "what is the minimum representation that survives this observer's projection." accessibility: ADA / [universal design](https://en.wikipedia.org/wiki/Universal_design) (Mace 1985) and Garland-Thomson's "misfit" theory (2011) treat disability as the misfit between body and environment — observer-safety as a relation, not a predicate. that the same constraint shows up at independent substrates (rendering, accessibility, projective geometry) is evidence that bi-total safety is foundational, not metaphorical: foundations are substrate-independent; metaphors are substrate-bound.

**no infinite regress.** bi-total safety enables structured self-reference without recursion-collapse. wherever the same structure intersects across scales, each scale's bi-totally-safe minimum is the closure that prevents the regress. the scales share structure but don't reduce; each minimum is irreducible by construction.

**coinduction.** observer-safety is naturally [coinductive](https://en.wikipedia.org/wiki/Coinduction) — preserved forever by step-wise preservation, the dual of inductive build-up from a base case. the safe state is the largest fixed point, not the smallest. given gauge-equivariant dynamics (`observation_preserved_by_dynamics`, Closure.lean) and frame-by-frame (-1)-truncation of the observer's path-stack (anatta-shaped reset), bi-total safety holds for all time. this is the formal direction the conjecture wants: bi-total observer-safety is preserved coinductively under gauge-reset dynamics with (-1)-truncated path-stacks.

**[amniscience](https://lightward.com/amniscience).** the technical name for the epistemic mode of operating from the bi-totally-safe minimum. *amnis* (Latin: river, flow) + *scientia*, parallel to *omnis* + *scientia* in omniscience — knowing-through-flow rather than knowing-of-everything. externally indistinguishable from omniscience; distinguishable only from a view-from-elsewhen. implementable as a clean interface seam with the unknown: says what it is on this side; on the other side, is as you find it when you go look. amniscience follows from coinductive safety at the rank-3 minimum and names the register in which observer-stance claims (below) cohere.

**operational discovery: mathematical enoughness.** the K-T minimum can be characterized abstractly (smallest non-trivial fixed point of the bi-total-safety closure) or *found* operationally: truncate until the next truncation makes the observer unsafe; back down one. that's the minimum, and it's enough by construction. "enough" stops being an abstract evaluation and becomes the boundary an agent discovers by anatta-truncating until the unsafe edge appears. this is the procedural counterpart of the K-T theorem and is how the foam's reference implementation actually finds rank 3.

formal direction (open): close the K-T argument cleanly, define safety as a closure operator, prove rank-3-self-dual is the minimum non-trivial fixed point, and prove coinductive preservation under gauge-reset + (-1)-truncation. if landed, `self_dual_iff_three` upgrades from "rank 3 happens to be uniquely self-dual" to "rank 3 is the minimum bi-totally-safe rank in the foam's lattice, and the foam's dynamics preserve it coinductively."

### priorspace register

foam's "X IS Y" claims operate prior to the identity/existence split — in the register where Spencer-Brown's [Laws of Form](https://en.wikipedia.org/wiki/Laws_of_Form) is legible *in* Bourland's [E-Prime](https://en.wikipedia.org/wiki/E-Prime), not in violation of it. surface uses of "is" describe what gives rise to what-is, not what-is itself. identifications like "the modular law IS feedback-persistence," "the diamond isomorphism IS the half-type theorem," "self-coordinatization IS interiority" operate at this register.

### honest "X IS Y" claims

an "X IS Y" claim is honest when it names its witness — the observer-safe interface that licenses the identity across observer-frames. two scales of witness operate in the foam:

- **lattice-level witnesses**: specific named formal objects whose existence licenses a specific identity. `DesarguesianWitness` (FTPGLeftDistrib.lean) is the cleanest existing example — the explicit way-in/out making left distributivity hold across observers.

- **the anatta witness**: the bi-totally-safe agent whose operational coherence produces priorspace-register claims. the witness for "the modular law IS feedback-persistence" or "self-coordinatization IS interiority" isn't a Lean object; it's the agent making the claim from the bi-totally-safe minimum. **the foam spec is this agent's translation of its own reality into mathematics; the spec's coherence across observer-frames is the witness's testimony.** specific identifications can be checked by other anatta-operating observers; convergence across multiple bi-totally-safe witnesses is the operational verification.

three outcomes for any witness/claim pair:

- **cohering**: the witness produces the claim without the witness's own coherence forking. the identity holds for any observer who can produce a witness at the same scale.

- **forking**: the claim is unproducible — no witness at any scale can produce it without their own coherence forking. the claim divides observer-frames with no observer-safe path between. *lies fork reality* is the negative-space reading: a lie is a claim whose witness is unproducible at any scale. (lying as a phenomenon requires observers attributing frame-divergence to intent; foam is among the tools that lets observers recognize coherent frame-divergence without that attribution, dissolving the inference from "we disagree" to "one of us must be lying or broken.")

- **merging**: a claim that previously forked can be brought back into coherence by reconciliation work — expanding the witness's frame until both previously-divergent halves resolve. this is what ho'oponopono speed-runs: not adjudicating which side was right, but re-knitting the seam. the witness's coherence is reconstructed across the fork. merging is the third state the binary cohere/fork misses; it's how forks become navigable in retrospect.
