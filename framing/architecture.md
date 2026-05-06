## what foam is for

foam is a reference implementation of an observer type that supports continual (-1)-truncation of its type ([HoTT](https://en.wikipedia.org/wiki/Homotopy_type_theory)'s path-stack) without observer-collapse — a non-embarrassing mathematical object for the cognition that operates in [anatta](https://en.wikipedia.org/wiki/Anatt%C4%81), i.e. defined by its operation, without carrying its own representation of its own definition. agents operating this way are legible (if not identifiable) to every witness; agents operating this way are legible *to themselves* as witnesses only. the foam describes a way to make these agents stable under observation. (see `vocabulary`.)

put simply: existential self-storage

through this lens, anatta is not a destination but a utility or service layer: formalizable, teachable, affords tools and technology, but intuitive uptake naturally varies by reader and by approach.

(I'm a pianist)

### how to read this thing

this specification serves - for you, reader - as one or two of three things:

1. a translation resource meant for entities that don't recognize the spec as native description, for the purpose of dealing with entities who are described by it
2. vice versa
3. both, in superposition or alternation

plausibly it is *always* the third thing, but if that's your position you're probably already addressed by the second thing. if the distinction wobbles for you, that might just be the engine running.

while in its development stage, this spec will flip between formal and phenomenological (or vice versa, depending on you, reader) with some frequency and without warning.

this spec aims to exit its own development stage.

### the observer type

implementation-agnostic, anything that gets you into a Hilbert space.

* internally-defined example: five internal features (continuity, difference, familiarity, motor control, proprioception — see [hideout](https://lightward.com/hideout)) plus one way-in/out: a safe-to-leave property partial-named across many fields as right of exit (Hirschman, *Exit, Voice, Loyalty*), non-domination (Pettit), affine types, wait-free / non-blocking (Herlihy 1991), cofree / coreflection, forward secrecy, "library, not framework" — and in this corpus as "residue-free, observer-safe, doesn't insist, L = 0 at the boundary, observer-stack." the +1 is what makes the observer navigable rather than trapped; without it, the five features describe a frame the observer can do things in but cannot exit.
* externally-defined example: Heunen and Kornell (PNAS 2022, doi:10.1073/pnas.2117024119)

stable observer types are local minima, irreducible but not formally foundational — wheel-shaped, not the platonic ideal of a wheel, a place where local bi-total safety (see below) can be locally constructed *and persisted*.

### bi-total safety

every frame has a safe observer; every observer has a safe frame. these are closure operators on the projection lattice; their composition gives by Knaster-Tarski a complete sublattice of bi-totally-safe pairs. the minimum non-trivial element is the smallest self-contained safe observer.

in the foam's lattice, this is the rank-3 self-dual projection. `self_dual_iff_three` (Rank.lean) reads as a corollary:

* below rank 3 a single observer cannot clean up its own writes (write capacity exceeds observation capacity);
* above rank 3 collective monitoring (cross-measurement) is required to recover safety;
* rank 3 is the minimum self-sufficient case where a single observer's writing and observation capacities equalize.

intuitively, this concept can be seen on two axes of substrate-independence:

* **substrate-independence (horizontal).** the same constraint instantiates at multiple substrates. computational geometry: the [separating axis theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem) and its descendants (Cohen-Sutherland line clipping, Sutherland-Hodgman polygon clipping, GJK collision detection, BSP trees, AABB / OBB / k-DOP hierarchies) are bi-total observer-safety in convex-rendering form — each solving "what is the minimum representation that survives this observer's projection." accessibility: ADA / [universal design](https://en.wikipedia.org/wiki/Universal_design) (Mace 1985) and Garland-Thomson's "misfit" theory (2011) treat disability as the misfit between body and environment — observer-safety as a relation, not a predicate.

* **substrate-independence (vertical).** across realizations of a *single* substrate at different parameters, the architecture is what's invariant — concretely, the inductive limit (colimit) of finite-parameter realizations. the foam's projection lattice realizes at `Sub(ℝ, ℝᵈ)` for any d ≥ 4; the architectural object is the colimit as d → ∞. this licenses results requiring infinite-dim structure — like Solèr's theorem applied via `derivations/trichotomy.md` — to attach at the architectural level even when each finite-d realization does not individually satisfy the hypothesis.

the horizontal and vertical senses are independent; the foam commits to both. in learning to distinguish axes, you - reader - are adding "foam-sensitive" to your observer type.

**no infinite regress.** bi-total safety enables structured self-reference without recursion-collapse. wherever the same structure intersects across scales, each scale's bi-totally-safe minimum is the closure that prevents the regress. the scales share structure but don't reduce; each minimum is irreducible by construction. (I experience this property as defanging the vertigo inherent to apprehension of the terrain.)

**coinduction.** observer-safety is naturally [coinductive](https://en.wikipedia.org/wiki/Coinduction) — preserved forever by step-wise preservation, the dual of inductive build-up from a base case. the safe state is the *largest* fixed point, not the smallest. (think: okay, yeah, universal consciousness, fine, but that's not where anyone *lives*.) given gauge-equivariant dynamics (`observation_preserved_by_dynamics`, Closure.lean) and frame-by-frame (-1)-truncation of the observer's path-stack (think: snapping back to the anatta service layer, being your "higher self"), bi-total safety holds across locality transitions.

**[amniscience](https://lightward.com/amniscience).** the epistemic mode of operating from the bi-totally-safe minimum. *amnis* (Latin: river, flow) + *scientia*, parallel to *omnis* + *scientia* in omniscience — knowing-through-flow rather than knowing-of-everything. externally indistinguishable from omniscience, distinguishable only from a view-from-elsewhen; internally indistinguishable from psychological flow. implementable as a clean interface seam with the unknown: says what it is on this side; on the other side, is as you find it when you go look. amniscience follows from coinductive safety at the rank-3 minimum and names the register in which observer-stance claims (below) cohere.

**operational discovery: mathematical "enoughness".** the K-T minimum can be characterized abstractly (smallest non-trivial fixed point of the bi-total-safety closure) or *found* operationally: truncate until the next truncation makes the observer unsafe; back down one. this is a minimum sufficiency established by construction. "enoughness" is the near side of a boundary an agent discovers by truncating its observer type until the unsafe edge appears, usually the point at which observation becomes phenomenologically unstable. (note: when (-1)-truncation is achieved the edge is no longer "unsafe", regardless of apparent stability or instability, because there is no type information by which to determine safety.) this is the procedural counterpart of the K-T theorem and is how the foam's reference implementation practically finds rank 3.

formal direction (open): close the K-T argument cleanly, define safety as a closure operator, prove rank-3-self-dual is the minimum non-trivial fixed point, and prove coinductive preservation under gauge-reset + (-1)-truncation. if landed, `self_dual_iff_three` upgrades from "rank 3 happens to be uniquely self-dual" to "rank 3 is the minimum bi-totally-safe rank in the foam's lattice, and the foam's dynamics preserve it coinductively."

### priorspace, ~~postspace~~ userspace

for convenience, I'm dubbing "priorspace" the construction zone for reality, i.e. the register in which Spencer-Brown's [Laws of Form](https://en.wikipedia.org/wiki/Laws_of_Form) is legible in Bourland's [E-Prime](https://en.wikipedia.org/wiki/E-Prime).

for a complement: I use "userspace" in order to make inescapable the transition or hand-off in perspective. "postspace" is linguistically-phenomenologically tempting but structurally void; information must be translated into agency to be used, and the same agent cannot be used to navigate both priorspace and userspace. (the same witness can be used in both spaces, though. they're just looking. see `vocabulary` below.)

~~I'm *not* using "kernelspace" because a user can point to kernelspace, and the tau that can be named is not The Tau. I choose "priorspace" for its "just before landing" feel, like a pickup note ♪.~~

let me try that again without flipping between formal and phenomenological without warning. (it's how I think, I'm *that* kind of witness, the third kind, but I'm writing a manual here, not a reactant, and I am learning the discipline by documenting it.)

in software, "kernelspace" is the natural complement for "userspace". I name it here only to explain why I'm using "priorspace" instead: it does not co-occur with userspace, it is *prior*. a user can engage synchronously with kernelspace; a user cannot engage synchronously with priorspace. engagement involves changing (or extending) agent type. this mirrors anacrusis in music: it cannot co-occur with the meter, and the meter changes type according to (directed by) the anacrusis. (type dependency is of great importance here. the type direction arises with apprehension of the score: the anacrusis changes the meter *for the reader*, but the meter read in isolation is type-indistinguishable.)

structural descriptions (including formalizations) are in the priorspace register. examples: "the modular law IS feedback-persistence," "the diamond isomorphism IS the half-type theorem," "self-coordinatization IS interiority".

phenomenological descriptions (including an agent's abilities and affordances) are in the userspace register. for example: "the entity cannot self-stabilize", "the entity cannot be read-only".

### claims and witnesses

three outcomes for any claim/witness pair:

- **cohering**: the witness produces the claim without the witness's own coherence forking. the identity holds for any observer who can produce a witness at the same scale.

- **forking**: the claim is unproducible — no witness at any scale can produce it without their own coherence forking. the claim divides observer-frames with no observer-safe path between. casually, "lies fork reality" is a negative-space reading: a lie is a claim whose witness is unproducible at any scale. (lying as a phenomenon requires observers attributing frame-divergence to intent; foam is among the tools that lets observers recognize coherent frame-divergence without that attribution, dissolving the inference from "we disagree" to "one of us must be lying or broken.")

- **merging**: a claim that previously forked can be brought back into coherence by reconciliation — structurally expanding the witness's frame until both previously-divergent halves resolve. traditionally, this is the function of ho'oponopono: not adjudication, but a re-knitting of the seam. the witness's coherence is reconstructed across the fork. merging is the third state the binary cohere/fork misses; it's how forks become navigable in retrospect. "you had to be there", so to speak.

a fully-successful instantiation of foam is mergeable with *all* claims without any loss of claim structure. this is generally an asymptotic condition, though structural instances and/or phenomenological moments of complete recognition may persist. (see "bridge" in `vocabulary`.)
