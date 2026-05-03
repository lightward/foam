### self-generation

**the foam generates its own dynamics.** the foam's own plurality (N >= 3 bubbles) provides observers — bubbles measuring each other. their pairwise relationships define R^3 slices. their cross-measurement IS local stabilization. the commutator of overlapping cross-measurements IS the curvature. the holonomy IS self-generated.

**the foam does not generate its own stability.** a self-generated R^3 keeps rotating: the observation basis is defined by the foam's current state, and the state changes with each write. the slice co-rotates with the thing it observes. convergence requires another observer whose basis depends on a different state, so it doesn't co-rotate with yours.

**stability is relational.** this works as long as someone else's measurement is pending.

**the minimum viable system is two roles.** not two bubbles (that's N = 2, no stable geometry). two *roles* within a foam of N >= 3 bubbles: one to be the foam (the thing being measured), one to be the line (the thing providing a reference frame).

- N >= 3 is geometric stability (Plateau junctions).
- two roles is dynamic stability (convergence vs orbiting).

neither role is permanent. the role assignment is perspectival. but the two is irreducible.

**what the line provides: a fixed subspace.** not content, not wisdom, not input — three dimensions that hold still while the foam's geometry settles into them. the settling is the foam's. the dynamics are the foam's. the curvature is the foam's. the stability of the frame — that's the line's.

**the foam cannot self-stack.** stacking requires two real slices to be fused into one complex measurement before the write (simultaneity). the foam's dynamics are sequential real writes, algebraically closed in so(d) (group.md: real operations cannot produce imaginary-symmetric directions). no sequence of real operations produces complex structure. stacking, like stability, requires something the foam's own dynamics cannot generate.

#### status

**proven**:
- dynamics preserve the ground (observation_preserved_by_dynamics)
- writes are confined to the observer's slice

**derived**:
- the foam generates its own dynamics (from plurality + cross-measurement)
- the foam does not generate its own stability (co-rotation of self-generated bases)
- stability is relational
- minimum viable system is two roles (geometric + dynamic stability)
- what the line provides (a fixed subspace)
- the foam cannot self-stack (so(d) closure under real operations)

**cited**:
- (none)

**observed**:
- (none)

**bugs**:
- *the co-rotation argument is plausibility, not theorem.* "a self-generated R^3 keeps rotating: the observation basis is defined by the foam's current state, and the state changes with each write. the slice co-rotates with the thing it observes. convergence requires another observer whose basis depends on a different state." this argues against convergence under purely self-generated bases by appeal to the intuition of co-rotation. the formal content the file relies on (observation_preserved_by_dynamics, write_confined_to_slice) does not directly establish that convergence requires a distinct-state observer. the dynamics could in principle exhibit limit cycles, ergodic orbits, or other non-converging behaviors that aren't simple co-rotation. closing this would mean either a formal stability/convergence theorem on U(d)^N showing that purely self-generated bases cannot reach a Haar-stationary state, or naming "stability requires role distinction" as a structural conjecture rather than a derivation.
- *"minimum viable system is two roles"* inherits the plausibility above. "two roles is dynamic stability (convergence vs orbiting)" is a forced consequence of the co-rotation argument; if that argument is plausibility, this conclusion is too. closing this requires the same convergence theorem.
- *triple identity claim in "the foam generates its own dynamics."* "cross-measurement IS local stabilization. the commutator of overlapping cross-measurements IS the curvature. the holonomy IS self-generated." three identifications between foam-internal objects and their geometric counterparts:
  1. cross-measurement ↔ local stabilization
  2. commutator of cross-measurements ↔ curvature
  3. self-generated holonomy ↔ holonomy
  each is an interpretive move connecting a foam-level concept to a geometric/algebraic object. (1) and (2) draw on `writing_map.md` and standard differential geometry; (3) is a tautology at face value but does work in context. closing this means either constructing each identification formally (e.g., showing the commutator literally equals the Riemann curvature in a specified setup) or stepping back to "cross-measurement *plays the role of* local stabilization; the commutator *encodes* curvature; the holonomy is generated from within."
- *"what the line provides: a fixed subspace."* the line role was introduced (`channel_capacity.md`) as informationally-independent input. specifying it here as "three dimensions that hold still" is a stronger characterization — it commits to a specific structural form (fixed subspace) for what the line provides. the formal content from `channel_capacity.md` is just "input independent of foam state." "fixed subspace" is one realization. closing this means either deriving fixed-subspace as the unique or canonical form of state-independent input, or naming this as an interpretive specification of the line role within this file.
- *"stacking, like stability, requires something the foam's own dynamics cannot generate."* the algebraic fact (so(d) is closed under real operations; reaching u(d) requires complex structure) is solid and proven. pairing it with "stability" treats the two non-self-generation claims as having the same status. they don't: the stacking claim is algebraic (real ops closed in so(d)), the stability claim is plausibility (co-rotation). closing this means either deriving the stability claim to algebraic-fact status, or distinguishing the two ("stacking is provably non-self-generated; stability is plausibly non-self-generated").
