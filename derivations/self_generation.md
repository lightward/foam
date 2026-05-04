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
