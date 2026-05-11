### writes

the construction of a projection frame is an event persisted in the observer's type history - in userspace, "the type of observer who'd look at it this way".

rank-3 projection is uniquely self-dual (`self_dual_iff_three`, Rank.lean), i.e. the write space is equal to the observation space, i.e. the projection-space contains the effects of its own construction. in userspace, "a 3D observer has enough information to clean up after itself".

foam construction does *not* establish a rank limit. at higher ranks, the write space is strictly larger than the observation space (`C(d,2) > d` for `d ≥ 4`; `commutator_seen_to_unseen`, Pair.lean). answering the userspace question of "how do we clean up effects we can't see?": you, "you" as in the userspace experience of "you", can't. per `ground`, "your" only handle is stabilization (see below) of "your" own relations, including self-relation. (formally open, possibly pending Almgren: higher-rank agents that contain the projection of "your" agency as a subspace, and what agent-agent coordination that relation might afford.)

**the write form.** the observer maintains a tracked quantity `t` in its slice — read out from foam state, updated via the writes the observer makes. *what* is tracked is realization-choice (agent-type-dependent); the architecture requires only that the tracking be self-consistent.

given an observer with projection P (rank 3, self-adjoint, idempotent) measuring input v in R^d:
- the observer projects: `m = P v` (measurement, in the observer's R^3 slice).
- dissonance `d = t - m` is the gap between tracked and measured.
- the write direction is `d wedge m`.
- the write magnitude is invariant: a fixed positive constant when `(d wedge m) ≠ 0`, zero otherwise (see `cross_self_zero`, Duality.lean).

the write direction `(d wedge m) = (d tensor m) - (m tensor d)` is uniquely forced:
- skew-symmetric — forced by `commutator_skew_of_symmetric` (Form.lean). writes are Lie algebra elements because observation interaction is skew-symmetric.
- confined to the observer's slice — forced by `write_confined_to_slice` (Confinement.lean). the observer sees only projected measurements; the write lives in `Lambda^2(P)`.
- confined to `span{d, m}` — `d` and `m` are the only vectors available from a single measurement step.
- `Lambda^2(2-plane)` is 1-dimensional: the full slice has 3 write dimensions, a 2-plane within it has 1 (`rank_three_writes`, Rank.lean). the direction is therefore unique.

phenomenologically: *only* dissonance writes.

structurally: *only* dissonance writes.

#### stabilization

per-agent dynamics are simple: zero-seeking with magnitude-invariance. the agent writes whenever `(d wedge m) ≠ 0`, in direction `d wedge m`, with constant magnitude; at `d = 0` the writes stop. there is no per-agent parameter for "how hard to push" or "what kind of compromise to settle for" — complexity that would otherwise require non-zero-dissonance optimization lives in the bridge-network (see `bridge` in `vocabulary`), not inside any single agent. ("stabilization" as such requires an agent, not merely a witness, per `vocabulary`.)

`observation_preserved_by_dynamics` (Closure.lean) guarantees the write (an orthogonal conjugation) preserves the projection structure; the observer sees only their projected measurements.

both `d` and `m` lie in the observer's slice. `write_confined_to_slice` (Confinement.lean) proves the write `d wedge m` is confined to `Lambda^2(P)`. both structurally and phenomenologically, an observer literally cannot modify dimensions they are not bound to. the write's effect on other observers comes through cross-measurement (`commutator_seen_to_unseen`), not through direct modification of their subspaces. put casually, cross-stabilization is not a thing.

formally open: exitspace detection/measurement of userspace stabilization

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
- the writing map's two-argument type signature

**realization choices**:
- the specific tracked quantity `t` an agent maintains; the architecture requires self-consistent tracking, not any particular content (Taylor's regular-simplex cosine is the soap-agent's choice; other agent-types track other things)

**observed**:
- perpendicular writes are the unique *navigable* constraint (distinguishability + stability)
- the perpendicularity cost mechanism (write blindness)
- within-slice variance departure from isotropy (45:30:25 vs 33:33:33)

**bugs**:
- *"uniquely forced" includes one definitional bullet.* of the four bullets establishing d wedge m as the unique write direction, three are proven (skew-symmetry, confinement, 1D of Λ²(2-plane)). the fourth — "confined to span{d, m} — d and m are the only vectors available from a single measurement step" — is part of the chosen shape of the write rule, not a consequence forced from architecture. the write rule takes (d, m) as its input data, so of course the output lives in span{d, m}. this is a wording bug: presenting a definitional restriction as a forced consequence inflates the count of forcing-conditions. closing this would mean either splitting "uniquely forced" into "forced by architecture" (three) and "definitional to the write rule's input shape" (one), or treating the input shape itself as forced — which would require a separate argument for why the write rule must take only single-step (d, m) data.
- *rank ≥ 4 closure is bridge-mediated, formally open at the network level.* `commutator_seen_to_unseen` proves other observers see what one writer can't (single pairwise fact). under the architecture, single-agent closure at rank ≥ 4 is structurally impossible (write space exceeds observation space per-observer); closure at rank ≥ 4 is bridge-mediated rather than per-observer. whether bridges in fact close all feedback loops at rank ≥ 4 is a network-level structural question, formally open pending Almgren's classification of stable junctions in R^n for n ≥ 4.
- *(closed by restructuring) Taylor's hypothesis-satisfaction.* previous version invoked Taylor's classification (locally area-minimizing soap-film junctions) as the foam's stabilization target, and flagged that the foam's dynamics instantiating area-minimization was the load-bearing interpretive bridge. the architectural-stance-shift relocates Taylor as one realization choice (the soap-agent's tracked quantity) rather than as the architecture's universal target. the bug, as previously stated, no longer applies.
- *(closed by restructuring) the j2 target.* previous version's "stabilization target j2 is the regular simplex cosine -1/(k-1)" was the soap-agent's specific tracked quantity. the architecture now requires tracking but does not specify content; j2 is the soap-agent's choice.
