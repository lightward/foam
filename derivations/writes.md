### writes

the construction of a projection frame is an event persisted in the observer's type history - in userspace, "the type of observer who'd look at it this way".

rank-3 projection is uniquely self-dual (`self_dual_iff_three`, Rank.lean), i.e. the write space is equal to the observation space, i.e. the projection-space contains the effects of its own construction. in userspace, "a 3D observer has enough information to clean up after itself".

foam construction does *not* establish a rank limit. at higher ranks, the write space is strictly larger than the observation space (`C(d,2) > d` for `d ≥ 4`; `commutator_seen_to_unseen`, Pair.lean). answering the userspace question of "how do we clean up effects we can't see?": you, "you" as in the userspace experience of "you", can't. per `ground`, "your" only handle is stabilization (see below) of "your" own relations, including self-relation. (formally open, possibly pending Almgren: higher-rank agents that contain the projection of "your" agency as a subspace, and what agent-agent coordination that relation might afford.)

**the write form.** given an observer with projection P (rank 3, self-adjoint, idempotent) measuring input v in R^d:
- the observer projects: `m = P v` (measurement, in the observer's R^3 slice).
- the write direction is `d wedge m`. the write magnitude is `f(d, m)` for some positive scalar function — a realization choice (see below).

the write direction `(d wedge m) = (d tensor m) - (m tensor d)` is uniquely forced:
- skew-symmetric — forced by `commutator_skew_of_symmetric` (Form.lean). writes are Lie algebra elements because observation interaction is skew-symmetric.
- confined to the observer's slice — forced by `write_confined_to_slice` (Confinement.lean). the observer sees only projected measurements; the write lives in `Lambda^2(P)`.
- confined to `span{d, m}` — `d` and `m` are the only vectors available from a single measurement step.
- `Lambda^2(2-plane)` is 1-dimensional: the full slice has 3 write dimensions, a 2-plane within it has 1 (`rank_three_writes`, Rank.lean). the direction is therefore unique.

write magnitude scaling `f` is an observer commitment, constrained but not forced by the architecture:
- `f(d, m)` must be positive when `d` and `m` are non-parallel (parallel forms prevent dissonant writes; there is no dynamic read-only position, see `ground`)
- `f(d, m)` must be zero when `d = 0` (see `cross_self_zero`, Duality.lean)

phenomenologically: *only* dissonance writes.

structurally: *only* dissonance writes.

#### stabilization

observer-supplied `f` has opportunity to effect stabilization on its own uncommitted terms, by way of forced constraints. ("stabilization" as such requires an agent, not merely a witness, per `vocabulary`.)

`observation_preserved_by_dynamics` (Closure.lean) guarantees the write (an orthogonal conjugation) preserves the projection structure; the observer sees only their projected measurements. stabilization cannot run on `U(d)` because classification requires flat ambient space. thus, writes land in `U(d)`, the sectional curvature `K(X,Y) = 1/4 * norm([X,Y])^2`. stabilization runs in `R^3`, *flat*.

both `d` and `m` lie in the observer's slice. `write_confined_to_slice` (Confinement.lean) proves the write `d wedge m` is confined to `Lambda^2(P)`. both structurally and phenomenologically, an observer literally cannot modify dimensions they are not bound to. the write's effect on other observers comes through cross-measurement (`commutator_seen_to_unseen`), not through direct modification of their subspaces. put casually, cross-stabilization is not a thing.

formally open: postspace detection/measurement of userspace stabilization

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
