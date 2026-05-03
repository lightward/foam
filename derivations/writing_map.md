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
