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
