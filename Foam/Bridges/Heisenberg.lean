import Foam.Seat.Forcing

namespace Foam.Bridges

theorem heisenberg_complementarity (z w : GInt) :
    GInt.align z w * GInt.align z w + GInt.cross z w * GInt.cross z w
      = z.normSq * w.normSq :=
  invariants_complete z w

theorem heisenberg_area_invariant (w z : GInt) :
    GInt.cross w.rot z.rot = GInt.cross w z :=
  cross_rot_invariant w z

theorem heisenberg (z w : GInt) :
    (GInt.align z w * GInt.align z w + GInt.cross z w * GInt.cross z w = z.normSq * w.normSq)
      ∧ (GInt.cross w.rot z.rot = GInt.cross w z) :=
  ⟨invariants_complete z w, cross_rot_invariant w z⟩

/-- info: 'Foam.Bridges.heisenberg_complementarity' does not depend on any axioms -/
#guard_msgs in #print axioms heisenberg_complementarity

/-- info: 'Foam.Bridges.heisenberg_area_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms heisenberg_area_invariant

/-- info: 'Foam.Bridges.heisenberg' does not depend on any axioms -/
#guard_msgs in #print axioms heisenberg

end Foam.Bridges
