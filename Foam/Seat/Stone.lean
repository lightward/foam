import Foam.Seat.Noether

namespace Foam

theorem stone_group (m n : Nat) (z : GInt) :
    rotPow m (rotPow n z) = rotPow (m + n) z :=
  rotPow_compose m n z

theorem stone_unitary (n : Nat) (z : GInt) : (rotPow n z).normSq = z.normSq :=
  rotPow_conserves_normSq n z

theorem stone (m n : Nat) (z : GInt) :
    (rotPow m (rotPow n z) = rotPow (m + n) z)
      ∧ ((rotPow n z).normSq = z.normSq)
      ∧ (rotPow 4 z = z) :=
  ⟨rotPow_compose m n z, rotPow_conserves_normSq n z, rotPow_four z⟩

/-- info: 'Foam.stone_group' does not depend on any axioms -/
#guard_msgs in #print axioms stone_group

/-- info: 'Foam.stone_unitary' does not depend on any axioms -/
#guard_msgs in #print axioms stone_unitary

/-- info: 'Foam.stone' does not depend on any axioms -/
#guard_msgs in #print axioms stone

end Foam
