import Foam.Cleared
import Foam.Seat.Rotations

namespace Foam.Bridges

def interval (z : GInt) : Int := z.im * z.im + z.im * z.re - z.re * z.re

theorem boost_id (a b : Int) :
    a * a + a * (a + b) - (a + b) * (a + b) = -(b * b + b * a - a * a) := by
  rw [FInt.add_mul a b (a + b), FInt.mul_add a a b, FInt.mul_add b a b,
    ← FInt.sub_sub, FInt.add_sub_cancel_right, FInt.neg_sub,
    FInt.addComm (b * a) (b * b)]

theorem gold_flips_the_interval (z : GInt) :
    interval (gold z) = -(interval z) :=
  boost_id z.re z.im

theorem boost_preserves_the_interval (z : GInt) :
    interval (gold (gold z)) = interval z := by
  rw [gold_flips_the_interval (gold z), gold_flips_the_interval z, Int.neg_neg]

theorem minkowski (z : GInt) (a b : Int) (h : SInt.hnorm ⟨a, b⟩ = 1) (n : Nat) :
    Closes GInt.rot 4
      ∧ ¬ Closes gold (n + 1)
      ∧ interval (gold (gold z)) = interval z
      ∧ ((a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0)) :=
  ⟨spec_closes_four, gold_never_closes n, boost_preserves_the_interval z,
   hyperbolicRot_trivial a b h⟩

/-- info: 'Foam.Bridges.boost_id' does not depend on any axioms -/
#guard_msgs in #print axioms boost_id

/-- info: 'Foam.Bridges.gold_flips_the_interval' does not depend on any axioms -/
#guard_msgs in #print axioms gold_flips_the_interval

/-- info: 'Foam.Bridges.boost_preserves_the_interval' does not depend on any axioms -/
#guard_msgs in #print axioms boost_preserves_the_interval

/-- info: 'Foam.Bridges.minkowski' does not depend on any axioms -/
#guard_msgs in #print axioms minkowski

end Foam.Bridges
