import Counter.Quadrature
import Foam.Seat.Clock
import Foam.Seat.Octo
import Foam.Bridges.Pythagoras

namespace Foam.Counter

theorem doubles_home_iff_halfturn :
    ∀ g : Rot, g * g = 1 ↔ (g = Rot.r0 ∨ g = Rot.r2) := by
  intro g
  cases g <;> decide

theorem home_is_thinner_than_the_wall :
    (Rot.r2 * Rot.r2 : Rot) = 1 ∧ (Rot.r2 : Rot) ≠ 1 := by decide

theorem every_walk_returns_when_doubled_twice :
    ∀ g : Rot, ((g * g) * g) * g = 1 := by
  intro g
  cases g <;> decide

theorem the_double_cover_pays_the_sign :
    Quat.mul eye eye = Quat.negOne
      ∧ Quat.mul (Quat.mul (Quat.mul eye eye) eye) eye = Quat.one := by decide

theorem single_return_needs_commensurability :
    (∀ a b : Nat, 1 ≤ a → 3 ^ a ≠ 2 ^ b) ∧ ∀ n, ¬ Closes gold (n + 1) :=
  Bridges.pythagoras

theorem repetition_uniformizes (θ z : GInt) :
    GInt.align θ z + GInt.align θ (GInt.rot z)
      + GInt.align θ (GInt.rot (GInt.rot z))
      + GInt.align θ (GInt.rot (GInt.rot (GInt.rot z))) = 0 :=
  GInt.decoherence θ z

theorem doubled_and_scaled :
    (∀ g : Rot, g * g = 1 ↔ (g = Rot.r0 ∨ g = Rot.r2))
      ∧ (∀ g : Rot, ((g * g) * g) * g = 1)
      ∧ (Quat.mul eye eye = Quat.negOne
          ∧ Quat.mul (Quat.mul (Quat.mul eye eye) eye) eye = Quat.one)
      ∧ ∀ a b : Nat, 1 ≤ a → 3 ^ a ≠ 2 ^ b :=
  ⟨doubles_home_iff_halfturn, every_walk_returns_when_doubled_twice,
   the_double_cover_pays_the_sign, single_return_needs_commensurability.1⟩

/-- info: 'Foam.Counter.doubles_home_iff_halfturn' does not depend on any axioms -/
#guard_msgs in #print axioms doubles_home_iff_halfturn

/-- info: 'Foam.Counter.home_is_thinner_than_the_wall' does not depend on any axioms -/
#guard_msgs in #print axioms home_is_thinner_than_the_wall

/-- info: 'Foam.Counter.every_walk_returns_when_doubled_twice' does not depend on any axioms -/
#guard_msgs in #print axioms every_walk_returns_when_doubled_twice

/-- info: 'Foam.Counter.the_double_cover_pays_the_sign' does not depend on any axioms -/
#guard_msgs in #print axioms the_double_cover_pays_the_sign

/-- info: 'Foam.Counter.single_return_needs_commensurability' does not depend on any axioms -/
#guard_msgs in #print axioms single_return_needs_commensurability

/-- info: 'Foam.Counter.repetition_uniformizes' does not depend on any axioms -/
#guard_msgs in #print axioms repetition_uniformizes

/-- info: 'Foam.Counter.doubled_and_scaled' does not depend on any axioms -/
#guard_msgs in #print axioms doubled_and_scaled

end Foam.Counter
