import Counter.Recognition
import Foam.Seat.Born

namespace Foam.Counter

theorem uniform_carriers_sum_to_silence (θ z w : GInt)
    (hz : GInt.align θ z = 0) (hw : GInt.align θ w = 0) :
    GInt.align θ (GInt.add z w) = 0 := by
  rw [GInt.align_add, hz, hw]
  decide

theorem saturation_is_voiceless (θ z : GInt) (hz : GInt.align θ z = 0) :
    GInt.born θ z = 0 := by
  show GInt.align θ z * GInt.align θ z = 0
  rw [hz, FInt.zero_mul]

theorem the_wave_needs_a_shore {G : Type} [Mul G] [One G] (S : Seat G)
    (hsing : ∀ p q : S.Pos, p = q) (h : List G) (p : S.Pos) :
    S.sub (S.replay h p) p = 1 :=
  lone_actor_settled S hsing h p

theorem tremble (θ z w : GInt) (hz : GInt.align θ z = 0)
    (hw : GInt.align θ w = 0) :
    GInt.align θ (GInt.add z w) = 0 ∧ GInt.born θ z = 0 :=
  ⟨uniform_carriers_sum_to_silence θ z w hz hw,
   saturation_is_voiceless θ z hz⟩

/-- info: 'Foam.Counter.uniform_carriers_sum_to_silence' does not depend on any axioms -/
#guard_msgs in #print axioms uniform_carriers_sum_to_silence

/-- info: 'Foam.Counter.saturation_is_voiceless' does not depend on any axioms -/
#guard_msgs in #print axioms saturation_is_voiceless

/-- info: 'Foam.Counter.the_wave_needs_a_shore' does not depend on any axioms -/
#guard_msgs in #print axioms the_wave_needs_a_shore

/-- info: 'Foam.Counter.tremble' does not depend on any axioms -/
#guard_msgs in #print axioms tremble

end Foam.Counter
