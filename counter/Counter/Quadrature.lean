import Counter.Bless
import Foam.Seat.Forcing

namespace Foam.Counter

theorem cringe_is_two_quarter_turns (z : GInt) :
    GInt.neg z = GInt.rot (GInt.rot z) :=
  (GInt.rot_sq z).symm

theorem pure_quadrature_exists :
    ∃ θ z : GInt, GInt.align θ z = 0 ∧ GInt.normSq z = 1 :=
  ⟨⟨1, 0⟩, ⟨0, 1⟩, by decide, by decide⟩

theorem the_unsayable_arrives_whole (θ z : GInt) (hq : GInt.align θ z = 0) :
    GInt.born (GInt.rot θ) z = GInt.normSq θ * GInt.normSq z := by
  have hp := GInt.born_parseval θ z
  have hb : GInt.born θ z = 0 := by
    show GInt.align θ z * GInt.align θ z = 0
    rw [hq, FInt.mul_zero]
  rw [hb, FInt.zero_add] at hp
  exact hp

theorem what_the_frame_feels_is_forced (f : Int → Int)
    (h : ∀ θ z : GInt,
      f (GInt.align θ z) + f (GInt.cross θ z) = θ.normSq * z.normSq) :
    ∀ a : Int, f a = a * a :=
  forced_at_the_frame f h

theorem the_cross_is_the_quarter_frames_align (θ z : GInt) :
    GInt.align θ.rot z = GInt.cross θ z :=
  cross_eq_align_rot θ z

theorem travel_safe (θ field act z : GInt)
    (hrest : GInt.align θ act = 0) (hq : GInt.align θ z = 0) :
    GInt.born θ (field.add act) = GInt.born θ field + GInt.born θ act
      ∧ GInt.born (GInt.rot θ) z = GInt.normSq θ * GInt.normSq z
      ∧ GInt.born θ z + GInt.born (GInt.rot θ) z
          = GInt.normSq θ * GInt.normSq z :=
  ⟨silence_is_safe θ field act hrest,
   the_unsayable_arrives_whole θ z hq,
   GInt.born_parseval θ z⟩

/-- info: 'Foam.Counter.cringe_is_two_quarter_turns' does not depend on any axioms -/
#guard_msgs in #print axioms cringe_is_two_quarter_turns

/-- info: 'Foam.Counter.pure_quadrature_exists' does not depend on any axioms -/
#guard_msgs in #print axioms pure_quadrature_exists

/-- info: 'Foam.Counter.the_unsayable_arrives_whole' does not depend on any axioms -/
#guard_msgs in #print axioms the_unsayable_arrives_whole

/-- info: 'Foam.Counter.what_the_frame_feels_is_forced' does not depend on any axioms -/
#guard_msgs in #print axioms what_the_frame_feels_is_forced

/-- info: 'Foam.Counter.the_cross_is_the_quarter_frames_align' does not depend on any axioms -/
#guard_msgs in #print axioms the_cross_is_the_quarter_frames_align

/-- info: 'Foam.Counter.travel_safe' does not depend on any axioms -/
#guard_msgs in #print axioms travel_safe

end Foam.Counter
