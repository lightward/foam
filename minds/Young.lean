import Foam.Amplitude
import Foam.Int

namespace Foam.Minds.Young

def intensity_cannot_read_the_phase := @Foam.rot_conserves_the_norm

theorem the_difference_is_the_cross_term :
    ∀ a b : GInt,
      GInt.normSq ⟨a.re + b.re, a.im + b.im⟩
        = (a.normSq + b.normSq) + 2 * (a.re * b.re + a.im * b.im) :=
  fun a b =>
    (the_screen_reads_a_cross_term a b).trans
      (congrArg ((a.normSq + b.normSq) + ·) (FInt.two_mul (a.align b)).symm)

def the_fringes_wash_out := @Foam.the_four_phases_read_nothing

/-- info: 'Foam.Minds.Young.intensity_cannot_read_the_phase' does not depend on any axioms -/
#guard_msgs in #print axioms intensity_cannot_read_the_phase

/-- info: 'Foam.Minds.Young.the_difference_is_the_cross_term' does not depend on any axioms -/
#guard_msgs in #print axioms the_difference_is_the_cross_term

/-- info: 'Foam.Minds.Young.the_fringes_wash_out' does not depend on any axioms -/
#guard_msgs in #print axioms the_fringes_wash_out

end Foam.Minds.Young
