import Foam.Amplitude
import Foam.Int

namespace Foam.Minds.Young

def intensity_cannot_read_the_phase := @Foam.rot_conserves_the_norm

theorem the_difference_is_the_cross_term :
    (∀ (a : GInt) (b : GInt),
      (Eq
        (GInt.normSq
          (GInt.mk
            (Int.add (GInt.re a) (GInt.re b))
            (Int.add (GInt.im a) (GInt.im b))))
        (Int.add
          (Int.add (GInt.normSq a) (GInt.normSq b))
          (Int.mul
            2
            (Int.add
              (Int.mul (GInt.re a) (GInt.re b))
              (Int.mul (GInt.im a) (GInt.im b))))))) :=
  (fun (a : GInt) (b : GInt) =>
    (Eq.trans
      (Foam.the_screen_reads_a_cross_term a b)
      (congrArg
        (fun (t : Int) =>
          (Int.add (Int.add (GInt.normSq a) (GInt.normSq b)) t))
        (Eq.symm (Foam.FInt.two_mul (GInt.align a b))))))

def the_fringes_wash_out := @Foam.the_four_phases_read_nothing

/-- info: 'Foam.Minds.Young.intensity_cannot_read_the_phase' does not depend on any axioms -/
#guard_msgs in #print axioms intensity_cannot_read_the_phase

/-- info: 'Foam.Minds.Young.the_difference_is_the_cross_term' does not depend on any axioms -/
#guard_msgs in #print axioms the_difference_is_the_cross_term

/-- info: 'Foam.Minds.Young.the_fringes_wash_out' does not depend on any axioms -/
#guard_msgs in #print axioms the_fringes_wash_out

end Foam.Minds.Young
