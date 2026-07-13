import Mathlib.Analysis.InnerProductSpace.TwoDim
import Foam.Seat.Forcing

namespace Foam.Bridges

open Complex

attribute [local instance] Complex.finrank_real_complex_fact

def toPlane (z : GInt) : ℂ := ⟨(z.re : ℝ), (z.im : ℝ)⟩

theorem the_tick_is_recognized (z : GInt) :
    toPlane z.rot = Complex.I * toPlane z := by
  apply Complex.ext
  · show ((-z.im : ℤ) : ℝ) = (Complex.I * toPlane z).re
    simp [toPlane, Complex.mul_re]
  · show ((z.re : ℤ) : ℝ) = (Complex.I * toPlane z).im
    simp [toPlane, Complex.mul_im]

theorem the_right_angle_is_the_rot (z : GInt) :
    Complex.orientation.rightAngleRotation (toPlane z) = toPlane z.rot := by
  rw [Complex.rightAngleRotation, the_tick_is_recognized]

theorem the_cross_is_the_area (θ z : GInt) :
    Complex.orientation.areaForm (toPlane θ) (toPlane z) = (GInt.cross θ z : ℝ) := by
  rw [Complex.areaForm]
  simp [toPlane, Complex.mul_im, GInt.cross]
  push_cast
  ring

/-- info: 'Foam.Bridges.the_tick_is_recognized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_tick_is_recognized

/-- info: 'Foam.Bridges.the_right_angle_is_the_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_right_angle_is_the_rot

/-- info: 'Foam.Bridges.the_cross_is_the_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_cross_is_the_area

end Foam.Bridges
