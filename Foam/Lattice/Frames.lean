import Foam.Lattice.Dial

namespace Foam.Lattice

def normK (κ : Int) (z : GInt) : Int := z.re * z.re - κ * (z.im * z.im)

def alignK (κ : Int) (w z : GInt) : Int := w.re * z.re - κ * (w.im * z.im)

def crossK (w z : GInt) : Int := w.re * z.im - w.im * z.re

theorem alignK_axis (κ a : Int) : alignK κ ⟨a, 0⟩ ⟨1, 0⟩ = a := by
  show a * 1 - κ * (0 * 0) = a
  rw [Int.mul_one, Int.mul_zero, Int.mul_zero, Int.sub_zero]

theorem crossK_axis (a : Int) : crossK ⟨a, 0⟩ ⟨1, 0⟩ = 0 := by
  show a * 0 - 0 * 1 = 0
  rw [Int.mul_zero, Int.zero_mul, Int.sub_zero]

theorem normK_axis_a (κ a : Int) : normK κ ⟨a, 0⟩ = a * a := by
  show a * a - κ * (0 * 0) = a * a
  rw [Int.mul_zero, Int.mul_zero, Int.sub_zero]

theorem normK_axis_one (κ : Int) : normK κ ⟨1, 0⟩ = 1 := by
  show 1 * 1 - κ * (0 * 0) = 1
  rw [Int.mul_one, Int.mul_zero, Int.mul_zero, Int.sub_zero]

theorem forced_at_the_frame_kappa (κ : Int) (f : Int → Int)
    (h : ∀ w z : GInt, f (alignK κ w z) - κ * f (crossK w z) = normK κ w * normK κ z) :
    ∀ a : Int, f a = a * a + κ * f 0 := by
  intro a
  have ha := h ⟨a, 0⟩ ⟨1, 0⟩
  rw [alignK_axis κ a, crossK_axis a, normK_axis_a κ a, normK_axis_one κ,
      Int.mul_one] at ha
  rw [← Int.sub_add_cancel (a := f a) (b := κ * f 0), ha]

theorem zero_point_kappa (κ : Int) (f : Int → Int)
    (h : ∀ w z : GInt, f (alignK κ w z) - κ * f (crossK w z) = normK κ w * normK κ z) :
    (1 - κ) * f 0 = 0 := by
  have hf0 := forced_at_the_frame_kappa κ f h 0
  rw [Int.zero_mul, Int.zero_add] at hf0
  rw [Int.sub_eq_add_neg, Int.add_mul, Int.one_mul, Int.neg_mul, ← hf0, Int.add_right_neg]

theorem normK_frame_dependent : ∃ z : GInt, normK (-1) z ≠ normK 1 z :=
  ⟨⟨1, 1⟩, by decide⟩

def galileanBoost (v : Int) (z : GInt) : GInt := ⟨z.re, v * z.re + z.im⟩

theorem galilean_preserves_time (v : Int) (z : GInt) :
    (galileanBoost v z).re = z.re := rfl

theorem galilean_velocities_add (v1 v2 : Int) (z : GInt) :
    galileanBoost v2 (galileanBoost v1 z) = galileanBoost (v2 + v1) z := by
  show (⟨z.re, v2 * z.re + (v1 * z.re + z.im)⟩ : GInt) = ⟨z.re, (v2 + v1) * z.re + z.im⟩
  rw [Int.add_mul v2 v1 z.re, Int.add_assoc (v2 * z.re) (v1 * z.re) z.im]

/-- info: 'Foam.Lattice.forced_at_the_frame_kappa' depends on axioms: [propext] -/
#guard_msgs in #print axioms forced_at_the_frame_kappa

/-- info: 'Foam.Lattice.zero_point_kappa' depends on axioms: [propext] -/
#guard_msgs in #print axioms zero_point_kappa

/-- info: 'Foam.Lattice.normK_frame_dependent' does not depend on any axioms -/
#guard_msgs in #print axioms normK_frame_dependent

/-- info: 'Foam.Lattice.galilean_preserves_time' does not depend on any axioms -/
#guard_msgs in #print axioms galilean_preserves_time

/-- info: 'Foam.Lattice.galilean_velocities_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms galilean_velocities_add

end Foam.Lattice
