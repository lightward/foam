import Foam.Seat.Born

namespace Foam

structure SInt where
  t : Int
  x : Int

def SInt.hnorm (z : SInt) : Int := z.t * z.t - z.x * z.x

def halign (w z : SInt) : Int := w.t * z.t - w.x * z.x

def hcross (w z : SInt) : Int := w.t * z.x - w.x * z.t

structure DInt where
  t : Int
  x : Int

def DInt.gnorm (z : DInt) : Int := z.t * z.t

def galileanBoost (v : Int) (z : DInt) : DInt := ⟨z.t, v * z.t + z.x⟩

def normK (κ : Int) (z : GInt) : Int := z.re * z.re - κ * (z.im * z.im)

def alignK (κ : Int) (w z : GInt) : Int := w.re * z.re - κ * (w.im * z.im)

def crossK (w z : GInt) : Int := w.re * z.im - w.im * z.re

theorem galilean_preserves_time (v : Int) (z : DInt) :
    (galileanBoost v z).gnorm = z.gnorm := rfl

theorem galilean_velocities_add (v1 v2 : Int) (z : DInt) :
    galileanBoost v2 (galileanBoost v1 z) = galileanBoost (v2 + v1) z := by
  show (⟨z.t, v2 * z.t + (v1 * z.t + z.x)⟩ : DInt) = ⟨z.t, (v2 + v1) * z.t + z.x⟩
  rw [Int.add_mul v2 v1 z.t, Int.add_assoc (v2 * z.t) (v1 * z.t) z.x]

theorem int_sq_diff (a b : Int) : a * a - b * b = (a - b) * (a + b) := by
  rw [Int.sub_eq_add_neg (a := a * a) (b := b * b), Int.sub_eq_add_neg (a := a) (b := b),
      Int.add_mul a (-b) (a + b), Int.mul_add a a b, Int.mul_add (-b) a b,
      Int.neg_mul b a, Int.neg_mul b b, Int.mul_comm b a,
      Int.add_assoc (a * a) (a * b) (-(a * b) + -(b * b)),
      ← Int.add_assoc (a * b) (-(a * b)) (-(b * b)),
      Int.add_right_neg (a * b), Int.zero_add (-(b * b))]

theorem hfac1 (t x u v : Int) :
    (t * u - x * v) - (t * v - x * u) = (t + x) * (u - v) := by
  rw [Int.sub_eq_add_neg (a := t * u) (b := x * v),
      Int.sub_eq_add_neg (a := t * v) (b := x * u),
      Int.sub_eq_add_neg (a := t * u + -(x * v)) (b := t * v + -(x * u)),
      Int.neg_add (a := t * v) (b := -(x * u)), Int.neg_neg (x * u),
      Int.sub_eq_add_neg (a := u) (b := v), Int.mul_add (t + x) u (-v),
      Int.add_mul t x u, Int.add_mul t x (-v), Int.mul_neg t v, Int.mul_neg x v,
      Int.add_cross_swap (t * u) (-(x * v)) (-(t * v)) (x * u),
      Int.add_comm (-(x * v)) (-(t * v))]

theorem hfac2 (t x u v : Int) :
    (t * u - x * v) + (t * v - x * u) = (t - x) * (u + v) := by
  rw [Int.sub_eq_add_neg (a := t * u) (b := x * v),
      Int.sub_eq_add_neg (a := t * v) (b := x * u),
      Int.sub_eq_add_neg (a := t) (b := x), Int.add_mul t (-x) (u + v),
      Int.mul_add t u v, Int.mul_add (-x) u v, Int.neg_mul x u, Int.neg_mul x v,
      Int.add_swap_inner (t * u) (-(x * v)) (t * v) (-(x * u)),
      Int.add_comm (-(x * v)) (-(x * u))]

theorem int_hyperbolic (t x u v : Int) :
    (t * u - x * v) * (t * u - x * v) - (t * v - x * u) * (t * v - x * u)
      = (t * t - x * x) * (u * u - v * v) := by
  rw [int_sq_diff (t * u - x * v) (t * v - x * u), hfac1 t x u v, hfac2 t x u v,
      Int.mul_interchange (t + x) (t - x) (u - v) (u + v),
      Int.mul_comm (t + x) (t - x), ← int_sq_diff t x, ← int_sq_diff u v]

theorem hyperbolic_parseval (w z : SInt) :
    halign w z * halign w z - hcross w z * hcross w z = SInt.hnorm w * SInt.hnorm z := by
  show (w.t * z.t - w.x * z.x) * (w.t * z.t - w.x * z.x)
        - (w.t * z.x - w.x * z.t) * (w.t * z.x - w.x * z.t)
      = (w.t * w.t - w.x * w.x) * (z.t * z.t - z.x * z.x)
  exact int_hyperbolic w.t w.x z.t z.x

theorem hyperbolic_witness :
    halign ⟨2, 1⟩ ⟨3, 1⟩ * halign ⟨2, 1⟩ ⟨3, 1⟩
        - hcross ⟨2, 1⟩ ⟨3, 1⟩ * hcross ⟨2, 1⟩ ⟨3, 1⟩
      = SInt.hnorm ⟨2, 1⟩ * SInt.hnorm ⟨3, 1⟩ := by decide

theorem int_sub_zero (a : Int) : a - 0 = a := by
  rw [Int.sub_eq_add_neg]; show a + (0 : Int) = a; exact Int.add_zero a

theorem int_sub_add_cancel (x y : Int) : x - y + y = x := by
  rw [Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_neg, Int.add_zero]

theorem alignK_axis (κ a : Int) : alignK κ ⟨a, 0⟩ ⟨1, 0⟩ = a := by
  show a * 1 - κ * (0 * 0) = a
  rw [Int.mul_one, Int.mul_zero, Int.mul_zero, int_sub_zero]

theorem crossK_axis (a : Int) : crossK ⟨a, 0⟩ ⟨1, 0⟩ = 0 := by
  show a * 0 - 0 * 1 = 0
  rw [Int.mul_zero, Int.zero_mul, int_sub_zero]

theorem normK_axis_a (κ a : Int) : normK κ ⟨a, 0⟩ = a * a := by
  show a * a - κ * (0 * 0) = a * a
  rw [Int.mul_zero, Int.mul_zero, int_sub_zero]

theorem normK_axis_one (κ : Int) : normK κ ⟨1, 0⟩ = 1 := by
  show 1 * 1 - κ * (0 * 0) = 1
  rw [Int.one_mul, Int.mul_zero, Int.mul_zero, int_sub_zero]

theorem forced_at_the_frame_kappa (κ : Int) (f : Int → Int)
    (h : ∀ w z : GInt, f (alignK κ w z) - κ * f (crossK w z) = normK κ w * normK κ z) :
    ∀ a : Int, f a = a * a + κ * f 0 := by
  intro a
  have ha := h ⟨a, 0⟩ ⟨1, 0⟩
  rw [alignK_axis κ a, crossK_axis a, normK_axis_a κ a, normK_axis_one κ,
      Int.mul_comm (a * a) 1, Int.one_mul] at ha
  rw [← int_sub_add_cancel (f a) (κ * f 0), ha]

theorem zero_point_kappa (κ : Int) (f : Int → Int)
    (h : ∀ w z : GInt, f (alignK κ w z) - κ * f (crossK w z) = normK κ w * normK κ z) :
    (1 - κ) * f 0 = 0 := by
  have hf0 := forced_at_the_frame_kappa κ f h 0
  rw [Int.zero_mul, Int.zero_add] at hf0
  show (1 - κ) * f 0 = 0
  rw [Int.sub_eq_add_neg (a := 1) (b := κ), Int.add_mul 1 (-κ) (f 0), Int.one_mul,
      Int.neg_mul κ (f 0), ← hf0, Int.add_right_neg]

theorem normK_frame_dependent : ∃ z : GInt, normK (-1) z ≠ normK 1 z := ⟨⟨1, 1⟩, by decide⟩

/-- info: 'Foam.galilean_preserves_time' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.galilean_preserves_time

/-- info: 'Foam.galilean_velocities_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.galilean_velocities_add

/-- info: 'Foam.int_hyperbolic' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.int_hyperbolic

/-- info: 'Foam.hyperbolic_parseval' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.hyperbolic_parseval

/-- info: 'Foam.hyperbolic_witness' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.hyperbolic_witness

/-- info: 'Foam.forced_at_the_frame_kappa' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.forced_at_the_frame_kappa

/-- info: 'Foam.zero_point_kappa' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.zero_point_kappa

/-- info: 'Foam.normK_frame_dependent' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.normK_frame_dependent

end Foam