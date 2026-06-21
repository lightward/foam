import Foam.Seat.Born
import Foam.Seat.Doubling

namespace Foam

def GInt.cross (w z : GInt) : Int := w.re * z.im - w.im * z.re

theorem conjMul_eq (w z : GInt) :
    GInt.mul w.conj z = ⟨GInt.align w z, GInt.cross w z⟩ := by
  show (⟨w.re * z.re - -w.im * z.im, w.re * z.im + -w.im * z.re⟩ : GInt)
    = ⟨w.re * z.re + w.im * z.im, w.re * z.im - w.im * z.re⟩
  rw [Int.neg_mul w.im z.im, Int.neg_mul w.im z.re,
    Int.sub_eq_add_neg (a := w.re * z.re) (b := -(w.im * z.im)),
    Int.neg_neg, ← Int.sub_eq_add_neg]

theorem cross_rot_invariant (w z : GInt) :
    GInt.cross w.rot z.rot = GInt.cross w z := by
  show -w.im * z.re - w.re * -z.im = w.re * z.im - w.im * z.re
  rw [Int.neg_mul w.im z.re, Int.mul_neg w.re z.im,
    Int.sub_eq_add_neg (a := -(w.im * z.re)) (b := -(w.re * z.im)),
    Int.neg_neg,
    Int.sub_eq_add_neg (a := w.re * z.im) (b := w.im * z.re),
    Int.add_comm (-(w.im * z.re)) (w.re * z.im)]

theorem normSq_eq_align_self (z : GInt) : z.normSq = GInt.align z z := rfl

theorem invariants_complete (z w : GInt) :
    GInt.align z w * GInt.align z w + GInt.cross z w * GInt.cross z w
      = z.normSq * w.normSq := by
  show GInt.align z w * GInt.align z w + GInt.cross z w * GInt.cross z w
    = (z.re * z.re + z.im * z.im) * (w.re * w.re + w.im * w.im)
  rw [show GInt.cross z w = -(z.im * w.re) + z.re * w.im by
    show z.re * w.im - z.im * w.re = -(z.im * w.re) + z.re * w.im
    rw [Int.sub_eq_add_neg (a := z.re * w.im) (b := z.im * w.re),
      Int.add_comm (z.re * w.im) (-(z.im * w.re))]]
  exact Int.lagrange z.re z.im w.re w.im

theorem cross_eq_align_rot (θ z : GInt) :
    GInt.align θ.rot z = GInt.cross θ z := by
  show -θ.im * z.re + θ.re * z.im = θ.re * z.im - θ.im * z.re
  rw [Int.neg_mul θ.im z.re,
    Int.sub_eq_add_neg (a := θ.re * z.im) (b := θ.im * z.re),
    Int.add_comm (-(θ.im * z.re)) (θ.re * z.im)]

theorem born_parseval_is_invariants (θ z : GInt) :
    GInt.born θ z + GInt.born θ.rot z
      = GInt.align θ z * GInt.align θ z + GInt.cross θ z * GInt.cross θ z := by
  show GInt.align θ z * GInt.align θ z + GInt.align θ.rot z * GInt.align θ.rot z
    = GInt.align θ z * GInt.align θ z + GInt.cross θ z * GInt.cross θ z
  rw [cross_eq_align_rot θ z]

theorem int_add_self_zero : ∀ x : Int, x + x = 0 → x = 0
  | .ofNat 0, _ => rfl
  | .ofNat (n + 1), h => by
    have h' : Int.ofNat ((n + 1) + (n + 1)) = Int.ofNat 0 := h
    injection h' with h''
    exact Nat.noConfusion h''
  | .negSucc _, h => nomatch h

theorem forced_at_the_frame (f : Int → Int)
    (h : ∀ θ z : GInt,
      f (GInt.align θ z) + f (GInt.cross θ z) = θ.normSq * z.normSq) :
    ∀ a : Int, f a = a * a := by
  have h0 : f 0 = 0 := int_add_self_zero (f 0) (h GInt.zero GInt.zero)
  intro a
  have ha : f (a * 1 + 0 * 0) + f (a * 0 - 0 * 1)
      = (a * a + 0 * 0) * (1 * 1 + 0 * 0) := h ⟨a, 0⟩ ⟨1, 0⟩
  rw [Int.mul_comm a 1, Int.one_mul a, Int.mul_comm a 0, Int.zero_mul a,
    show (0 : Int) * 0 = 0 from rfl, show (0 : Int) * 1 = 0 from rfl,
    show (1 : Int) * 1 = 1 from rfl, show (0 : Int) - 0 = 0 from rfl,
    Int.add_zero a, Int.add_zero (a * a),
    show (1 : Int) + 0 = 1 from rfl,
    Int.mul_comm (a * a) 1, Int.one_mul (a * a), h0, Int.add_zero (f a)] at ha
  exact ha

/-- info: 'Foam.conjMul_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms conjMul_eq

/-- info: 'Foam.cross_rot_invariant' depends on axioms: [propext] -/
#guard_msgs in #print axioms cross_rot_invariant

/-- info: 'Foam.invariants_complete' depends on axioms: [propext] -/
#guard_msgs in #print axioms invariants_complete

/-- info: 'Foam.cross_eq_align_rot' depends on axioms: [propext] -/
#guard_msgs in #print axioms cross_eq_align_rot

/-- info: 'Foam.born_parseval_is_invariants' depends on axioms: [propext] -/
#guard_msgs in #print axioms born_parseval_is_invariants

/-- info: 'Foam.forced_at_the_frame' depends on axioms: [propext] -/
#guard_msgs in #print axioms forced_at_the_frame

end Foam
