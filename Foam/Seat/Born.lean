import Foam.Seat.Dial

namespace Foam

theorem Int.add_swap_inner (p q r s : Int) : (p + q) + (r + s) = (p + r) + (q + s) := by
  rw [Int.add_assoc p q (r + s), ← Int.add_assoc q r s, Int.add_comm q r,
      Int.add_assoc r q s, ← Int.add_assoc p r (q + s)]

def GInt.neg (z : GInt) : GInt := ⟨-z.re, -z.im⟩
def GInt.rot (z : GInt) : GInt := ⟨-z.im, z.re⟩
def GInt.align (w z : GInt) : Int := w.re * z.re + w.im * z.im
def GInt.born (w z : GInt) : Int := GInt.align w z * GInt.align w z

theorem GInt.born_nonneg (w z : GInt) : ∃ k : Nat, GInt.born w z = Int.ofNat k :=
  GInt.sq_image (GInt.align w z)

theorem GInt.rot_sq (z : GInt) : GInt.rot (GInt.rot z) = GInt.neg z := rfl

theorem GInt.align_neg (w z : GInt) : GInt.align w (GInt.neg z) = -(GInt.align w z) := by
  show w.re * (-z.re) + w.im * (-z.im) = -(w.re * z.re + w.im * z.im)
  rw [Int.mul_neg, Int.mul_neg, ← Int.neg_add]

theorem GInt.decoherence (θ z : GInt) :
    GInt.align θ z + GInt.align θ (GInt.rot z)
      + GInt.align θ (GInt.rot (GInt.rot z))
      + GInt.align θ (GInt.rot (GInt.rot (GInt.rot z))) = 0 := by
  have e3 : GInt.align θ (GInt.rot (GInt.rot z)) = -(GInt.align θ z) := by
    have h : GInt.rot (GInt.rot z) = GInt.neg z := rfl
    rw [h, GInt.align_neg]
  have e4 : GInt.align θ (GInt.rot (GInt.rot (GInt.rot z))) = -(GInt.align θ (GInt.rot z)) := by
    have h : GInt.rot (GInt.rot (GInt.rot z)) = GInt.neg (GInt.rot z) := rfl
    rw [h, GInt.align_neg]
  rw [e3, e4,
      Int.add_assoc (GInt.align θ z + GInt.align θ (GInt.rot z))
        (-(GInt.align θ z)) (-(GInt.align θ (GInt.rot z))),
      Int.add_swap_inner (GInt.align θ z) (GInt.align θ (GInt.rot z))
        (-(GInt.align θ z)) (-(GInt.align θ (GInt.rot z))),
      Int.add_right_neg, Int.add_right_neg, Int.add_zero]

/-- info: 'Foam.GInt.born_nonneg' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.born_nonneg

/-- info: 'Foam.GInt.rot_sq' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.rot_sq

/-- info: 'Foam.GInt.align_neg' depends on axioms: [propext] -/
#guard_msgs in #print axioms GInt.align_neg

/-- info: 'Foam.GInt.decoherence' depends on axioms: [propext] -/
#guard_msgs in #print axioms GInt.decoherence

end Foam
