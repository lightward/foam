import Foam.Seat.Dial

namespace Foam

theorem Int.add_swap_inner (p q r s : Int) : (p + q) + (r + s) = (p + r) + (q + s) := by
  rw [Int.add_assoc p q (r + s), ← Int.add_assoc q r s, Int.add_comm q r,
      Int.add_assoc r q s, ← Int.add_assoc p r (q + s)]

theorem Int.add_cross_swap (p q r s : Int) : (p + q) + (r + s) = (p + s) + (q + r) := by
  rw [Int.add_assoc p q (r + s), Int.add_comm r s, ← Int.add_assoc q s r,
      Int.add_comm q s, Int.add_assoc s q r, ← Int.add_assoc p s (q + r)]

theorem Int.two_mul' (x : Int) : 2 * x = x + x := by
  rw [show (2 : Int) = 1 + 1 from rfl, Int.add_mul, Int.one_mul]

theorem Int.mul_interchange (a b c d : Int) : (a * c) * (b * d) = (a * b) * (c * d) := by
  rw [Int.mul_assoc a c (b * d), ← Int.mul_assoc c b d, Int.mul_comm c b,
      Int.mul_assoc b c d, ← Int.mul_assoc a b (c * d)]

theorem Int.sq_interchange (a c : Int) : (a * c) * (a * c) = (a * a) * (c * c) :=
  Int.mul_interchange a a c c

theorem Int.neg_mul_neg' (a b : Int) : (-a) * (-b) = a * b := by
  rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]

theorem Int.parseval_collect (W K Z M N : Int) :
    ((W + K) + (K + Z)) + ((M + (-K)) + ((-K) + N)) = (W + M) + (N + Z) := by
  rw [Int.add_cross_swap W K K Z, Int.add_cross_swap M (-K) (-K) N,
      Int.add_swap_inner (W + Z) (K + K) (M + N) ((-K) + (-K)),
      Int.add_cross_swap K K (-K) (-K), Int.add_right_neg K, Int.add_zero, Int.add_zero,
      Int.add_swap_inner W Z M N, Int.add_comm Z N]

theorem Int.lagrange (a b c d : Int) :
    (a * c + b * d) * (a * c + b * d)
      + (-(b * c) + a * d) * (-(b * c) + a * d)
    = (a * a + b * b) * (c * c + d * d) := by
  rw [Int.mul_add (a * c + b * d) (a * c) (b * d),
      Int.add_mul (a * c) (b * d) (a * c), Int.add_mul (a * c) (b * d) (b * d)]
  rw [Int.mul_add (-(b * c) + a * d) (-(b * c)) (a * d),
      Int.add_mul (-(b * c)) (a * d) (-(b * c)), Int.add_mul (-(b * c)) (a * d) (a * d)]
  rw [Int.mul_add (a * a + b * b) (c * c) (d * d),
      Int.add_mul (a * a) (b * b) (c * c), Int.add_mul (a * a) (b * b) (d * d)]
  rw [Int.sq_interchange a c, Int.sq_interchange b d]
  rw [Int.neg_mul_neg' (b * c) (b * c), Int.sq_interchange b c, Int.sq_interchange a d]
  rw [Int.mul_neg (a * d) (b * c), Int.neg_mul (b * c) (a * d)]
  rw [Int.mul_comm (b * d) (a * c), Int.mul_interchange a b c d]
  rw [Int.mul_interchange a b d c, Int.mul_comm d c]
  rw [Int.mul_comm (b * c) (a * d), Int.mul_interchange a b d c, Int.mul_comm d c]
  exact Int.parseval_collect (a * a * (c * c)) (a * b * (c * d)) (b * b * (d * d))
        (b * b * (c * c)) (a * a * (d * d))

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

theorem GInt.align_add (θ a b : GInt) :
    GInt.align θ (GInt.add a b) = GInt.align θ a + GInt.align θ b := by
  show θ.re * (a.re + b.re) + θ.im * (a.im + b.im)
     = (θ.re * a.re + θ.im * a.im) + (θ.re * b.re + θ.im * b.im)
  rw [Int.mul_add, Int.mul_add]
  exact Int.add_swap_inner (θ.re * a.re) (θ.re * b.re) (θ.im * a.im) (θ.im * b.im)

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

theorem GInt.born_superpose (θ a b : GInt) :
    GInt.born θ (GInt.add a b)
      = GInt.born θ a + GInt.born θ b + 2 * (GInt.align θ a * GInt.align θ b) := by
  show GInt.align θ (GInt.add a b) * GInt.align θ (GInt.add a b)
     = GInt.align θ a * GInt.align θ a + GInt.align θ b * GInt.align θ b
       + 2 * (GInt.align θ a * GInt.align θ b)
  rw [GInt.align_add θ a b, Int.two_mul' (GInt.align θ a * GInt.align θ b),
      Int.add_mul (GInt.align θ a) (GInt.align θ b) (GInt.align θ a + GInt.align θ b),
      Int.mul_add (GInt.align θ a) (GInt.align θ a) (GInt.align θ b),
      Int.mul_add (GInt.align θ b) (GInt.align θ a) (GInt.align θ b),
      Int.mul_comm (GInt.align θ b) (GInt.align θ a)]
  exact Int.add_cross_swap (GInt.align θ a * GInt.align θ a) (GInt.align θ a * GInt.align θ b)
        (GInt.align θ a * GInt.align θ b) (GInt.align θ b * GInt.align θ b)

theorem GInt.born_parseval (θ z : GInt) :
    GInt.born θ z + GInt.born (GInt.rot θ) z = GInt.normSq θ * GInt.normSq z := by
  show (θ.re * z.re + θ.im * z.im) * (θ.re * z.re + θ.im * z.im)
     + ((-θ.im) * z.re + θ.re * z.im) * ((-θ.im) * z.re + θ.re * z.im)
     = (θ.re * θ.re + θ.im * θ.im) * (z.re * z.re + z.im * z.im)
  rw [Int.neg_mul θ.im z.re]
  exact Int.lagrange θ.re θ.im z.re z.im

/-- info: 'Foam.GInt.born_nonneg' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.born_nonneg

/-- info: 'Foam.GInt.rot_sq' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.rot_sq

/-- info: 'Foam.GInt.decoherence' depends on axioms: [propext] -/
#guard_msgs in #print axioms GInt.decoherence

/-- info: 'Foam.GInt.born_superpose' depends on axioms: [propext] -/
#guard_msgs in #print axioms GInt.born_superpose

/-- info: 'Foam.GInt.born_parseval' depends on axioms: [propext] -/
#guard_msgs in #print axioms GInt.born_parseval

end Foam
