import Foam.Lattice.Born

namespace Foam.Lattice

theorem add_swap_inner (p q r s : Int) : (p + q) + (r + s) = (p + r) + (q + s) := by
  rw [Int.add_assoc p q (r + s), ← Int.add_assoc q r s, Int.add_comm q r,
      Int.add_assoc r q s, ← Int.add_assoc p r (q + s)]

theorem add_cross_swap (p q r s : Int) : (p + q) + (r + s) = (p + s) + (q + r) := by
  rw [Int.add_assoc p q (r + s), Int.add_comm r s, ← Int.add_assoc q s r,
      Int.add_comm q s, Int.add_assoc s q r, ← Int.add_assoc p s (q + r)]

theorem two_mul' (x : Int) : (2 : Int) * x = x + x := by
  rw [show (2 : Int) = 1 + 1 from rfl, Int.add_mul, Int.one_mul]

theorem align_add_right (θ a b : GInt) :
    align θ (a.add b) = align θ a + align θ b := by
  show θ.re * (a.re + b.re) + θ.im * (a.im + b.im)
     = (θ.re * a.re + θ.im * a.im) + (θ.re * b.re + θ.im * b.im)
  rw [Int.mul_add, Int.mul_add]
  exact add_swap_inner (θ.re * a.re) (θ.re * b.re) (θ.im * a.im) (θ.im * b.im)

theorem born_superpose (θ a b : GInt) :
    born θ (a.add b) = born θ a + born θ b + (2 : Int) * (align θ a * align θ b) := by
  show align θ (a.add b) * align θ (a.add b)
     = align θ a * align θ a + align θ b * align θ b + (2 : Int) * (align θ a * align θ b)
  rw [align_add_right θ a b, two_mul' (align θ a * align θ b),
      Int.add_mul (align θ a) (align θ b) (align θ a + align θ b),
      Int.mul_add (align θ a) (align θ a) (align θ b),
      Int.mul_add (align θ b) (align θ a) (align θ b),
      Int.mul_comm (align θ b) (align θ a)]
  exact add_cross_swap (align θ a * align θ a) (align θ a * align θ b)
        (align θ a * align θ b) (align θ b * align θ b)

def GInt.normSq (z : GInt) : Int := z.re * z.re + z.im * z.im

theorem align_negate (θ z : GInt) : align θ (GInt.negate z) = -(align θ z) := by
  show θ.re * (-z.re) + θ.im * (-z.im) = -(θ.re * z.re + θ.im * z.im)
  rw [Int.mul_neg, Int.mul_neg, ← Int.neg_add]

theorem decoherence_cancels_cross (θ b : GInt) :
    align θ b + align θ b.rot + align θ b.rot.rot + align θ b.rot.rot.rot = 0 := by
  show align θ b + align θ b.rot + align θ (GInt.negate b) + align θ (GInt.negate b.rot) = 0
  rw [align_negate θ b, align_negate θ b.rot,
      Int.add_assoc (align θ b + align θ b.rot) (-(align θ b)) (-(align θ b.rot)),
      add_swap_inner (align θ b) (align θ b.rot) (-(align θ b)) (-(align θ b.rot)),
      Int.add_right_neg, Int.add_right_neg, Int.add_zero]

theorem mul_interchange (a b c d : Int) : (a * c) * (b * d) = (a * b) * (c * d) := by
  rw [Int.mul_assoc a c (b * d), ← Int.mul_assoc c b d, Int.mul_comm c b,
      Int.mul_assoc b c d, ← Int.mul_assoc a b (c * d)]

theorem sq_interchange (a c : Int) : (a * c) * (a * c) = (a * a) * (c * c) :=
  mul_interchange a a c c

theorem neg_mul_neg' (a b : Int) : (-a) * (-b) = a * b := by
  rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]

theorem parseval_collect (W K Z M N : Int) :
    ((W + K) + (K + Z)) + ((M + (-K)) + ((-K) + N)) = (W + M) + (N + Z) := by
  rw [add_cross_swap W K K Z, add_cross_swap M (-K) (-K) N,
      add_swap_inner (W + Z) (K + K) (M + N) ((-K) + (-K)),
      add_cross_swap K K (-K) (-K), Int.add_right_neg K, Int.add_zero, Int.add_zero,
      add_swap_inner W Z M N, Int.add_comm Z N]

theorem int_lagrange (a b c d : Int) :
    (a * c + b * d) * (a * c + b * d)
      + (-(b * c) + a * d) * (-(b * c) + a * d)
    = (a * a + b * b) * (c * c + d * d) := by
  rw [Int.mul_add (a * c + b * d) (a * c) (b * d),
      Int.add_mul (a * c) (b * d) (a * c), Int.add_mul (a * c) (b * d) (b * d)]
  rw [Int.mul_add (-(b * c) + a * d) (-(b * c)) (a * d),
      Int.add_mul (-(b * c)) (a * d) (-(b * c)), Int.add_mul (-(b * c)) (a * d) (a * d)]
  rw [Int.mul_add (a * a + b * b) (c * c) (d * d),
      Int.add_mul (a * a) (b * b) (c * c), Int.add_mul (a * a) (b * b) (d * d)]
  rw [sq_interchange a c, sq_interchange b d]
  rw [neg_mul_neg' (b * c) (b * c), sq_interchange b c, sq_interchange a d]
  rw [Int.mul_neg (a * d) (b * c), Int.neg_mul (b * c) (a * d)]
  rw [Int.mul_comm (b * d) (a * c), mul_interchange a b c d]
  rw [mul_interchange a b d c, Int.mul_comm d c]
  rw [Int.mul_comm (b * c) (a * d), mul_interchange a b d c, Int.mul_comm d c]
  exact parseval_collect (a * a * (c * c)) (a * b * (c * d)) (b * b * (d * d))
        (b * b * (c * c)) (a * a * (d * d))

theorem born_parseval (θ z : GInt) :
    born θ z + born θ.rot z = θ.normSq * z.normSq := by
  show (θ.re * z.re + θ.im * z.im) * (θ.re * z.re + θ.im * z.im)
     + ((-θ.im) * z.re + θ.re * z.im) * ((-θ.im) * z.re + θ.re * z.im)
     = (θ.re * θ.re + θ.im * θ.im) * (z.re * z.re + z.im * z.im)
  rw [Int.neg_mul θ.im z.re]
  exact int_lagrange θ.re θ.im z.re z.im

/-- info: 'Foam.Lattice.align_add_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms align_add_right

/-- info: 'Foam.Lattice.int_lagrange' depends on axioms: [propext] -/
#guard_msgs in #print axioms int_lagrange

/-- info: 'Foam.Lattice.born_parseval' depends on axioms: [propext] -/
#guard_msgs in #print axioms born_parseval

/-- info: 'Foam.Lattice.decoherence_cancels_cross' depends on axioms: [propext] -/
#guard_msgs in #print axioms decoherence_cancels_cross

/-- info: 'Foam.Lattice.born_superpose' depends on axioms: [propext] -/
#guard_msgs in #print axioms born_superpose

end Foam.Lattice

