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

/-- info: 'Foam.Lattice.align_add_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms align_add_right

/-- info: 'Foam.Lattice.born_superpose' depends on axioms: [propext] -/
#guard_msgs in #print axioms born_superpose

end Foam.Lattice

