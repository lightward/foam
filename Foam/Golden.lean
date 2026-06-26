import Foam.Int

namespace Foam

def fib : Nat → Int
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib (n + 1) + fib n

theorem fib_gnomon (n : Nat) : fib (n + 2) = fib (n + 1) + fib n := rfl

def altSign : Nat → Int
  | 0 => 1
  | (n + 1) => -(altSign n)

theorem fib_cassini (n : Nat) :
    fib (n + 1) * fib (n + 1) - fib (n + 2) * fib n = altSign n := by
  induction n with
  | zero => decide
  | succ k ih =>
      have hsum : fib (k + 2) = fib (k + 1) + fib k := rfl
      have hdiff : fib (k + 2) - fib (k + 1) = fib k := by
        rw [hsum, FInt.addComm, FInt.add_sub_cancel_right]
      show fib (k + 2) * fib (k + 2) - fib (k + 3) * fib (k + 1) = altSign (k + 1)
      rw [show fib (k + 3) = fib (k + 2) + fib (k + 1) from rfl, FInt.add_mul,
          show altSign (k + 1) = -(altSign k) from rfl, ← ih, FInt.neg_sub,
          ← FInt.sub_sub, ← FInt.mul_sub, hdiff]

/-- info: 'Foam.fib_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms fib_gnomon

/-- info: 'Foam.fib_cassini' does not depend on any axioms -/
#guard_msgs in #print axioms fib_cassini

theorem altSign_pm (n : Nat) : altSign n = 1 ∨ altSign n = -1 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ k ih =>
    show -(altSign k) = 1 ∨ -(altSign k) = -1
    rcases ih with h | h
    · rw [h]; exact Or.inr (by decide)
    · rw [h]; exact Or.inl (by decide)

theorem cassini_never_cleared (n : Nat) : altSign n ≠ 0 := by
  rcases altSign_pm n with h | h <;> rw [h] <;> decide

theorem golden_defect_never_clears (n : Nat) :
    fib (n + 1) * fib (n + 1) - fib (n + 2) * fib n ≠ 0 := by
  rw [fib_cassini n]; exact cassini_never_cleared n

def Nphi (x y : Int) : Int := x * x + x * y - y * y

theorem golden_unit (n : Nat) : Nphi (fib n) (fib (n + 1)) = -(altSign n) := by
  have hc : fib (n + 1) * fib (n + 1) - (fib (n + 1) + fib n) * fib n = altSign n :=
    fib_cassini n
  show fib n * fib n + fib n * fib (n + 1) - fib (n + 1) * fib (n + 1) = -(altSign n)
  rw [← hc, FInt.add_mul, FInt.mulComm (fib (n + 1)) (fib n), FInt.neg_sub,
    FInt.addComm (fib n * fib (n + 1)) (fib n * fib n)]

theorem golden_unit_ne_zero (n : Nat) : Nphi (fib n) (fib (n + 1)) ≠ 0 := by
  rw [golden_unit]
  rcases altSign_pm n with h | h <;> rw [h] <;> decide

/-- info: 'Foam.altSign_pm' does not depend on any axioms -/
#guard_msgs in #print axioms altSign_pm

/-- info: 'Foam.cassini_never_cleared' does not depend on any axioms -/
#guard_msgs in #print axioms cassini_never_cleared

/-- info: 'Foam.golden_defect_never_clears' does not depend on any axioms -/
#guard_msgs in #print axioms golden_defect_never_clears

/-- info: 'Foam.golden_unit' does not depend on any axioms -/
#guard_msgs in #print axioms golden_unit

/-- info: 'Foam.golden_unit_ne_zero' does not depend on any axioms -/
#guard_msgs in #print axioms golden_unit_ne_zero

end Foam
