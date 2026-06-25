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

end Foam
