namespace Foam

def fib : Nat → Int
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib (n + 1) + fib n

theorem fib_gnomon (n : Nat) : fib (n + 2) = fib (n + 1) + fib n := rfl

theorem fib_cassini (n : Nat) :
    fib (n + 1) * fib (n + 1) - fib (n + 2) * fib n = (-1) ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
      have hsum : fib (k + 2) = fib (k + 1) + fib k := rfl
      have hdiff : fib (k + 2) - fib (k + 1) = fib k := by
        rw [hsum, Int.add_comm, Int.add_sub_cancel]
      show fib (k + 2) * fib (k + 2) - fib (k + 3) * fib (k + 1) = (-1) ^ (k + 1)
      rw [show fib (k + 3) = fib (k + 2) + fib (k + 1) from rfl, Int.add_mul,
          Int.pow_succ, Int.mul_neg_one, ← ih, Int.neg_sub, ← Int.sub_sub,
          ← Int.mul_sub, hdiff]

/-- info: 'Foam.fib_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms fib_gnomon

/-- info: 'Foam.fib_cassini' depends on axioms: [propext] -/
#guard_msgs in #print axioms fib_cassini

end Foam
