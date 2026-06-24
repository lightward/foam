import Foam.Int

namespace Foam

def d014 : Nat → Int
  | 0 => 0
  | 1 => 1
  | (n + 2) => d014 (n + 1) + d014 n

theorem t113 (n : Nat) : d014 (n + 2) = d014 (n + 1) + d014 n := rfl

def d005 : Nat → Int
  | 0 => 1
  | (n + 1) => -(d005 n)

theorem t112 (n : Nat) :
    d014 (n + 1) * d014 (n + 1) - d014 (n + 2) * d014 n = d005 n := by
  induction n with
  | zero => decide
  | succ k ih =>
      have hsum : d014 (k + 2) = d014 (k + 1) + d014 k := rfl
      have hdiff : d014 (k + 2) - d014 (k + 1) = d014 k := by
        rw [hsum, Foam.t004, Foam.t013]
      show d014 (k + 2) * d014 (k + 2) - d014 (k + 3) * d014 (k + 1) = d005 (k + 1)
      rw [show d014 (k + 3) = d014 (k + 2) + d014 (k + 1) from rfl, Foam.t007,
          show d005 (k + 1) = -(d005 k) from rfl, ← ih, Foam.t030,
          ← Foam.t051, ← Foam.t021, hdiff]

/-- info: 'Foam.t113' does not depend on any axioms -/
#guard_msgs in #print axioms t113

/-- info: 'Foam.t112' does not depend on any axioms -/
#guard_msgs in #print axioms t112

end Foam
