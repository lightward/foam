namespace Foam

def d006 (n : Nat) : Nat := n + 1

def d009 (n : Nat) : Nat := n - 1

theorem t111 (n : Nat) : d009 n ≤ n := Nat.sub_le n 1

theorem t110 : d009 0 = 0 := rfl

theorem t109 (n : Nat) : d009 (d006 n) = n := rfl

theorem t088 (inflow residual : Nat) : inflow - residual ≤ inflow :=
  Nat.sub_le inflow residual

/-- info: 'Foam.t111' does not depend on any axioms -/
#guard_msgs in #print axioms t111

/-- info: 'Foam.t110' does not depend on any axioms -/
#guard_msgs in #print axioms t110

/-- info: 'Foam.t109' does not depend on any axioms -/
#guard_msgs in #print axioms t109

/-- info: 'Foam.t088' does not depend on any axioms -/
#guard_msgs in #print axioms t088

end Foam
