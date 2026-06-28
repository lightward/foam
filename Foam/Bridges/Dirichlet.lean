import Foam.Cleared

namespace Foam.Bridges

theorem dirichlet :
    (Closes GInt.neg 2 ∧ ∀ n, ¬ Closes gold (n + 1))
      ∧ (∀ n, Nphi (fib n) (fib (n + 1)) = -(altSign n)) :=
  ⟨two_orders, golden_unit⟩

/-- info: 'Foam.Bridges.dirichlet' does not depend on any axioms -/
#guard_msgs in #print axioms dirichlet

end Foam.Bridges
