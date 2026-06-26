import Foam.Seat.Closure
import Foam.Golden

namespace Foam

theorem two_pm_ones :
    Closes GInt.neg 2
      ∧ (∀ n, fib (n + 1) * fib (n + 1) - fib (n + 2) * fib n ≠ 0) :=
  ⟨alt_closes_two, golden_defect_never_clears⟩

/-- info: 'Foam.two_pm_ones' does not depend on any axioms -/
#guard_msgs in #print axioms two_pm_ones

end Foam
