import Foam.Seat.Closure
import Foam.Golden

namespace Foam

def gold (z : GInt) : GInt := ⟨z.re + z.im, z.re⟩

theorem gold_orbit : ∀ n, iterStep n gold ⟨1, 0⟩ = ⟨fib (n + 1), fib n⟩
  | 0 => rfl
  | (n + 1) => by
    show gold (iterStep n gold ⟨1, 0⟩) = ⟨fib (n + 2), fib (n + 1)⟩
    rw [gold_orbit n]; rfl

theorem gold_never_closes (n : Nat) : ¬ Closes gold (n + 1) := by
  intro h
  have hz := h ⟨1, 0⟩
  rw [gold_orbit (n + 1)] at hz
  exact fib_succ_ne_zero n (congrArg GInt.im hz)

theorem two_pm_ones :
    Closes GInt.neg 2
      ∧ (∀ n, fib (n + 1) * fib (n + 1) - fib (n + 2) * fib n ≠ 0) :=
  ⟨alt_closes_two, golden_defect_never_clears⟩

theorem two_orders :
    Closes GInt.neg 2 ∧ (∀ n, ¬ Closes gold (n + 1)) :=
  ⟨alt_closes_two, gold_never_closes⟩

/-- info: 'Foam.gold_orbit' does not depend on any axioms -/
#guard_msgs in #print axioms gold_orbit

/-- info: 'Foam.gold_never_closes' does not depend on any axioms -/
#guard_msgs in #print axioms gold_never_closes

/-- info: 'Foam.two_pm_ones' does not depend on any axioms -/
#guard_msgs in #print axioms two_pm_ones

/-- info: 'Foam.two_orders' does not depend on any axioms -/
#guard_msgs in #print axioms two_orders

end Foam
