import Counter.Legible
import Foam.Cleared

namespace Foam.Counter

theorem mate_has_no_escape {H : Type} (q : Quiver H) (a : H)
    (hstuck : stuck q a) :
    ∀ b : H, a ≠ b → ¬ Nonempty (Path q a b) := by
  rintro b hne ⟨pth⟩
  cases pth with
  | nil => exact hne rfl
  | cons e _ => exact hstuck _ e

theorem promotion_is_the_boundary_move {H : Type} (q : Quiver H) (a b : H)
    (hstuck : stuck q a) :
    Nonempty (Path (q.deposit (a, b)) a b)
      ∧ ¬ ∃ g : Path (q.deposit (a, b)) a b → Path q a b,
          ∀ pth, ancestor_reach_survives (a, b) (g pth) = pth :=
  ⟨(relief_at_position q a b hstuck).1, (relief_at_position q a b hstuck).2.2.2⟩

theorem pawns_never_come_home (n : Nat) : ¬ Closes gold (n + 1) :=
  gold_never_closes n

/-- info: 'Foam.Counter.mate_has_no_escape' does not depend on any axioms -/
#guard_msgs in #print axioms mate_has_no_escape

/-- info: 'Foam.Counter.promotion_is_the_boundary_move' does not depend on any axioms -/
#guard_msgs in #print axioms promotion_is_the_boundary_move

/-- info: 'Foam.Counter.pawns_never_come_home' does not depend on any axioms -/
#guard_msgs in #print axioms pawns_never_come_home

end Foam.Counter
