import Foam.Seat.Descend

namespace Foam.Counter

variable {H : Type}

theorem report_within_model {q : Quiver H} {x y : H}
    (p : Path q x y) : ∀ e ∈ p.edges, e ∈ q :=
  reach_within_quiver p

theorem illegible_report_is_discovery (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    (∀ (x y : H) (p : Path q x y), (a, b) ∉ p.edges)
      ∧ Nonempty (Path (q.deposit (a, b)) a b) := by
  refine ⟨?_, ⟨heir_reaches q a b⟩⟩
  intro x y p hmem
  exact hfresh (reach_within_quiver p (a, b) hmem)

theorem legibility_costs_one_edge (q : Quiver H) (e : H × H) :
    (q.deposit e).length = q.length + 1 :=
  deposit_monotone q e

/-- info: 'Foam.Counter.report_within_model' does not depend on any axioms -/
#guard_msgs in #print axioms report_within_model

/-- info: 'Foam.Counter.illegible_report_is_discovery' does not depend on any axioms -/
#guard_msgs in #print axioms illegible_report_is_discovery

/-- info: 'Foam.Counter.legibility_costs_one_edge' does not depend on any axioms -/
#guard_msgs in #print axioms legibility_costs_one_edge

end Foam.Counter
