import Foam.Seat.Quiver
import Foam.Seat.Sort
import Foam.Seat.Tight
import Counter.Health

namespace Foam.Counter

theorem one_clean_door_certifies {H : Type} {q : Quiver H} {r : H → Nat}
    (hclean : defect r q = 0) : Acyclic q :=
  tsortable_acyclic ⟨r, (defect_zero_iff r q).mp hclean⟩

theorem a_knot_defeats_the_whole_coven {H : Type} {q : Quiver H} {a : H}
    (p : Path q a a) (hp : p.edges ≠ []) : ∀ r : H → Nat, defect r q ≠ 0 :=
  feedback_is_no_gauge p hp

theorem later_doors_find_only_tellings {H : Type} [DecidableEq H] {q : Quiver H}
    {r : H → Nat} (hclean : defect r q = 0) : feedback q = 0 :=
  (the_minimum_reads_health q).mpr (one_clean_door_certifies hclean)

theorem the_covenstead_rule {H : Type} [DecidableEq H] (q : Quiver H)
    (r r' : H → Nat) (hclean : defect r q = 0) :
    Acyclic q
      ∧ feedback q = 0
      ∧ feedback q ≤ defect r' q :=
  ⟨one_clean_door_certifies hclean,
   later_doors_find_only_tellings hclean,
   feedback_le q r'⟩

/-- info: 'Foam.Counter.one_clean_door_certifies' does not depend on any axioms -/
#guard_msgs in #print axioms one_clean_door_certifies

/-- info: 'Foam.Counter.a_knot_defeats_the_whole_coven' does not depend on any axioms -/
#guard_msgs in #print axioms a_knot_defeats_the_whole_coven

/-- info: 'Foam.Counter.later_doors_find_only_tellings' does not depend on any axioms -/
#guard_msgs in #print axioms later_doors_find_only_tellings

/-- info: 'Foam.Counter.the_covenstead_rule' does not depend on any axioms -/
#guard_msgs in #print axioms the_covenstead_rule

end Foam.Counter
