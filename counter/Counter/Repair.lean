import Counter.Actor
import Foam.Scar
import Foam.Maintenance

namespace Foam.Counter

theorem wounds_do_not_deepen_by_sitting (k : Nat) :
    checkedDrain (Int.negSucc k) (Int.negSucc k) = Int.negSucc k :=
  scar_stable k

theorem repair_is_exact (k : Nat) :
    Int.negSucc k + Int.ofNat (debt (Int.negSucc k)) = 0 :=
  promise_kept k

theorem repair_stops_at_ground (m : Nat) :
    checkedSettle (Int.ofNat m) (Int.ofNat m) = Int.ofNat m :=
  settle_stops_at_ground m

theorem over_repair_is_real_yet_invisible :
    checkedSettle (-1) (checkedSettle (-1) (-1)) = 1
      ∧ grounded (checkedSettle (-1) (checkedSettle (-1) (-1))) :=
  ⟨stale_settle_passes_ground, phantom_invisible⟩

theorem repair_is_quiet :
    (∀ b : Int, posPart (checkedSettle b b) = posPart b)
      ∧ ∃ b : Int, posPart (checkedDrain b b) ≠ posPart b :=
  ⟨settle_invisible, drain_visible⟩

theorem no_usury (k m : Nat) :
    checkedDrain (Int.negSucc k) (Int.negSucc k) = Int.negSucc k
      ∧ Int.negSucc k + Int.ofNat (debt (Int.negSucc k)) = 0
      ∧ checkedSettle (Int.ofNat m) (Int.ofNat m) = Int.ofNat m :=
  ⟨scar_stable k, promise_kept k, settle_stops_at_ground m⟩

/-- info: 'Foam.Counter.wounds_do_not_deepen_by_sitting' does not depend on any axioms -/
#guard_msgs in #print axioms wounds_do_not_deepen_by_sitting

/-- info: 'Foam.Counter.repair_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms repair_is_exact

/-- info: 'Foam.Counter.repair_stops_at_ground' does not depend on any axioms -/
#guard_msgs in #print axioms repair_stops_at_ground

/-- info: 'Foam.Counter.over_repair_is_real_yet_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms over_repair_is_real_yet_invisible

/-- info: 'Foam.Counter.repair_is_quiet' does not depend on any axioms -/
#guard_msgs in #print axioms repair_is_quiet

/-- info: 'Foam.Counter.no_usury' does not depend on any axioms -/
#guard_msgs in #print axioms no_usury

end Foam.Counter
