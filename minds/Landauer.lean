import Foam
import Foam.Contact
import Foam.Countermove
import Foam.Marks
import Foam.Roles
import Foam.Tower

namespace Foam.Minds.Landauer

def information_is_physical := @Foam.a_wider_seat_reads_the_remainder

theorem erasure_shows :
    ∀ (S : Stage) (m : S.State → S.State), Invisible S m →
      ∀ s t, m s = m t → ∀ p, S.obs s p = S.obs t p :=
  fun S _ hi s t hmerge p =>
    (hi s p).symm.trans ((congrArg (S.obs · p) hmerge).trans (hi t p))

def reset_pays_in_record := @Foam.undo_in_an_append_only_world

def no_machine_undercuts_the_bill := @Foam.the_marks_pay_the_depth

def reversible_runs_free := @Foam.invisible_is_gauge

def conductance_is_transmission := @Foam.contact_is_addition_not_fixing

theorem the_demon_pays_at_the_reset (S : Stage) (X : Type) :
    (∀ (p : S.Probe) (Q : S.Ans → Prop), Derived S (fun t => Q (S.obs t p)))
      ∧ (∀ (P : (dress S).State → Prop), Derived (dress S) P →
          ∀ (s : S.State) (n m : Int), P (s, n) ↔ P (s, m))
      ∧ (∀ (h : List (Move X)) (x : X),
          replay (h ++ countermove h) x = x
            ∧ (h ≠ [] → h ++ countermove h ≠ h)) :=
  ⟨fun p Q => a_role_read_off_the_record_is_derived S p Q,
   fun P hP s n m => a_derived_role_cannot_read_the_badge S P hP s n m,
   fun h x => undo_in_an_append_only_world h x⟩

def no_disembodied_referee := @Foam.no_seat_is_the_last_seat

/-- info: 'Foam.Minds.Landauer.information_is_physical' does not depend on any axioms -/
#guard_msgs in #print axioms information_is_physical

/-- info: 'Foam.Minds.Landauer.erasure_shows' does not depend on any axioms -/
#guard_msgs in #print axioms erasure_shows

/-- info: 'Foam.Minds.Landauer.reset_pays_in_record' does not depend on any axioms -/
#guard_msgs in #print axioms reset_pays_in_record

/-- info: 'Foam.Minds.Landauer.no_machine_undercuts_the_bill' does not depend on any axioms -/
#guard_msgs in #print axioms no_machine_undercuts_the_bill

/-- info: 'Foam.Minds.Landauer.reversible_runs_free' does not depend on any axioms -/
#guard_msgs in #print axioms reversible_runs_free

/-- info: 'Foam.Minds.Landauer.conductance_is_transmission' does not depend on any axioms -/
#guard_msgs in #print axioms conductance_is_transmission

/-- info: 'Foam.Minds.Landauer.the_demon_pays_at_the_reset' does not depend on any axioms -/
#guard_msgs in #print axioms the_demon_pays_at_the_reset

/-- info: 'Foam.Minds.Landauer.no_disembodied_referee' does not depend on any axioms -/
#guard_msgs in #print axioms no_disembodied_referee

end Foam.Minds.Landauer
