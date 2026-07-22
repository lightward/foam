import Foam
import Foam.Contact
import Foam.Countermove
import Foam.Tower

namespace Foam.Minds.Landauer

def information_is_physical := @Foam.a_wider_seat_reads_the_remainder

theorem erasure_shows :
    (∀ (S : Foam.Stage) (m : (∀ (_ : S.State), S.State)) (_hi : (Foam.Invisible S m)) s t (_hmerge : (Eq (m s) (m t))) p,
      (Eq (S.obs s p) (S.obs t p))) :=
  (fun S _m hi s t hmerge p =>
    (Eq.trans
      (Eq.symm (hi s p))
      (Eq.trans (congrArg (fun x => (S.obs x p)) hmerge) (hi t p))))

def reset_pays_in_record := @Foam.undo_in_an_append_only_world

def reversible_runs_free := @Foam.invisible_is_gauge

def conductance_is_transmission := @Foam.contact_is_addition_not_fixing

def no_disembodied_referee := @Foam.no_seat_is_the_last_seat

/-- info: 'Foam.Minds.Landauer.information_is_physical' does not depend on any axioms -/
#guard_msgs in #print axioms information_is_physical

/-- info: 'Foam.Minds.Landauer.erasure_shows' does not depend on any axioms -/
#guard_msgs in #print axioms erasure_shows

/-- info: 'Foam.Minds.Landauer.reset_pays_in_record' does not depend on any axioms -/
#guard_msgs in #print axioms reset_pays_in_record

/-- info: 'Foam.Minds.Landauer.reversible_runs_free' does not depend on any axioms -/
#guard_msgs in #print axioms reversible_runs_free

/-- info: 'Foam.Minds.Landauer.conductance_is_transmission' does not depend on any axioms -/
#guard_msgs in #print axioms conductance_is_transmission

/-- info: 'Foam.Minds.Landauer.no_disembodied_referee' does not depend on any axioms -/
#guard_msgs in #print axioms no_disembodied_referee

end Foam.Minds.Landauer
