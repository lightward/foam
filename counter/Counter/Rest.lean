import Counter.Actor
import Foam.Held
import Foam.Engine.Drain

namespace Foam.Counter

theorem the_fold_is_real_and_unrecorded (S : Stage) (m : S.State → S.State)
    (h : Invisible S m) (ps : List S.Probe) (s : S.State) :
    transcriptWith S m s ps = transcript S s ps :=
  maintenance_unobservable S m h ps s

theorem any_cadence_is_licensed {S C : Type} [DecidableEq S]
    (refresh : List S → C → C) :
    Invisible (LedgerStage S C) (fun st => (st.1, refresh st.1 st.2)) :=
  sweep_invisible refresh

theorem ground_holds : drainOne 0 = 0 :=
  drain_floor

/-- info: 'Foam.Counter.the_fold_is_real_and_unrecorded' does not depend on any axioms -/
#guard_msgs in #print axioms the_fold_is_real_and_unrecorded

/-- info: 'Foam.Counter.any_cadence_is_licensed' does not depend on any axioms -/
#guard_msgs in #print axioms any_cadence_is_licensed

/-- info: 'Foam.Counter.ground_holds' does not depend on any axioms -/
#guard_msgs in #print axioms ground_holds

end Foam.Counter
