import Foam
import Foam.Contact
import Foam.Continuum
import Foam.Engine
import Foam.Int
import Foam.Tower

namespace Foam.Minds.LEJBrouwer

theorem two_ity :
    (∀ (S : Foam.Stage), (Eq (Foam.towerN S 1) (Foam.contact S Int))) :=
  (fun _S => rfl)

def the_record_is_not_the_activity := @Foam.dropping_the_remainder_is_platonism

def the_activity_runs_unheard := @Foam.the_wheel_holds_the_emission_settles

def existence_is_exhibition := @Foam.FInt.mul_eq_zero

def the_continuum_is_never_finished := @Foam.continuum_closure_terms

/-- info: 'Foam.Minds.LEJBrouwer.two_ity' does not depend on any axioms -/
#guard_msgs in #print axioms two_ity

/-- info: 'Foam.Minds.LEJBrouwer.the_record_is_not_the_activity' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_is_not_the_activity

/-- info: 'Foam.Minds.LEJBrouwer.the_activity_runs_unheard' does not depend on any axioms -/
#guard_msgs in #print axioms the_activity_runs_unheard

/-- info: 'Foam.Minds.LEJBrouwer.existence_is_exhibition' does not depend on any axioms -/
#guard_msgs in #print axioms existence_is_exhibition

/-- info: 'Foam.Minds.LEJBrouwer.the_continuum_is_never_finished' does not depend on any axioms -/
#guard_msgs in #print axioms the_continuum_is_never_finished

end Foam.Minds.LEJBrouwer
