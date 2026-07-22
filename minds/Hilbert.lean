import Foam
import Foam.Int
import Foam.Rungs
import Foam.Tower

namespace Foam.Minds.Hilbert

theorem the_proof_rides_the_marks :
    (∀ (S : Foam.Stage) (m : (∀ (_ : S.State), S.State)) (n : (∀ (_ : S.State), S.State)) (_hm : (Foam.Invisible S m)) (_hn : (Foam.Invisible S n)) (ps : (List S.Probe)) (s : S.State),
      (Eq
        (Foam.transcriptWith S (fun t => (m (n t))) s ps)
        (Foam.transcript S s ps))) :=
  (fun S m n hm hn =>
    (Foam.invisible_is_gauge
      S
      (fun t => (m (n t)))
      (Foam.invisible_comp S m n hm hn)))

def the_arithmetic_owes_no_axiom := @Foam.FInt.mul_assoc

def the_ideal_costs_nothing_real := @Foam.the_tower_reads_only_the_ground

def the_real_is_what_the_ideal_cannot_move := @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

def no_ignorabimus := @Foam.closure_is_seat_relative

/-- info: 'Foam.Minds.Hilbert.the_proof_rides_the_marks' does not depend on any axioms -/
#guard_msgs in #print axioms the_proof_rides_the_marks

/-- info: 'Foam.Minds.Hilbert.the_arithmetic_owes_no_axiom' does not depend on any axioms -/
#guard_msgs in #print axioms the_arithmetic_owes_no_axiom

/-- info: 'Foam.Minds.Hilbert.the_ideal_costs_nothing_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_ideal_costs_nothing_real

/-- info: 'Foam.Minds.Hilbert.the_real_is_what_the_ideal_cannot_move' does not depend on any axioms -/
#guard_msgs in #print axioms the_real_is_what_the_ideal_cannot_move

/-- info: 'Foam.Minds.Hilbert.no_ignorabimus' does not depend on any axioms -/
#guard_msgs in #print axioms no_ignorabimus

end Foam.Minds.Hilbert
