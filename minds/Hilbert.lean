import Foam
import Foam.Int
import Foam.Margin
import Foam.Rungs
import Foam.Tower

namespace Foam.Minds.Hilbert

theorem the_proof_rides_the_marks :
    ∀ (S : Stage) (m n : S.State → S.State),
      Invisible S m → Invisible S n →
      ∀ (ps : List S.Probe) (s : S.State),
        transcriptWith S (fun t => m (n t)) s ps = transcript S s ps :=
  fun S m n hm hn =>
    invisible_is_gauge S (fun t => m (n t)) (invisible_comp S m n hm hn)

def the_arithmetic_owes_no_axiom := @Foam.FInt.mul_assoc

def the_ideal_costs_nothing_real := @Foam.the_tower_reads_only_the_ground

def the_real_is_what_the_ideal_cannot_move :=
  @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

theorem the_epsilon_settles_on_any_schedule :
    (∀ (A B : Type) (f : B → A → B) (s : B × List A),
        marginRead f (settle f s) = marginRead f s)
      ∧ (∀ (A B : Type) (f : B → A → B) (ps : List Unit) (s : B × List A),
          transcriptWith (marginStage A B f) (settle f) s ps
            = transcriptWith (marginStage A B f) (fun s => s) s ps)
      ∧ (indist (marginStage Nat Nat (· + ·)) (1, ([] : List Nat)) (0, [1])
          ∧ (marginOrderStage Nat Nat).obs (1, ([] : List Nat)) ()
              ≠ (marginOrderStage Nat Nat).obs (0, [1]) ()) :=
  ⟨fun _ _ f s => the_reading_survives_the_settle f s,
   fun A B f ps s => any_settling_cadence_reads_the_same A B f ps s,
   a_wider_seat_reads_the_tail⟩

def no_ignorabimus := @Foam.closure_is_seat_relative

/-- info: 'Foam.Minds.Hilbert.the_proof_rides_the_marks' does not depend on any axioms -/
#guard_msgs in #print axioms the_proof_rides_the_marks

/-- info: 'Foam.Minds.Hilbert.the_arithmetic_owes_no_axiom' does not depend on any axioms -/
#guard_msgs in #print axioms the_arithmetic_owes_no_axiom

/-- info: 'Foam.Minds.Hilbert.the_ideal_costs_nothing_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_ideal_costs_nothing_real

/-- info: 'Foam.Minds.Hilbert.the_real_is_what_the_ideal_cannot_move' does not depend on any axioms -/
#guard_msgs in #print axioms the_real_is_what_the_ideal_cannot_move

/-- info: 'Foam.Minds.Hilbert.the_epsilon_settles_on_any_schedule' does not depend on any axioms -/
#guard_msgs in #print axioms the_epsilon_settles_on_any_schedule

/-- info: 'Foam.Minds.Hilbert.no_ignorabimus' does not depend on any axioms -/
#guard_msgs in #print axioms no_ignorabimus

end Foam.Minds.Hilbert
