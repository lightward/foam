import Foam
import Foam.Census
import Foam.Expectation
import Foam.Ledger

namespace Foam.Minds.Gauss

def the_sum_is_deaf_to_the_shuffle := @Foam.counting_is_licensed_by_permutation

def congruent_not_equal := @Foam.the_handshake

def the_egregious_reading_descends :=
  @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

theorem the_shape_arrives_by_counting :
    freq ((book 2).map (fun w => freq w true)) 1 = 2
      ∧ freq ((book 2).map (fun w => freq w true)) 0 = 1
      ∧ freq ((book 2).map (fun w => freq w true)) 2 = 1 :=
  ⟨rfl, rfl, rfl⟩

theorem the_error_has_a_shape :
    (∀ n k : Nat, k ≤ n → classCount n k = classCount n (n - k))
      ∧ ∀ n k : Nat, 2 * k + 1 ≤ n → classCount n k ≤ classCount n (k + 1) :=
  ⟨the_census_is_symmetric, the_census_rises_to_the_middle⟩

/-- info: 'Foam.Minds.Gauss.the_sum_is_deaf_to_the_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms the_sum_is_deaf_to_the_shuffle

/-- info: 'Foam.Minds.Gauss.congruent_not_equal' does not depend on any axioms -/
#guard_msgs in #print axioms congruent_not_equal

/-- info: 'Foam.Minds.Gauss.the_egregious_reading_descends' does not depend on any axioms -/
#guard_msgs in #print axioms the_egregious_reading_descends

/-- info: 'Foam.Minds.Gauss.the_shape_arrives_by_counting' does not depend on any axioms -/
#guard_msgs in #print axioms the_shape_arrives_by_counting

/-- info: 'Foam.Minds.Gauss.the_error_has_a_shape' does not depend on any axioms -/
#guard_msgs in #print axioms the_error_has_a_shape

end Foam.Minds.Gauss
