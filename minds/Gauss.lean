import Foam
import Foam.Census
import Foam.Expectation
import Foam.Ledger

namespace Foam.Minds.Gauss

def the_sum_is_deaf_to_the_shuffle := @Foam.counting_is_licensed_by_permutation

def congruent_not_equal := @Foam.the_handshake

def the_egregious_reading_descends := @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

theorem the_shape_arrives_by_counting :
    ((fun (readings : (List Nat)) =>
        (And
          (Eq (Foam.freq readings 1) 2)
          (And (Eq (Foam.freq readings 0) 1) (Eq (Foam.freq readings 2) 1))))
      (List.map (fun (w : (List Bool)) => (Foam.freq w true)) (Foam.book 2))) :=
  (And.intro rfl (And.intro rfl rfl))

theorem the_error_has_a_shape :
    (And
      (∀ (n : Nat) (k : Nat) (_ : (Nat.le k n)),
        (Eq
          (List.length
            (List.filter
              (fun (w : (List Bool)) => (Nat.beq (Foam.freq w true) k))
              (Foam.book n)))
          (List.length
            (List.filter
              (fun (w : (List Bool)) =>
                (Nat.beq (Foam.freq w true) (Nat.sub n k)))
              (Foam.book n)))))
      (∀ (n : Nat) (k : Nat) (_ : (Nat.le (Nat.add (Nat.mul 2 k) 1) n)),
        (Nat.le
          (List.length
            (List.filter
              (fun (w : (List Bool)) => (Nat.beq (Foam.freq w true) k))
              (Foam.book n)))
          (List.length
            (List.filter
              (fun (w : (List Bool)) =>
                (Nat.beq (Foam.freq w true) (Nat.add k 1)))
              (Foam.book n)))))) :=
  (And.intro Foam.the_census_is_symmetric Foam.the_census_rises_to_the_middle)

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
