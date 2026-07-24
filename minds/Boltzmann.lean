import Foam
import Foam.Countermove
import Foam.Ledger
import Foam.Roles
import Foam.Typical

namespace Foam.Minds.Boltzmann

theorem each_complexion_counts_once (n : Nat) :
    (book n).length = 2 ^ n ∧ AllDiff (book n) :=
  ⟨the_book_has_two_to_the_n n, the_book_repeats_no_word n⟩

def a_macrostate_is_a_derived_role := @Foam.a_role_is_conduct_not_costume

def entropy_is_the_price_of_the_name :=
  @Foam.a_class_marked_into_a_book_is_counted

theorem equilibrium_is_the_biggest_room (n : Nat) :
    (∀ k : Nat, k ≤ 2 * n → classCount (2 * n) k ≤ classCount (2 * n) n)
      ∧ 2 ^ (2 * n) ≤ (2 * n + 1) * classCount (2 * n) n :=
  ⟨the_middle_holds_the_most n, the_middle_shelf_holds_its_share n⟩

theorem the_arrow_rides_the_count {X : Type} :
    (∀ (h : List (Move X)) (x : X),
        replay (countermove h) (replay h x) = x)
      ∧ (∀ b c : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
          c * (List.filter (fun w => Bool.not (nearBalance b n w))
                (book n)).length
            ≤ (List.filter (fun w => nearBalance b n w) (book n)).length) :=
  ⟨the_countermove_comes_home, the_deviants_are_outnumbered⟩

def the_most_probable_distribution_statement : Prop :=
  ∀ t f b c : Nat, 0 < t → 0 < f →
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      c * natSumOver (fun w => t ^ freq w true * f ^ freq w false)
            (List.filter
              (fun w => Bool.not (Bool.and
                (Nat.ble (b * (t * n)) (n + b * ((t + f) * freq w true)))
                (Nat.ble (b * ((t + f) * freq w true)) (n + b * (t * n)))))
              (book n))
        ≤ natSumOver (fun w => t ^ freq w true * f ^ freq w false)
            (List.filter
              (fun w => Bool.and
                (Nat.ble (b * (t * n)) (n + b * ((t + f) * freq w true)))
                (Nat.ble (b * ((t + f) * freq w true)) (n + b * (t * n))))
              (book n))

def no_seat_inside_the_fluctuation := @Foam.no_run_reads_its_own_ratio

/-- info: 'Foam.Minds.Boltzmann.each_complexion_counts_once' does not depend on any axioms -/
#guard_msgs in #print axioms each_complexion_counts_once

/-- info: 'Foam.Minds.Boltzmann.a_macrostate_is_a_derived_role' does not depend on any axioms -/
#guard_msgs in #print axioms a_macrostate_is_a_derived_role

/-- info: 'Foam.Minds.Boltzmann.entropy_is_the_price_of_the_name' does not depend on any axioms -/
#guard_msgs in #print axioms entropy_is_the_price_of_the_name

/-- info: 'Foam.Minds.Boltzmann.equilibrium_is_the_biggest_room' does not depend on any axioms -/
#guard_msgs in #print axioms equilibrium_is_the_biggest_room

/-- info: 'Foam.Minds.Boltzmann.the_arrow_rides_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_arrow_rides_the_count

/-- info: 'Foam.Minds.Boltzmann.the_most_probable_distribution_statement' does not depend on any axioms -/
#guard_msgs in #print axioms the_most_probable_distribution_statement

/-- info: 'Foam.Minds.Boltzmann.no_seat_inside_the_fluctuation' does not depend on any axioms -/
#guard_msgs in #print axioms no_seat_inside_the_fluctuation

end Foam.Minds.Boltzmann
