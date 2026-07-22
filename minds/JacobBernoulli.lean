import Foam
import Foam.Concentration
import Foam.Expectation
import Foam.Ledger

namespace Foam.Minds.JacobBernoulli

def eadem_mutata_resurgo := @Foam.the_remainder_is_real

def the_trials_are_deaf_to_their_order := @Foam.counting_is_licensed_by_permutation

def the_whole_book_balances := @Foam.the_complete_book_balances

theorem what_frequency_promises :
    (∀ (b : Nat) (c : Nat),
      (Exists
        (fun (N : Nat) =>
          (∀ (n : Nat) (_ : (Nat.le N n)),
            (Nat.le
              (Nat.mul
                c
                (List.length
                  (List.filter
                    (fun (w : (List Bool)) =>
                      (Bool.not
                        (Bool.and
                          (Nat.ble
                            (Nat.mul b n)
                            (Nat.add
                              n
                              (Nat.mul 2 (Nat.mul b (Foam.freq w true)))))
                          (Nat.ble
                            (Nat.mul 2 (Nat.mul b (Foam.freq w true)))
                            (Nat.add n (Nat.mul b n))))))
                    (Foam.book n))))
              (List.length
                (List.filter
                  (fun (w : (List Bool)) =>
                    (Bool.and
                      (Nat.ble
                        (Nat.mul b n)
                        (Nat.add n (Nat.mul 2 (Nat.mul b (Foam.freq w true)))))
                      (Nat.ble
                        (Nat.mul 2 (Nat.mul b (Foam.freq w true)))
                        (Nat.add n (Nat.mul b n)))))
                  (Foam.book n)))))))) :=
  (fun b c => (Foam.the_deviants_are_outnumbered b c))

/-- info: 'Foam.Minds.JacobBernoulli.eadem_mutata_resurgo' does not depend on any axioms -/
#guard_msgs in #print axioms eadem_mutata_resurgo

/-- info: 'Foam.Minds.JacobBernoulli.the_trials_are_deaf_to_their_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_trials_are_deaf_to_their_order

/-- info: 'Foam.Minds.JacobBernoulli.the_whole_book_balances' does not depend on any axioms -/
#guard_msgs in #print axioms the_whole_book_balances

/-- info: 'Foam.Minds.JacobBernoulli.what_frequency_promises' does not depend on any axioms -/
#guard_msgs in #print axioms what_frequency_promises

end Foam.Minds.JacobBernoulli
