import Foam.Concentration
import Foam.Expectation
import Foam.Fold
import Foam.Int
import Foam.Ledger

namespace Foam.Minds.Chebyshev

def the_mean_arrives_first := @Foam.the_complete_book_balances

theorem the_second_moment_is_conserved :
    (∀ (n : Nat),
      (Eq
        (Foam.fold
          (fun acc w =>
            (Int.add
              acc
              (Int.mul
                (Int.sub
                  (Int.mul 2 (Int.ofNat (Foam.freq w true)))
                  (Int.ofNat n))
                (Int.sub
                  (Int.mul 2 (Int.ofNat (Foam.freq w true)))
                  (Int.ofNat n)))))
          (0 : Int)
          (Foam.book n))
        (Int.mul (Int.ofNat n) (Int.ofNat (Nat.pow 2 n))))) :=
  (fun n =>
    (Eq.trans
      (Eq.trans
        (Foam.fold_reads_the_sum
          (fun w =>
            (Int.mul
              (Int.sub
                (Int.mul 2 (Int.ofNat (Foam.freq w true)))
                (Int.ofNat n))
              (Int.sub
                (Int.mul 2 (Int.ofNat (Foam.freq w true)))
                (Int.ofNat n))))
          (Foam.book n)
          (0 : Int))
        (Foam.FInt.zero_add
          (Foam.sumOver
            (fun w =>
              (Int.mul
                (Int.sub
                  (Int.mul 2 (Int.ofNat (Foam.freq w true)))
                  (Int.ofNat n))
                (Int.sub
                  (Int.mul 2 (Int.ofNat (Foam.freq w true)))
                  (Int.ofNat n))))
            (Foam.book n))))
      (Foam.the_squares_pool_to_the_depth n)))

theorem every_deviant_pays_its_square :
    (∀ (b : Nat) (n : Nat),
      (Nat.le
        (Nat.mul
          (List.length
            (List.filter
              (fun (w : (List Bool)) =>
                (Bool.not
                  (Bool.and
                    (Nat.ble
                      (Nat.mul b n)
                      (Nat.add n (Nat.mul 2 (Nat.mul b (Foam.freq w true)))))
                    (Nat.ble
                      (Nat.mul 2 (Nat.mul b (Foam.freq w true)))
                      (Nat.add n (Nat.mul b n))))))
              (Foam.book n)))
          (Nat.mul (Nat.add n 1) (Nat.add n 1)))
        (Nat.mul (Nat.mul b b) (Nat.mul n (Nat.pow 2 n))))) :=
  (fun b n => (Foam.the_pooled_square_caps_the_deviants b n))

/-- info: 'Foam.Minds.Chebyshev.the_mean_arrives_first' does not depend on any axioms -/
#guard_msgs in #print axioms the_mean_arrives_first

/-- info: 'Foam.Minds.Chebyshev.the_second_moment_is_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_moment_is_conserved

/-- info: 'Foam.Minds.Chebyshev.every_deviant_pays_its_square' does not depend on any axioms -/
#guard_msgs in #print axioms every_deviant_pays_its_square

end Foam.Minds.Chebyshev
