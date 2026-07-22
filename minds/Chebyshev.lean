import Foam.Concentration
import Foam.Expectation
import Foam.Fold
import Foam.Int
import Foam.Ledger

namespace Foam.Minds.Chebyshev

def the_mean_arrives_first := @Foam.the_complete_book_balances

theorem the_second_moment_is_conserved :
    ∀ n : Nat,
      fold (fun acc w => acc + sqDev n w) 0 (book n)
        = Int.ofNat n * Int.ofNat (2 ^ n) :=
  fun n =>
    ((fold_reads_the_sum (sqDev n) (book n) 0).trans
      (FInt.zero_add (sumOver (sqDev n) (book n)))).trans
      (the_squares_pool_to_the_depth n)

theorem every_deviant_pays_its_square :
    ∀ b n : Nat,
      (List.filter (fun w => !nearBalance b n w) (book n)).length
          * ((n + 1) * (n + 1))
        ≤ (b * b) * (n * 2 ^ n) :=
  fun b n => the_pooled_square_caps_the_deviants b n

/-- info: 'Foam.Minds.Chebyshev.the_mean_arrives_first' does not depend on any axioms -/
#guard_msgs in #print axioms the_mean_arrives_first

/-- info: 'Foam.Minds.Chebyshev.the_second_moment_is_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_moment_is_conserved

/-- info: 'Foam.Minds.Chebyshev.every_deviant_pays_its_square' does not depend on any axioms -/
#guard_msgs in #print axioms every_deviant_pays_its_square


end Foam.Minds.Chebyshev
