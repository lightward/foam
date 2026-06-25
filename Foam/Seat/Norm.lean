import Foam.Seat.Born
import Foam.Seat.Doubling

namespace Foam

open Foam.FInt (addComm neg_mul mul_neg)

theorem Int.neg_sq (a : Int) : -a * -a = a * a := by
  rw [neg_mul, mul_neg, Int.neg_neg]

theorem GInt.normSq_conj (z : GInt) : z.conj.normSq = z.normSq := by
  show z.re * z.re + -z.im * -z.im = z.re * z.re + z.im * z.im
  rw [Int.neg_sq z.im]

theorem GInt.normSq_mul (z w : GInt) :
    (z.mul w).normSq = z.normSq * w.normSq := by
  show (z.re * w.re - z.im * w.im) * (z.re * w.re - z.im * w.im)
      + (z.re * w.im + z.im * w.re) * (z.re * w.im + z.im * w.re)
    = (z.re * z.re + z.im * z.im) * (w.re * w.re + w.im * w.im)
  have L := Int.lagrange z.re (-z.im) w.re w.im
  rw [neg_mul z.im w.im, neg_mul z.im w.re, Int.neg_neg,
      Int.neg_sq z.im, ← Int.sub_eq_add_neg,
      addComm (z.im * w.re) (z.re * w.im)] at L
  exact L

/-- info: 'Foam.Int.neg_sq' does not depend on any axioms -/
#guard_msgs in #print axioms Int.neg_sq

/-- info: 'Foam.GInt.normSq_conj' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.normSq_conj

/-- info: 'Foam.GInt.normSq_mul' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.normSq_mul

end Foam
