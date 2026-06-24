import Foam.Seat.Born
import Foam.Seat.Doubling

namespace Foam


theorem t062 (a : Int) : -a * -a = a * a := by
  rw [t027, t018, Int.neg_neg]

theorem Ty05.t211 (z : Ty05) : z.d110.d114 = z.d114 := by
  show z.d043 * z.d043 + -z.d041 * -z.d041 = z.d043 * z.d043 + z.d041 * z.d041
  rw [Foam.t062 z.d041]

theorem Ty05.t212 (z w : Ty05) :
    (z.d112 w).d114 = z.d114 * w.d114 := by
  show (z.d043 * w.d043 - z.d041 * w.d041) * (z.d043 * w.d043 - z.d041 * w.d041)
      + (z.d043 * w.d041 + z.d041 * w.d043) * (z.d043 * w.d041 + z.d041 * w.d043)
    = (z.d043 * z.d043 + z.d041 * z.d041) * (w.d043 * w.d043 + w.d041 * w.d041)
  have L := Foam.t059 z.d043 (-z.d041) w.d043 w.d041
  rw [t027 z.d041 w.d041, t027 z.d041 w.d043, Int.neg_neg,
      Foam.t062 z.d041, ← Int.sub_eq_add_neg,
      t004 (z.d041 * w.d043) (z.d043 * w.d041)] at L
  exact L

/-- info: 'Foam.t062' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t062

/-- info: 'Foam.Ty05.t211' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t211

/-- info: 'Foam.Ty05.t212' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t212

end Foam
