import Foam.Seat.Born
import Foam.Seat.Doubling

namespace Foam


def Ty05.d111 (w z : Ty05) : Int := w.d043 * z.d041 - w.d041 * z.d043

theorem t267 (w z : Ty05) :
    Foam.Ty05.d112 w.d110 z = ⟨Foam.Ty05.d109 w z, Foam.Ty05.d111 w z⟩ := by
  show (⟨w.d043 * z.d043 - -w.d041 * z.d041, w.d043 * z.d041 + -w.d041 * z.d043⟩ : Ty05)
    = ⟨w.d043 * z.d043 + w.d041 * z.d041, w.d043 * z.d041 - w.d041 * z.d043⟩
  rw [t027 w.d041 z.d041, t027 w.d041 z.d043,
    Int.sub_eq_add_neg (a := w.d043 * z.d043) (b := -(w.d041 * z.d041)),
    Int.neg_neg, ← Int.sub_eq_add_neg]

theorem t276 (w z : Ty05) :
    Foam.Ty05.d111 w.d115 z.d115 = Foam.Ty05.d111 w z := by
  show -w.d041 * z.d043 - w.d043 * -z.d041 = w.d043 * z.d041 - w.d041 * z.d043
  rw [t027 w.d041 z.d043, t018 w.d043 z.d041,
    Int.sub_eq_add_neg (a := -(w.d041 * z.d043)) (b := -(w.d043 * z.d041)),
    Int.neg_neg,
    Int.sub_eq_add_neg (a := w.d043 * z.d041) (b := w.d041 * z.d043),
    t004 (-(w.d041 * z.d043)) (w.d043 * z.d041)]

theorem t306 (z : Ty05) : z.d114 = Foam.Ty05.d109 z z := rfl

theorem t302 (z w : Ty05) :
    Foam.Ty05.d109 z w * Foam.Ty05.d109 z w + Foam.Ty05.d111 z w * Foam.Ty05.d111 z w
      = z.d114 * w.d114 := by
  show Foam.Ty05.d109 z w * Foam.Ty05.d109 z w + Foam.Ty05.d111 z w * Foam.Ty05.d111 z w
    = (z.d043 * z.d043 + z.d041 * z.d041) * (w.d043 * w.d043 + w.d041 * w.d041)
  rw [show Foam.Ty05.d111 z w = -(z.d041 * w.d043) + z.d043 * w.d041 by
    show z.d043 * w.d041 - z.d041 * w.d043 = -(z.d041 * w.d043) + z.d043 * w.d041
    rw [Int.sub_eq_add_neg (a := z.d043 * w.d041) (b := z.d041 * w.d043),
      t004 (z.d043 * w.d041) (-(z.d041 * w.d043))]]
  exact Foam.t059 z.d043 z.d041 w.d043 w.d041

theorem t275 (θ z : Ty05) :
    Foam.Ty05.d109 θ.d115 z = Foam.Ty05.d111 θ z := by
  show -θ.d041 * z.d043 + θ.d043 * z.d041 = θ.d043 * z.d041 - θ.d041 * z.d043
  rw [t027 θ.d041 z.d043,
    Int.sub_eq_add_neg (a := θ.d043 * z.d041) (b := θ.d041 * z.d043),
    t004 (-(θ.d041 * z.d043)) (θ.d043 * z.d041)]

theorem t367 (θ z : Ty05) :
    Foam.Ty05.d165 θ z + Foam.Ty05.d165 θ.d115 z
      = Foam.Ty05.d109 θ z * Foam.Ty05.d109 θ z + Foam.Ty05.d111 θ z * Foam.Ty05.d111 θ z := by
  show Foam.Ty05.d109 θ z * Foam.Ty05.d109 θ z + Foam.Ty05.d109 θ.d115 z * Foam.Ty05.d109 θ.d115 z
    = Foam.Ty05.d109 θ z * Foam.Ty05.d109 θ z + Foam.Ty05.d111 θ z * Foam.Ty05.d111 θ z
  rw [t275 θ z]

theorem t078 : ∀ x : Int, x + x = 0 → x = 0
  | .ofNat 0, _ => rfl
  | .ofNat (n + 1), h => by
    have h' : Int.ofNat ((n + 1) + (n + 1)) = Int.ofNat 0 := h
    injection h' with h''
    exact Nat.noConfusion h''
  | .negSucc _, h => nomatch h

theorem t283 (f : Int → Int)
    (h : ∀ θ z : Ty05,
      f (Foam.Ty05.d109 θ z) + f (Foam.Ty05.d111 θ z) = θ.d114 * z.d114) :
    ∀ a : Int, f a = a * a := by
  have h0 : f 0 = 0 := t078 (f 0) (h Foam.Ty05.d044 Foam.Ty05.d044)
  intro a
  have ha : f (a * 1 + 0 * 0) + f (a * 0 - 0 * 1)
      = (a * a + 0 * 0) * (1 * 1 + 0 * 0) := h ⟨a, 0⟩ ⟨1, 0⟩
  rw [t014 a 1, Int.one_mul a, t014 a 0, t055 a,
    show (0 : Int) * 0 = 0 from rfl, show (0 : Int) * 1 = 0 from rfl,
    show (1 : Int) * 1 = 1 from rfl, show (0 : Int) - 0 = 0 from rfl,
    Int.add_zero a, Int.add_zero (a * a),
    show (1 : Int) + 0 = 1 from rfl,
    t014 (a * a) 1, Int.one_mul (a * a), h0, Int.add_zero (f a)] at ha
  exact ha

/-- info: 'Foam.t267' does not depend on any axioms -/
#guard_msgs in #print axioms t267

/-- info: 'Foam.t276' does not depend on any axioms -/
#guard_msgs in #print axioms t276

/-- info: 'Foam.t302' does not depend on any axioms -/
#guard_msgs in #print axioms t302

/-- info: 'Foam.t275' does not depend on any axioms -/
#guard_msgs in #print axioms t275

/-- info: 'Foam.t367' does not depend on any axioms -/
#guard_msgs in #print axioms t367

/-- info: 'Foam.t283' does not depend on any axioms -/
#guard_msgs in #print axioms t283

end Foam
