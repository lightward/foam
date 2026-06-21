import Foam.Seat.Doubling
import Foam.Seat.Dial

namespace Foam

def Rung : Nat → Type
  | 0 => GInt
  | n + 1 => Rung n × Rung n

def Rung.zero : (n : Nat) → Rung n
  | 0 => GInt.zero
  | n + 1 => (Rung.zero n, Rung.zero n)

def Rung.add : (n : Nat) → Rung n → Rung n → Rung n
  | 0, a, b => GInt.add a b
  | n + 1, x, y => (Rung.add n x.1 y.1, Rung.add n x.2 y.2)

def Rung.neg : (n : Nat) → Rung n → Rung n
  | 0, a => ⟨-a.re, -a.im⟩
  | n + 1, x => (Rung.neg n x.1, Rung.neg n x.2)

def Rung.sub (n : Nat) (x y : Rung n) : Rung n :=
  Rung.add n x (Rung.neg n y)

def Rung.conj : (n : Nat) → Rung n → Rung n
  | 0, a => GInt.conj a
  | n + 1, x => (Rung.conj n x.1, Rung.neg n x.2)

def Rung.mul : (n : Nat) → Rung n → Rung n → Rung n
  | 0, a, b => GInt.mul a b
  | n + 1, x, y =>
    (Rung.sub n (Rung.mul n x.1 y.1) (Rung.mul n (Rung.conj n y.2) x.2),
     Rung.add n (Rung.mul n y.2 x.1) (Rung.mul n x.2 (Rung.conj n y.1)))

def Rung.normSq : (n : Nat) → Rung n → Int
  | 0, a => GInt.normSq a
  | n + 1, x => Rung.normSq n x.1 + Rung.normSq n x.2

def Rung.e : (n : Nat) → Nat → Rung n
  | 0, _ => ⟨1, 0⟩
  | n + 1, i =>
    if i < 2 ^ n then (Rung.e n i, Rung.zero n)
    else (Rung.zero n, Rung.e n (i - 2 ^ n))

def Rung.decEq : (n : Nat) → DecidableEq (Rung n)
  | 0 => (inferInstance : DecidableEq GInt)
  | n + 1 => fun x y =>
    @instDecidableEqProd _ _ (Rung.decEq n) (Rung.decEq n) x y

instance {n : Nat} : DecidableEq (Rung n) := Rung.decEq n

def Rung.toQuat (x : Rung 1) : Quat := ⟨x.1, x.2⟩

def Quat.toRung (q : Quat) : Rung 1 := (q.a, q.b)

theorem Rung.toQuat_left_inv (x : Rung 1) : Quat.toRung (Rung.toQuat x) = x := rfl

theorem Rung.toQuat_right_inv (q : Quat) : Rung.toQuat (Quat.toRung q) = q := rfl

theorem Rung.toQuat_zero : Rung.toQuat (Rung.zero 1) = (⟨GInt.zero, GInt.zero⟩ : Quat) := rfl

theorem Rung.toQuat_mul (x y : Rung 1) :
    Rung.toQuat (Rung.mul 1 x y) = Quat.mul (Rung.toQuat x) (Rung.toQuat y) := rfl

theorem Rung.base_conj (a : GInt) : Rung.conj 0 a = GInt.conj a := rfl

theorem Rung.base_mul (a b : GInt) : Rung.mul 0 a b = GInt.mul a b := rfl

theorem Rung.base_add (a b : GInt) : Rung.add 0 a b = GInt.add a b := rfl

theorem Rung.lift_mul (n : Nat) (x y : Rung (n + 1)) :
    Rung.mul (n + 1) x y =
      (Rung.sub n (Rung.mul n x.1 y.1) (Rung.mul n (Rung.conj n y.2) x.2),
       Rung.add n (Rung.mul n y.2 x.1) (Rung.mul n x.2 (Rung.conj n y.1))) := rfl

theorem lift_one_pays_order :
    Rung.mul 1 (Rung.e 1 1) (Rung.e 1 1) = Rung.neg 1 (Rung.e 1 0) := rfl

theorem lift_two_pays_commutation :
    Rung.mul 2 (Rung.e 2 1) (Rung.e 2 2)
      = Rung.neg 2 (Rung.mul 2 (Rung.e 2 2) (Rung.e 2 1))
    ∧ Rung.mul 2 (Rung.e 2 1) (Rung.e 2 2)
      ≠ Rung.mul 2 (Rung.e 2 2) (Rung.e 2 1) :=
  ⟨rfl, by decide⟩

theorem lift_three_pays_association :
    Rung.mul 3 (Rung.mul 3 (Rung.e 3 1) (Rung.e 3 2)) (Rung.e 3 4)
      = Rung.neg 3 (Rung.mul 3 (Rung.e 3 1) (Rung.mul 3 (Rung.e 3 2) (Rung.e 3 4)))
    ∧ Rung.mul 3 (Rung.mul 3 (Rung.e 3 1) (Rung.e 3 2)) (Rung.e 3 4)
      ≠ Rung.mul 3 (Rung.e 3 1) (Rung.mul 3 (Rung.e 3 2) (Rung.e 3 4)) :=
  ⟨rfl, by decide⟩

def sedLeft : Rung 4 := Rung.add 4 (Rung.e 4 1) (Rung.e 4 10)

def sedRight : Rung 4 := Rung.sub 4 (Rung.e 4 4) (Rung.e 4 15)

theorem lift_four_pays_presence :
    sedLeft ≠ Rung.zero 4 ∧ sedRight ≠ Rung.zero 4
      ∧ Rung.mul 4 sedLeft sedRight = Rung.zero 4 :=
  ⟨by decide, by decide, rfl⟩

theorem norm_stops_composing :
    Rung.normSq 4 sedLeft * Rung.normSq 4 sedRight
      ≠ Rung.normSq 4 (Rung.mul 4 sedLeft sedRight) := by
  decide

/-- info: 'Foam.Rung.toQuat_left_inv' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.toQuat_left_inv

/-- info: 'Foam.Rung.toQuat_right_inv' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.toQuat_right_inv

/-- info: 'Foam.Rung.toQuat_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.toQuat_zero

/-- info: 'Foam.Rung.toQuat_mul' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.toQuat_mul

/-- info: 'Foam.Rung.base_conj' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.base_conj

/-- info: 'Foam.Rung.base_mul' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.base_mul

/-- info: 'Foam.Rung.base_add' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.base_add

/-- info: 'Foam.Rung.lift_mul' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.lift_mul

/-- info: 'Foam.lift_one_pays_order' does not depend on any axioms -/
#guard_msgs in #print axioms lift_one_pays_order

/-- info: 'Foam.lift_two_pays_commutation' does not depend on any axioms -/
#guard_msgs in #print axioms lift_two_pays_commutation

/-- info: 'Foam.lift_three_pays_association' does not depend on any axioms -/
#guard_msgs in #print axioms lift_three_pays_association

/-- info: 'Foam.lift_four_pays_presence' does not depend on any axioms -/
#guard_msgs in #print axioms lift_four_pays_presence

/-- info: 'Foam.norm_stops_composing' does not depend on any axioms -/
#guard_msgs in #print axioms norm_stops_composing

end Foam