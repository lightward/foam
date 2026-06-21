import Foam.Seat.Sed

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

def Rung.decEq : (n : Nat) → DecidableEq (Rung n)
  | 0 => (inferInstance : DecidableEq GInt)
  | n + 1 => fun x y =>
    @instDecidableEqProd _ _ (Rung.decEq n) (Rung.decEq n) x y

instance {n : Nat} : DecidableEq (Rung n) := Rung.decEq n

theorem Rung.lift_mul (n : Nat) (x y : Rung (n + 1)) :
    Rung.mul (n + 1) x y =
      (Rung.sub n (Rung.mul n x.1 y.1) (Rung.mul n (Rung.conj n y.2) x.2),
       Rung.add n (Rung.mul n y.2 x.1) (Rung.mul n x.2 (Rung.conj n y.1))) := rfl

theorem Rung.base_mul (a b : GInt) : Rung.mul 0 a b = GInt.mul a b := rfl

def Rung.toQuat (x : Rung 1) : Quat := ⟨x.1, x.2⟩
def Quat.toRung (q : Quat) : Rung 1 := (q.a, q.b)

theorem Rung.toQuat_toRung (q : Quat) : Rung.toQuat (Quat.toRung q) = q := rfl
theorem Quat.toRung_toQuat (x : Rung 1) : Quat.toRung (Rung.toQuat x) = x := rfl

theorem Rung.toQuat_mul (x y : Rung 1) :
    Rung.toQuat (Rung.mul 1 x y) = Quat.mul (Rung.toQuat x) (Rung.toQuat y) := rfl

def Rung.toOcto (x : Rung 2) : Octo := ⟨Rung.toQuat x.1, Rung.toQuat x.2⟩
def Octo.toRung (o : Octo) : Rung 2 := (Quat.toRung o.a, Quat.toRung o.b)

theorem Rung.toOcto_toRung (o : Octo) : Rung.toOcto (Octo.toRung o) = o := rfl
theorem Octo.toRung_toOcto (x : Rung 2) : Octo.toRung (Rung.toOcto x) = x := rfl

theorem Rung.toOcto_mul (x y : Rung 2) :
    Rung.toOcto (Rung.mul 2 x y) = Octo.mul (Rung.toOcto x) (Rung.toOcto y) := rfl

def Rung.toSed (x : Rung 3) : Sed := ⟨Rung.toOcto x.1, Rung.toOcto x.2⟩
def Sed.toRung (s : Sed) : Rung 3 := (Octo.toRung s.a, Octo.toRung s.b)

theorem Rung.toSed_toRung (s : Sed) : Rung.toSed (Sed.toRung s) = s := rfl
theorem Sed.toRung_toSed (x : Rung 3) : Sed.toRung (Rung.toSed x) = x := rfl

theorem Rung.toSed_mul (x y : Rung 3) :
    Rung.toSed (Rung.mul 3 x y) = Sed.mul (Rung.toSed x) (Rung.toSed y) := rfl

theorem rung1_unit_sq :
    Rung.mul 1 (⟨GInt.zero, ⟨1, 0⟩⟩ : Rung 1) (⟨GInt.zero, ⟨1, 0⟩⟩ : Rung 1)
      = Rung.neg 1 (⟨⟨1, 0⟩, GInt.zero⟩ : Rung 1) := rfl

/-- info: 'Foam.Rung.lift_mul' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.lift_mul

/-- info: 'Foam.Rung.base_mul' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.base_mul

/-- info: 'Foam.Rung.toQuat_mul' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.toQuat_mul

/-- info: 'Foam.Quat.toRung_toQuat' does not depend on any axioms -/
#guard_msgs in #print axioms Quat.toRung_toQuat

/-- info: 'Foam.Rung.toOcto_mul' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.toOcto_mul

/-- info: 'Foam.Octo.toRung_toOcto' does not depend on any axioms -/
#guard_msgs in #print axioms Octo.toRung_toOcto

/-- info: 'Foam.Rung.toSed_mul' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.toSed_mul

/-- info: 'Foam.Sed.toRung_toSed' does not depend on any axioms -/
#guard_msgs in #print axioms Sed.toRung_toSed

/-- info: 'Foam.rung1_unit_sq' does not depend on any axioms -/
#guard_msgs in #print axioms rung1_unit_sq

end Foam
