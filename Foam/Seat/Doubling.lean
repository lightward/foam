import Foam.Seat.Dial

namespace Foam

def GInt.zero : GInt := ⟨0, 0⟩
def GInt.conj (z : GInt) : GInt := ⟨z.re, -z.im⟩
def GInt.sub (z w : GInt) : GInt := ⟨z.re - w.re, z.im - w.im⟩

structure Quat where
  a : GInt
  b : GInt
  deriving DecidableEq

def Quat.mul (x y : Quat) : Quat :=
  ⟨GInt.sub (GInt.mul x.a y.a) (GInt.mul (GInt.conj y.b) x.b),
   GInt.add (GInt.mul y.b x.a) (GInt.mul x.b (GInt.conj y.a))⟩

def Quat.negOne : Quat := ⟨⟨-1, 0⟩, ⟨0, 0⟩⟩
def eye : Quat := ⟨⟨0, 1⟩, ⟨0, 0⟩⟩
def jay : Quat := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩
def kay : Quat := Quat.mul eye jay

theorem eye_sq : Quat.mul eye eye = Quat.negOne := by decide
theorem jay_sq : Quat.mul jay jay = Quat.negOne := by decide
theorem kay_sq : Quat.mul kay kay = Quat.negOne := by decide

theorem jay_outside : jay.b ≠ GInt.zero := by decide

theorem order_arrives : Quat.mul eye jay ≠ Quat.mul jay eye := by decide

theorem three_imaginaries :
    Quat.mul eye eye = Quat.negOne
      ∧ Quat.mul jay jay = Quat.negOne
      ∧ Quat.mul kay kay = Quat.negOne :=
  ⟨eye_sq, jay_sq, kay_sq⟩

/-- info: 'Foam.jay_sq' does not depend on any axioms -/
#guard_msgs in #print axioms jay_sq

/-- info: 'Foam.order_arrives' does not depend on any axioms -/
#guard_msgs in #print axioms order_arrives

/-- info: 'Foam.three_imaginaries' does not depend on any axioms -/
#guard_msgs in #print axioms three_imaginaries

end Foam
