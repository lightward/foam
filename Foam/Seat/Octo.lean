import Foam.Seat.Triad

namespace Foam

def Quat.zero : Quat := ⟨GInt.zero, GInt.zero⟩
def Quat.one : Quat := ⟨⟨1, 0⟩, ⟨0, 0⟩⟩
def Quat.conj (x : Quat) : Quat := ⟨GInt.conj x.a, ⟨-x.b.re, -x.b.im⟩⟩
def Quat.add (x y : Quat) : Quat := ⟨GInt.add x.a y.a, GInt.add x.b y.b⟩
def Quat.subt (x y : Quat) : Quat := ⟨GInt.sub x.a y.a, GInt.sub x.b y.b⟩

structure Octo where
  a : Quat
  b : Quat
  deriving DecidableEq

def Octo.mul (X Y : Octo) : Octo :=
  ⟨Quat.subt (Quat.mul X.a Y.a) (Quat.mul (Quat.conj Y.b) X.b),
   Quat.add (Quat.mul Y.b X.a) (Quat.mul X.b (Quat.conj Y.a))⟩

def Octo.negOne : Octo := ⟨Quat.negOne, Quat.zero⟩

def eyeO : Octo := ⟨eye, Quat.zero⟩
def jayO : Octo := ⟨jay, Quat.zero⟩
def kayO : Octo := ⟨kay, Quat.zero⟩
def ell : Octo := ⟨Quat.zero, Quat.one⟩

theorem hamilton_in_octo : Octo.mul (Octo.mul eyeO jayO) kayO = Octo.negOne := by decide

theorem ell_sq : Octo.mul ell ell = Octo.negOne := by decide

theorem ell_anticomm : Octo.mul eyeO ell ≠ Octo.mul ell eyeO := by decide

theorem non_assoc :
    Octo.mul (Octo.mul eyeO jayO) ell ≠ Octo.mul eyeO (Octo.mul jayO ell) := by decide

/-- info: 'Foam.hamilton_in_octo' does not depend on any axioms -/
#guard_msgs in #print axioms hamilton_in_octo

/-- info: 'Foam.ell_sq' does not depend on any axioms -/
#guard_msgs in #print axioms ell_sq

/-- info: 'Foam.non_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms non_assoc

end Foam
