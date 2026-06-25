import Foam.Seat.Octo

namespace Foam

def Quat.neg (x : Quat) : Quat := ⟨⟨-x.a.re, -x.a.im⟩, ⟨-x.b.re, -x.b.im⟩⟩

def Octo.zero : Octo := ⟨Quat.zero, Quat.zero⟩
def Octo.conj (X : Octo) : Octo := ⟨Quat.conj X.a, Quat.neg X.b⟩
def Octo.add (X Y : Octo) : Octo := ⟨Quat.add X.a Y.a, Quat.add X.b Y.b⟩
def Octo.subt (X Y : Octo) : Octo := ⟨Quat.subt X.a Y.a, Quat.subt X.b Y.b⟩

structure Sed where
  a : Octo
  b : Octo
  deriving DecidableEq

def Sed.mul (X Y : Sed) : Sed :=
  ⟨Octo.subt (Octo.mul X.a Y.a) (Octo.mul (Octo.conj Y.b) X.b),
   Octo.add (Octo.mul Y.b X.a) (Octo.mul X.b (Octo.conj Y.a))⟩

def Sed.zero : Sed := ⟨Octo.zero, Octo.zero⟩

def sedA : Sed := ⟨eyeO, jayO⟩
def sedB : Sed := ⟨⟨Quat.zero, eye⟩, ⟨Quat.zero, jay⟩⟩

theorem sed_zero_divisor : Sed.mul sedA sedB = Sed.zero := by decide

theorem sedA_ne_zero : sedA ≠ Sed.zero := by decide

theorem sedB_ne_zero : sedB ≠ Sed.zero := by decide

theorem division_dies :
    Sed.mul sedA sedB = Sed.zero ∧ sedA ≠ Sed.zero ∧ sedB ≠ Sed.zero :=
  ⟨sed_zero_divisor, sedA_ne_zero, sedB_ne_zero⟩

/-- info: 'Foam.division_dies' does not depend on any axioms -/
#guard_msgs in #print axioms division_dies

end Foam
