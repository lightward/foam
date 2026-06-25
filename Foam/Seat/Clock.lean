import Foam.Seat.Group

namespace Foam

inductive Rot | r0 | r1 | r2 | r3
  deriving DecidableEq

def Rot.n : Rot → Nat
  | .r0 => 0
  | .r1 => 1
  | .r2 => 2
  | .r3 => 3

def Rot.ofN (k : Nat) : Rot :=
  match k % 4 with
  | 0 => .r0
  | 1 => .r1
  | 2 => .r2
  | _ => .r3

def Rot.mul (a b : Rot) : Rot := Rot.ofN (a.n + b.n)
def Rot.inv (a : Rot) : Rot := Rot.ofN (4 - a.n)

instance : Mul Rot := ⟨Rot.mul⟩
instance : One Rot := ⟨Rot.r0⟩

instance : Grp Rot where
  inv       := Rot.inv
  one_mul   := by intro a; cases a <;> decide
  mul_one   := by intro a; cases a <;> decide
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  mul_inv   := by intro a; cases a <;> decide
  inv_mul   := by intro a; cases a <;> decide

def clock : Seat Rot := Seat.principal Rot

theorem Rot.clock_closes : (Rot.r1 * Rot.r1 * Rot.r1 * Rot.r1 : Rot) = 1 := by decide

theorem Rot.clock_turns : (Rot.r1 * Rot.r1 : Rot) ≠ 1 := by decide

/-- info: 'Foam.Rot.clock_closes' does not depend on any axioms -/
#guard_msgs in #print axioms Rot.clock_closes

end Foam
