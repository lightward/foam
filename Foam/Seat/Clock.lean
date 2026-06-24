import Foam.Seat.Group

namespace Foam

inductive Ty12 | c1 | c2 | c3 | c4
  deriving DecidableEq

def Ty12.d065 : Ty12 → Nat
  | Foam.Ty12.c1 => 0
  | Foam.Ty12.c2 => 1
  | Foam.Ty12.c3 => 2
  | Foam.Ty12.c4 => 3

def Ty12.d125 (k : Nat) : Ty12 :=
  match k % 4 with
  | 0 => Foam.Ty12.c1
  | 1 => Foam.Ty12.c2
  | 2 => Foam.Ty12.c3
  | _ => Foam.Ty12.c4

def Ty12.d175 (a b : Ty12) : Ty12 := Foam.Ty12.d125 (a.d065 + b.d065)
def Ty12.d174 (a : Ty12) : Ty12 := Foam.Ty12.d125 (4 - a.d065)

instance : Mul Ty12 := ⟨Foam.Ty12.d175⟩
instance : One Ty12 := ⟨Foam.Ty12.c1⟩

instance : Ty06 Ty12 where
  d046       := Foam.Ty12.d174
  t144   := by intro a; cases a <;> decide
  t143   := by intro a; cases a <;> decide
  t141 := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  t142   := by intro a; cases a <;> decide
  t140   := by intro a; cases a <;> decide

def d222 : Ty16 Ty12 := Foam.Ty16.d181 Ty12

theorem Ty12.t150 : (Foam.Ty12.c2 * Foam.Ty12.c2 * Foam.Ty12.c2 * Foam.Ty12.c2 : Ty12) = 1 := by decide

theorem Ty12.t151 : (Foam.Ty12.c2 * Foam.Ty12.c2 : Ty12) ≠ 1 := by decide

/-- info: 'Foam.Ty12.t150' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t150

end Foam
