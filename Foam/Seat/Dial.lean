import Foam.Seat.Clock

namespace Foam

structure Ty05 where
  d043 : Int
  d041 : Int
  deriving DecidableEq

def Ty05.d112 (z w : Ty05) : Ty05 :=
  ⟨z.d043 * w.d043 - z.d041 * w.d041, z.d043 * w.d041 + z.d041 * w.d043⟩

def Ty05.d108 (z w : Ty05) : Ty05 := ⟨z.d043 + w.d043, z.d041 + w.d041⟩

def Ty05.d040 : Ty05 := ⟨0, 1⟩
def Ty05.d114 (z : Ty05) : Int := z.d043 * z.d043 + z.d041 * z.d041

def Ty12.d063 : Ty12 → Ty05
  | Foam.Ty12.c1 => ⟨1, 0⟩
  | Foam.Ty12.c2 => ⟨0, 1⟩
  | Foam.Ty12.c3 => ⟨-1, 0⟩
  | Foam.Ty12.c4 => ⟨0, -1⟩

theorem Ty12.t228 (a b : Ty12) : (a * b).d063 = Foam.Ty05.d112 a.d063 b.d063 := by
  cases a <;> cases b <;> decide

theorem Ty12.t229 (a : Ty12) : (Foam.Ty12.c2 * a).d063 = Foam.Ty05.d112 Foam.Ty05.d040 a.d063 := by
  cases a <;> decide

theorem Ty12.t230 (a : Ty12) : a.d063.d114 = 1 := by
  cases a <;> decide

theorem Ty05.t056 (a : Int) : ∃ k : Nat, a * a = Int.ofNat k := by
  cases a with
  | ofNat m => exact ⟨m * m, rfl⟩
  | negSucc m => exact ⟨(m + 1) * (m + 1), rfl⟩

theorem Ty05.t213 (z : Ty05) : ∃ k : Nat, z.d114 = Int.ofNat k := by
  obtain ⟨k1, h1⟩ := Foam.Ty05.t056 z.d043
  obtain ⟨k2, h2⟩ := Foam.Ty05.t056 z.d041
  refine ⟨k1 + k2, ?_⟩
  show z.d043 * z.d043 + z.d041 * z.d041 = Int.ofNat (k1 + k2)
  rw [h1, h2]; rfl

/-- info: 'Foam.Ty12.t228' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t228

/-- info: 'Foam.Ty12.t229' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t229

/-- info: 'Foam.Ty12.t230' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t230

/-- info: 'Foam.Ty05.t213' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t213

end Foam
