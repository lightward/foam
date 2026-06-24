import Foam.Seat.Dial

namespace Foam

def Ty05.d044 : Ty05 := ⟨0, 0⟩
def Ty05.d110 (z : Ty05) : Ty05 := ⟨z.d043, -z.d041⟩
def Ty05.d116 (z w : Ty05) : Ty05 := ⟨z.d043 - w.d043, z.d041 - w.d041⟩

structure Ty10 where
  d056 : Ty05
  d057 : Ty05
  deriving DecidableEq

def Ty10.d172 (x y : Ty10) : Ty10 :=
  ⟨Foam.Ty05.d116 (Foam.Ty05.d112 x.d056 y.d056) (Foam.Ty05.d112 (Foam.Ty05.d110 y.d057) x.d057),
   Foam.Ty05.d108 (Foam.Ty05.d112 y.d057 x.d056) (Foam.Ty05.d112 x.d057 (Foam.Ty05.d110 y.d056))⟩

def Ty10.d059 : Ty10 := ⟨⟨-1, 0⟩, ⟨0, 0⟩⟩
def d092 : Ty10 := ⟨⟨0, 1⟩, ⟨0, 0⟩⟩
def d097 : Ty10 := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩
def d224 : Ty10 := Foam.Ty10.d172 d092 d097

theorem t379 : Foam.Ty10.d172 d092 d092 = Foam.Ty10.d059 := by decide
theorem t384 : Foam.Ty10.d172 d097 d097 = Foam.Ty10.d059 := by decide
theorem t463 : Foam.Ty10.d172 d224 d224 = Foam.Ty10.d059 := by decide

theorem t178 : d097.d057 ≠ Foam.Ty05.d044 := by decide

theorem t392 : Foam.Ty10.d172 d092 d097 ≠ Foam.Ty10.d172 d097 d092 := by decide

theorem t480 :
    Foam.Ty10.d172 d092 d092 = Foam.Ty10.d059
      ∧ Foam.Ty10.d172 d097 d097 = Foam.Ty10.d059
      ∧ Foam.Ty10.d172 d224 d224 = Foam.Ty10.d059 :=
  ⟨t379, t384, t463⟩

/-- info: 'Foam.t384' does not depend on any axioms -/
#guard_msgs in #print axioms t384

/-- info: 'Foam.t392' does not depend on any axioms -/
#guard_msgs in #print axioms t392

/-- info: 'Foam.t480' does not depend on any axioms -/
#guard_msgs in #print axioms t480

end Foam
