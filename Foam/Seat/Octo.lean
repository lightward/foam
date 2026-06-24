import Foam.Seat.Triad

namespace Foam

def Ty10.d123 : Ty10 := ⟨Foam.Ty05.d044, Foam.Ty05.d044⟩
def Ty10.d060 : Ty10 := ⟨⟨1, 0⟩, ⟨0, 0⟩⟩
def Ty10.d171 (x : Ty10) : Ty10 := ⟨Foam.Ty05.d110 x.d056, ⟨-x.d057.d043, -x.d057.d041⟩⟩
def Ty10.d170 (x y : Ty10) : Ty10 := ⟨Foam.Ty05.d108 x.d056 y.d056, Foam.Ty05.d108 x.d057 y.d057⟩
def Ty10.d173 (x y : Ty10) : Ty10 := ⟨Foam.Ty05.d116 x.d056 y.d056, Foam.Ty05.d116 x.d057 y.d057⟩

structure Ty09 where
  d053 : Ty10
  d054 : Ty10
  deriving DecidableEq

def Ty09.d209 (X Y : Ty09) : Ty09 :=
  ⟨Foam.Ty10.d173 (Foam.Ty10.d172 X.d053 Y.d053) (Foam.Ty10.d172 (Foam.Ty10.d171 Y.d054) X.d054),
   Foam.Ty10.d170 (Foam.Ty10.d172 Y.d054 X.d053) (Foam.Ty10.d172 X.d054 (Foam.Ty10.d171 Y.d053))⟩

def Ty09.d166 : Ty09 := ⟨Foam.Ty10.d059, Foam.Ty10.d123⟩

def d191 : Ty09 := ⟨d092, Foam.Ty10.d123⟩
def d192 : Ty09 := ⟨d097, Foam.Ty10.d123⟩
def d228 : Ty09 := ⟨d224, Foam.Ty10.d123⟩
def d188 : Ty09 := ⟨Foam.Ty10.d123, Foam.Ty10.d060⟩

theorem t485 : Foam.Ty09.d209 (Foam.Ty09.d209 d191 d192) d228 = Foam.Ty09.d166 := by decide

theorem t455 : Foam.Ty09.d209 d188 d188 = Foam.Ty09.d166 := by decide

theorem t454 : Foam.Ty09.d209 d191 d188 ≠ Foam.Ty09.d209 d188 d191 := by decide

theorem t466 :
    Foam.Ty09.d209 (Foam.Ty09.d209 d191 d192) d188 ≠ Foam.Ty09.d209 d191 (Foam.Ty09.d209 d192 d188) := by decide

/-- info: 'Foam.t485' does not depend on any axioms -/
#guard_msgs in #print axioms t485

/-- info: 'Foam.t455' does not depend on any axioms -/
#guard_msgs in #print axioms t455

/-- info: 'Foam.t466' does not depend on any axioms -/
#guard_msgs in #print axioms t466

end Foam
