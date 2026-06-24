import Foam.Seat.Octo

namespace Foam

def Ty10.d121 (x : Ty10) : Ty10 := ⟨⟨-x.d056.d043, -x.d056.d041⟩, ⟨-x.d057.d043, -x.d057.d041⟩⟩

def Ty09.d168 : Ty09 := ⟨Foam.Ty10.d123, Foam.Ty10.d123⟩
def Ty09.d208 (X : Ty09) : Ty09 := ⟨Foam.Ty10.d171 X.d053, Foam.Ty10.d121 X.d054⟩
def Ty09.d207 (X Y : Ty09) : Ty09 := ⟨Foam.Ty10.d170 X.d053 Y.d053, Foam.Ty10.d170 X.d054 Y.d054⟩
def Ty09.d210 (X Y : Ty09) : Ty09 := ⟨Foam.Ty10.d173 X.d053 Y.d053, Foam.Ty10.d173 X.d054 Y.d054⟩

structure Ty17 where
  d081 : Ty09
  d082 : Ty09
  deriving DecidableEq

def Ty17.d227 (X Y : Ty17) : Ty17 :=
  ⟨Foam.Ty09.d210 (Foam.Ty09.d209 X.d081 Y.d081) (Foam.Ty09.d209 (Foam.Ty09.d208 Y.d082) X.d082),
   Foam.Ty09.d207 (Foam.Ty09.d209 Y.d082 X.d081) (Foam.Ty09.d209 X.d082 (Foam.Ty09.d208 Y.d081))⟩

def Ty17.d216 : Ty17 := ⟨Foam.Ty09.d168, Foam.Ty09.d168⟩

def d226 : Ty17 := ⟨d191, d192⟩
def d195 : Ty17 := ⟨⟨Foam.Ty10.d123, d092⟩, ⟨Foam.Ty10.d123, d097⟩⟩

theorem t489 : Foam.Ty17.d227 d226 d195 = Foam.Ty17.d216 := by decide

theorem t476 : d226 ≠ Foam.Ty17.d216 := by decide

theorem t477 : d195 ≠ Foam.Ty17.d216 := by decide

theorem t484 :
    Foam.Ty17.d227 d226 d195 = Foam.Ty17.d216 ∧ d226 ≠ Foam.Ty17.d216 ∧ d195 ≠ Foam.Ty17.d216 :=
  ⟨t489, t476, t477⟩

/-- info: 'Foam.t484' does not depend on any axioms -/
#guard_msgs in #print axioms t484

end Foam
