import Face
import Rest
import Counter
open Room Face Rest Counter
set_option autoImplicit false

namespace Halt

def stuck : room := ([], [(7, [7])])
def demo : room := ([], [(1, []), (2, [3]), (3, [])])
def seatedAfter (st : room) (k : Nat) : Option (List Nat) := (runs cascade.m cascade.steer cascade.rest st k).map (·.1)
def countAt (w : List Unit) (k : Nat) : Option Nat := (haltingGap Unit Nat).obs counting (w, k)
def carryAt (w : List Unit) (k : Nat) : Option Nat := (haltingGap Unit Nat).obs carrying (w, k)
#guard countAt [] 3 == some 3
#guard countAt [(), ()] 1 == some 3
#guard countAt [] 2 == none
#guard carryAt [] 3 == some 3
#guard carryAt [] 2 == none
#guard countAt [(), (), (), ()] 0 == carryAt [(), (), (), ()] 0
#guard seatedAfter demo 1 == none
#guard seatedAfter demo 2 == some [2, 3, 1]
#guard seatedAfter stuck 0 == some []
#guard settled stuck
#guard (sweep demo).2.length == 1
end Halt
