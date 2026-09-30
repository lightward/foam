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
def countPlan (w : List Unit) (k : Nat) : Option Nat := read counting (plan counting w) k
def cascadePlan (w : List Unit) (k : Nat) : Option (List Nat) := (read cascade (plan cascade w) k).map (·.1)
def cascadeAt (st : room) (k : Nat) : Option (List Nat) := (read cascade st k).map (·.1)
#guard countPlan [] 3 == countAt [] 3
#guard countPlan [(), ()] 1 == countAt [(), ()] 1
#guard countPlan [] 2 == none
#guard countPlan [] 5 == countPlan [] 3
#guard cascadePlan [] 0 == some []
#guard cascadeAt demo 0 == none
#guard cascadeAt demo 3 == some [2, 3, 1]
#guard cascadeAt demo 9 == cascadeAt demo 3
#guard cascadeAt stuck 0 == some []

theorem the_counters_plan_is_read_at_the_gap (w : List Unit) (k : Nat) :
    read counting (plan counting w) k = (haltingGap Unit Nat).obs counting (w, k) := sorry

theorem two_readers_of_the_counter_agree (w : List Unit) (o o' : Nat) (f f' : Nat)
    (h : read counting (plan counting w) f = some o) (h' : read counting (plan counting w) f' = some o') : o = o' := sorry

theorem the_cascades_replay_reads_its_plan (w : List Unit) (k : Nat) :
    read (replayRunner cascade) (plan (replayRunner cascade) w) k = read cascade (plan cascade w) k := sorry

theorem a_plan_read_is_a_meeting_at_a_door (w : List Unit) (k : Nat) :
    read counting (plan counting w) k = walkIn (haltingGap Unit Nat).obs (atTheDoor counting (w, k)) := sorry

end Halt
