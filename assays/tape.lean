import Face
import Rest
open Room Face Rest
set_option autoImplicit false

namespace Tape

universe w

def tended : Machine Nat Nat := tend adder (0 : Nat) recordTheState
def taped : Machine Nat Nat := tape adder (0 : Nat) recordTheState readThrough
def untended : Nat := behavior adder [1, 1, 1]
def tendedRuns : Nat := behavior tended [1, 1, 1]
def tapedRuns : Nat := behavior taped [1, 1, 1]
def tapeAfterTwo : Nat := met (park tended (atTheDoor (0 : Nat) (0 : Nat)) [1, 1])
def stateAfterTwo : Nat := face (park tended (atTheDoor (0 : Nat) (0 : Nat)) [1, 1])
def unreadTape : Nat := behavior (tape adder (0 : Nat) recordTheState (fun _ i => i)) [1, 1, 1]

#guard untended == 3
#guard tendedRuns == 3
#guard tapedRuns == 4
#guard tapeAfterTwo == 1
#guard stateAfterTwo == 2
#guard unreadTape == untended

def rememberedAdder : Machine Nat Nat := remembering adder
def adderRemembers : List Nat := met (park rememberedAdder (atTheDoor (0 : Nat) ([] : List Nat)) [1, 1, 1])
def adderForgets : door Nat (List Nat) :=
  unstep adder (unstep adder (unstep adder (park rememberedAdder (atTheDoor (0 : Nat) ([] : List Nat)) [1, 1, 1])))
def rememberedRuns : Nat := behavior rememberedAdder [1, 1, 1]

#guard adderRemembers == [2, 1, 0]
#guard face adderForgets == 0
#guard met adderForgets == []
#guard rememberedRuns == untended

theorem a_wait_is_a_still_plan_on_its_own_tape {I O : Type} (R : Runner.{0, 0, w} I O) (hstill : ∀ s, R.m.step s (R.steer s) = s)
    (n : Nat) (s : R.m.S) (m : Machine.{0, 0, w} I O) (d : door m.S (List m.S)) (i : I) (u : List I) :
    runs R.m R.steer R.rest s n = cond (R.rest s) (some (R.m.out s)) none
      ∧ (readable R s ↔ R.rest s = true)
      ∧ unstep m ((remembering m).step d i) = d
      ∧ (met (park (remembering m) d u)).length = (met d).length + u.length :=
  ⟨a_still_runner_rests_where_it_stands R hstill n s, the_still_plan_is_readable_iff_at_rest R hstill s,
   the_remembering_step_retracts m d i, the_bill_is_the_word m u d⟩

end Tape
