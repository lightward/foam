import Face
open Room Face
set_option autoImplicit false

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
