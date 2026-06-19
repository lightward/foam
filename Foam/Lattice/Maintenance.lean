import Foam.Lattice.Dial

namespace Foam.Lattice

def evalBeats {S : Type} [DecidableEq S] (step : GInt → GInt) : List (Option S) → S → GInt
  | [],          _ => GInt.zero
  | none :: l,   s => step (evalBeats step l s)
  | some x :: l, s => (if x = s then GInt.one else GInt.zero).add (step (evalBeats step l s))

theorem rest_turns {S : Type} [DecidableEq S] (step : GInt → GInt) (l : List (Option S)) (s : S) :
    evalBeats step (none :: l) s = step (evalBeats step l s) := rfl

theorem bar_invisible {S : Type} [DecidableEq S] (l : List (Option S)) (s : S) :
    evalBeats GInt.rot (none :: none :: none :: none :: l) s = evalBeats GInt.rot l s := by
  show ((((evalBeats GInt.rot l s).rot).rot).rot).rot = evalBeats GInt.rot l s
  exact GInt.rot_complete _

theorem bar_undetectable_maintenance {S : Type} [DecidableEq S] (l : List (Option S)) (s : S) :
    evalBeats GInt.rot (none :: none :: none :: none :: l) s = evalBeats GInt.rot l s
      ∧ (none :: none :: none :: none :: l).length = l.length + 4 :=
  ⟨bar_invisible l s, rfl⟩

/-- info: 'Foam.Lattice.bar_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms bar_invisible

/-- info: 'Foam.Lattice.bar_undetectable_maintenance' does not depend on any axioms -/
#guard_msgs in #print axioms bar_undetectable_maintenance

end Foam.Lattice
