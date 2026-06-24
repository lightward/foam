import Foam.Golden
import Foam.Int

namespace Foam


def d028 : Nat → List Bool → Int
  | _, [] => 0
  | i, false :: ds => d028 (i + 1) ds
  | i, true :: ds => d014 i + d028 (i + 1) ds

def d021 : List Bool → Nat
  | [] => 0
  | false :: ds => d021 ds
  | true :: ds => d021 ds + 1

def t066 : List Bool → Prop
  | [] => True
  | [_] => True
  | true :: true :: _ => False
  | _ :: ds => t066 ds

theorem t103 (i : Nat) (rest : List Bool) :
    d028 i (true :: true :: false :: rest) = d028 i (false :: false :: true :: rest) := by
  show d014 i + (d014 (i + 1) + d028 (i + 3) rest) = d014 (i + 2) + d028 (i + 3) rest
  rw [t113 i, ← t005, t004 (d014 i) (d014 (i + 1))]

theorem t102 (rest : List Bool) :
    d021 (true :: true :: false :: rest) = d021 (false :: false :: true :: rest) + 1 := rfl

/-- info: 'Foam.t103' does not depend on any axioms -/
#guard_msgs in #print axioms t103

/-- info: 'Foam.t102' does not depend on any axioms -/
#guard_msgs in #print axioms t102

end Foam
