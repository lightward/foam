import Foam.Golden
import Foam.Int

namespace Foam

open Foam.FInt (addComm add_assoc)

def zval : Nat → List Bool → Int
  | _, [] => 0
  | i, false :: ds => zval (i + 1) ds
  | i, true :: ds => fib i + zval (i + 1) ds

def ones : List Bool → Nat
  | [] => 0
  | false :: ds => ones ds
  | true :: ds => ones ds + 1

def NoConsec : List Bool → Prop
  | [] => True
  | [_] => True
  | true :: true :: _ => False
  | _ :: ds => NoConsec ds

theorem carry_lossless (i : Nat) (rest : List Bool) :
    zval i (true :: true :: false :: rest) = zval i (false :: false :: true :: rest) := by
  show fib i + (fib (i + 1) + zval (i + 3) rest) = fib (i + 2) + zval (i + 3) rest
  rw [fib_gnomon i, ← add_assoc, addComm (fib i) (fib (i + 1))]

theorem carry_compresses (rest : List Bool) :
    ones (true :: true :: false :: rest) = ones (false :: false :: true :: rest) + 1 := rfl

/-- info: 'Foam.carry_lossless' does not depend on any axioms -/
#guard_msgs in #print axioms carry_lossless

/-- info: 'Foam.carry_compresses' does not depend on any axioms -/
#guard_msgs in #print axioms carry_compresses

end Foam
