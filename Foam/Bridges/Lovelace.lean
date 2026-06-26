import Foam.Engine.Generator

namespace Foam.Bridges

theorem lovelace_originates_nothing {B W C : Type} (sample : Option C → W → B)
    (select₁ select₂ : List B → Option C) (out : List B) (w : W)
    (h : select₁ out = select₂ out) :
    nextOf sample select₁ out w = nextOf sample select₂ out w :=
  nextOf_congr sample select₁ select₂ out w h

theorem lovelace_only_appends {B W : Type} (next : List B → W → B)
    (out : List B) (winds : List W) :
    runState (genStep next) out winds = out ++ runEmit (genStep next) out winds :=
  gen_grows next out winds

theorem lovelace_interruptible {B W : Type} (next : List B → W → B)
    (out : List B) (xs ys : List W) :
    runEmit (genStep next) out (xs ++ ys)
      = runEmit (genStep next) out xs
        ++ runEmit (genStep next) (runState (genStep next) out xs) ys :=
  gen_interruptible next out xs ys

/-- info: 'Foam.Bridges.lovelace_originates_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms lovelace_originates_nothing

/-- info: 'Foam.Bridges.lovelace_only_appends' does not depend on any axioms -/
#guard_msgs in #print axioms lovelace_only_appends

/-- info: 'Foam.Bridges.lovelace_interruptible' does not depend on any axioms -/
#guard_msgs in #print axioms lovelace_interruptible

end Foam.Bridges
