import Foam.Engine.Generator

namespace Foam

theorem t119 {B W C : Type} (sample : Option C → W → B)
    (select₁ select₂ : List B → Option C) (out : List B) (w : W)
    (h : select₁ out = select₂ out) :
    d019 sample select₁ out w = d019 sample select₂ out w :=
  t123 sample select₁ select₂ out w h

theorem t180 {B W : Type} (next : List B → W → B)
    (out : List B) (winds : List W) :
    d099 (d015 next) out winds = out ++ d026 (d015 next) out winds :=
  t170 next out winds

theorem t179 {B W : Type} (next : List B → W → B)
    (out : List B) (xs ys : List W) :
    d026 (d015 next) out (xs ++ ys)
      = d026 (d015 next) out xs
        ++ d026 (d015 next) (d099 (d015 next) out xs) ys :=
  t171 next out xs ys

/-- info: 'Foam.t119' does not depend on any axioms -/
#guard_msgs in #print axioms t119

/-- info: 'Foam.t180' does not depend on any axioms -/
#guard_msgs in #print axioms t180

/-- info: 'Foam.t179' does not depend on any axioms -/
#guard_msgs in #print axioms t179

end Foam
