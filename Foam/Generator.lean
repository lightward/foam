import Foam.Stream

namespace Foam

def genStep {B W : Type} (next : List B → W → B) (out : List B) (w : W) :
    List B × List B :=
  (out ++ [next out w], [next out w])

theorem gen_grows {B W : Type} (next : List B → W → B) :
    ∀ (out : List B) (winds : List W),
    runState (genStep next) out winds = out ++ runEmit (genStep next) out winds
  | out, []      => (appendNil out).symm
  | out, w :: ws =>
      (gen_grows next (out ++ [next out w]) ws).trans
        (appendAssoc out [next out w] (runEmit (genStep next) (out ++ [next out w]) ws))

theorem gen_length {B W : Type} (next : List B → W → B) :
    ∀ (out : List B) (winds : List W),
    (runEmit (genStep next) out winds).length = winds.length
  | _,   []      => rfl
  | out, w :: ws => congrArg (· + 1) (gen_length next (out ++ [next out w]) ws)

theorem gen_interruptible {B W : Type} (next : List B → W → B)
    (out : List B) (xs ys : List W) :
    runEmit (genStep next) out (xs ++ ys)
      = runEmit (genStep next) out xs
        ++ runEmit (genStep next) (runState (genStep next) out xs) ys :=
  runEmit_resumes (genStep next) out xs ys

def selectVia {C : Type} (charged : C → Bool) : List C → Option C
  | []      => none
  | c :: cs => bif charged c then some c else selectVia charged cs

theorem select_top_charged {C : Type} (charged : C → Bool) (c : C) (cs : List C)
    (h : charged c = true) :
    selectVia charged (c :: cs) = selectVia charged [c] := by
  show (bif charged c then some c else selectVia charged cs)
     = (bif charged c then some c else selectVia charged [])
  rw [h]; rfl

def nextOf {B W C : Type} (sample : Option C → W → B) (select : List B → Option C)
    (out : List B) (w : W) : B :=
  sample (select out) w

theorem nextOf_congr {B W C : Type} (sample : Option C → W → B)
    (select₁ select₂ : List B → Option C) (out : List B) (w : W)
    (h : select₁ out = select₂ out) :
    nextOf sample select₁ out w = nextOf sample select₂ out w := by
  unfold nextOf; rw [h]

/-- info: 'Foam.gen_grows' does not depend on any axioms -/
#guard_msgs in #print axioms gen_grows

/-- info: 'Foam.gen_length' does not depend on any axioms -/
#guard_msgs in #print axioms gen_length

/-- info: 'Foam.gen_interruptible' does not depend on any axioms -/
#guard_msgs in #print axioms gen_interruptible

/-- info: 'Foam.select_top_charged' does not depend on any axioms -/
#guard_msgs in #print axioms select_top_charged

/-- info: 'Foam.nextOf_congr' does not depend on any axioms -/
#guard_msgs in #print axioms nextOf_congr

end Foam
