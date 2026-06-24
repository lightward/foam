import Foam.Engine.Stream

namespace Foam

def d015 {B W : Type} (next : List B → W → B) (out : List B) (w : W) :
    List B × List B :=
  (out ++ [next out w], [next out w])

theorem t170 {B W : Type} (next : List B → W → B) :
    ∀ (out : List B) (winds : List W),
    d099 (d015 next) out winds = out ++ d026 (d015 next) out winds
  | out, []      => (t071 out).symm
  | out, w :: ws =>
      (t170 next (out ++ [next out w]) ws).trans
        (t070 out [next out w] (d026 (d015 next) (out ++ [next out w]) ws))

theorem t114 {B W : Type} (next : List B → W → B) :
    ∀ (out : List B) (winds : List W),
    (d026 (d015 next) out winds).length = winds.length
  | _,   []      => rfl
  | out, w :: ws => congrArg (· + 1) (t114 next (out ++ [next out w]) ws)

theorem t171 {B W : Type} (next : List B → W → B)
    (out : List B) (xs ys : List W) :
    d026 (d015 next) out (xs ++ ys)
      = d026 (d015 next) out xs
        ++ d026 (d015 next) (d099 (d015 next) out xs) ys :=
  t188 (d015 next) out xs ys

def d027 {C : Type} (charged : C → Bool) : List C → Option C
  | []      => none
  | c :: cs => bif charged c then some c else d027 charged cs

theorem t133 {C : Type} (charged : C → Bool) (c : C) (cs : List C)
    (h : charged c = true) :
    d027 charged (c :: cs) = d027 charged [c] := by
  show (bif charged c then some c else d027 charged cs)
     = (bif charged c then some c else d027 charged [])
  rw [h]; rfl

def d019 {B W C : Type} (sample : Option C → W → B) (select : List B → Option C)
    (out : List B) (w : W) : B :=
  sample (select out) w

theorem t123 {B W C : Type} (sample : Option C → W → B)
    (select₁ select₂ : List B → Option C) (out : List B) (w : W)
    (h : select₁ out = select₂ out) :
    d019 sample select₁ out w = d019 sample select₂ out w := by
  unfold d019; rw [h]

/-- info: 'Foam.t170' does not depend on any axioms -/
#guard_msgs in #print axioms t170

/-- info: 'Foam.t114' does not depend on any axioms -/
#guard_msgs in #print axioms t114

/-- info: 'Foam.t171' does not depend on any axioms -/
#guard_msgs in #print axioms t171

/-- info: 'Foam.t133' does not depend on any axioms -/
#guard_msgs in #print axioms t133

/-- info: 'Foam.t123' does not depend on any axioms -/
#guard_msgs in #print axioms t123

end Foam
