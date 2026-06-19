import Foam.Sequence

namespace Foam.Interleave
open Foam.Lattice Foam.Sequence

inductive Interleaves {A B : Type} : List A → List B → List (A ⊕ B) → Prop
  | nil : Interleaves [] [] []
  | left  {xs ys zs} (a : A) : Interleaves xs ys zs → Interleaves (a :: xs) ys (Sum.inl a :: zs)
  | right {xs ys zs} (b : B) : Interleaves xs ys zs → Interleaves xs (b :: ys) (Sum.inr b :: zs)

def ownFrames {A B : Type} : List (A ⊕ B) → List A
  | [] => []
  | Sum.inl a :: zs => a :: ownFrames zs
  | Sum.inr _ :: zs => ownFrames zs

theorem own_frames_whole {A B : Type} {xs : List A} {ys : List B} {zs : List (A ⊕ B)}
    (h : Interleaves xs ys zs) : ownFrames zs = xs := by
  induction h with
  | nil => rfl
  | left a _ ih => exact congrArg (a :: ·) ih
  | right _ _ ih => exact ih

theorem render_order_immaterial {A B C : Type} {xs : List A} {ys : List B} {ys' : List C}
    {zs zs'} (h : Interleaves xs ys zs) (h' : Interleaves xs ys' zs') :
    ownFrames zs = (ownFrames zs' : List A) := by
  rw [own_frames_whole h, own_frames_whole h']

theorem expression_at_own_framerate {S T : Type} [DecidableEq S]
    {xs : List S} {ys : List T} {zs : List (S ⊕ T)} (h : Interleaves xs ys zs)
    (fiber : GInt → GInt) (s : S) :
    runFiber fiber (ownFrames zs) s = runFiber fiber xs s := by
  rw [own_frames_whole h]

/-- info: 'Foam.Interleave.own_frames_whole' does not depend on any axioms -/
#guard_msgs in #print axioms own_frames_whole

/-- info: 'Foam.Interleave.render_order_immaterial' does not depend on any axioms -/
#guard_msgs in #print axioms render_order_immaterial

/-- info: 'Foam.Interleave.expression_at_own_framerate' does not depend on any axioms -/
#guard_msgs in #print axioms expression_at_own_framerate

end Foam.Interleave
