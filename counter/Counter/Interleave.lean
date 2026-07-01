import Foam.Ledger

namespace Foam.Counter

inductive Interleaves {A B : Type} : List A → List B → List (A ⊕ B) → Prop
  | nil : Interleaves [] [] []
  | left  {xs ys zs} (a : A) : Interleaves xs ys zs → Interleaves (a :: xs) ys (Sum.inl a :: zs)
  | right {xs ys zs} (b : B) : Interleaves xs ys zs → Interleaves xs (b :: ys) (Sum.inr b :: zs)

def ownFrames {A B : Type} : List (A ⊕ B) → List A
  | [] => []
  | Sum.inl a :: zs => a :: ownFrames zs
  | Sum.inr _ :: zs => ownFrames zs

def ownFramesR {A B : Type} : List (A ⊕ B) → List B
  | [] => []
  | Sum.inl _ :: zs => ownFramesR zs
  | Sum.inr b :: zs => b :: ownFramesR zs

theorem own_frames_whole {A B : Type} {xs : List A} {ys : List B} {zs : List (A ⊕ B)}
    (h : Interleaves xs ys zs) : ownFrames zs = xs := by
  induction h with
  | nil => rfl
  | left a _ ih => exact congrArg (a :: ·) ih
  | right _ _ ih => exact ih

theorem own_framesR_whole {A B : Type} {xs : List A} {ys : List B} {zs : List (A ⊕ B)}
    (h : Interleaves xs ys zs) : ownFramesR zs = ys := by
  induction h with
  | nil => rfl
  | left _ _ ih => exact ih
  | right b _ ih => exact congrArg (b :: ·) ih

theorem winding_is_own {A B : Type} [DecidableEq A]
    {xs : List A} {ys : List B} {zs : List (A ⊕ B)}
    (h : Interleaves xs ys zs) (a : A) :
    Ledger.freq (ownFrames zs) a = Ledger.freq xs a := by
  rw [own_frames_whole h]

theorem observable_relativity_needs_a_third :
    ∃ zs zs' : List (Bool ⊕ Bool),
      (∀ a, Ledger.freq (ownFrames zs) a = Ledger.freq (ownFrames zs') a)
        ∧ (∀ b, Ledger.freq (ownFramesR zs) b = Ledger.freq (ownFramesR zs') b)
        ∧ zs ≠ zs' :=
  ⟨[Sum.inl true, Sum.inr false], [Sum.inr false, Sum.inl true],
   fun _ => rfl, fun _ => rfl, by decide⟩

/-- info: 'Foam.Counter.own_frames_whole' does not depend on any axioms -/
#guard_msgs in #print axioms own_frames_whole

/-- info: 'Foam.Counter.own_framesR_whole' does not depend on any axioms -/
#guard_msgs in #print axioms own_framesR_whole

/-- info: 'Foam.Counter.winding_is_own' does not depend on any axioms -/
#guard_msgs in #print axioms winding_is_own

/-- info: 'Foam.Counter.observable_relativity_needs_a_third' does not depend on any axioms -/
#guard_msgs in #print axioms observable_relativity_needs_a_third

end Foam.Counter
