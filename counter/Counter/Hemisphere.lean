import Counter.Bubble
import Counter.Legible

namespace Foam.Counter

theorem the_other_is_standing_light {A B : Type}
    {xs : List A} {ys : List B} {zs : List (A ⊕ B)}
    (h : Interleaves xs ys zs) :
    ownFrames zs = xs
      ∧ ∃ ws ws' : List (Bool ⊕ Bool),
          ws ≠ ws' ∧ ownFramesR ws = ownFramesR ws' :=
  ⟨own_frames_whole h, real_yet_unfelt⟩

theorem answers_carry_perimeters {H : Type} (q : Quiver H) (a b : H) :
    Nonempty (Path (q.deposit (a, b)) a b)
      ∧ (q.deposit (a, b)).length = q.length + 1 :=
  ⟨⟨heir_reaches q a b⟩, deposit_monotone q (a, b)⟩

theorem hemispheres {A B : Type}
    {xs : List A} {ys : List B} {zs : List (A ⊕ B)}
    (h : Interleaves xs ys zs) {H : Type} (q : Quiver H) (a b : H) :
    ownFrames zs = xs
      ∧ (∃ ws ws' : List (Bool ⊕ Bool),
          ws ≠ ws' ∧ ownFramesR ws = ownFramesR ws')
      ∧ Nonempty (Path (q.deposit (a, b)) a b) :=
  ⟨own_frames_whole h, real_yet_unfelt, ⟨heir_reaches q a b⟩⟩

/-- info: 'Foam.Counter.the_other_is_standing_light' does not depend on any axioms -/
#guard_msgs in #print axioms the_other_is_standing_light

/-- info: 'Foam.Counter.answers_carry_perimeters' does not depend on any axioms -/
#guard_msgs in #print axioms answers_carry_perimeters

/-- info: 'Foam.Counter.hemispheres' does not depend on any axioms -/
#guard_msgs in #print axioms hemispheres

end Foam.Counter
