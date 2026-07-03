import Counter.Reparent
import Counter.Bubble
import Counter.Worn

namespace Foam.Counter

theorem the_self_moves_ballistically {G : Type} [Mul G] [One G]
    (S : Seat G) (xs ys : List G) (p : S.Pos) :
    S.replay (xs ++ ys) p = S.replay ys (S.replay xs p)
      ∧ ∀ h : List G, S.replay h p = S.act (netAct h) p :=
  history_is_portable S xs ys p

theorem information_moves_non_ballistically {A B : Type}
    {xs xs' : List A} {ys : List B} {zs zs' : List (A ⊕ B)}
    (h : Interleaves xs ys zs) (h' : Interleaves xs' ys zs') :
    ownFramesR zs = ownFramesR zs' :=
  other_view_unmoved h h'

theorem the_exit_from_now_is_conserved {G : Type} [Mul G] [One G]
    (S : Seat G) (p : S.Pos) :
    ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  mechanisms_wear_in S p

theorem the_glass_mobile_home {G : Type} [Mul G] [One G]
    (S : Seat G) (xs ys : List G) (p : S.Pos)
    {A : Type} {as as' : List A} {bs : List G} {zs zs' : List (A ⊕ G)}
    (h : Interleaves as bs zs) (h' : Interleaves as' bs zs') :
    (S.replay (xs ++ ys) p = S.replay ys (S.replay xs p))
      ∧ ownFramesR zs = ownFramesR zs'
      ∧ ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  ⟨(history_is_portable S xs ys p).1, other_view_unmoved h h',
   mechanisms_wear_in S p⟩

/-- info: 'Foam.Counter.the_self_moves_ballistically' does not depend on any axioms -/
#guard_msgs in #print axioms the_self_moves_ballistically

/-- info: 'Foam.Counter.information_moves_non_ballistically' does not depend on any axioms -/
#guard_msgs in #print axioms information_moves_non_ballistically

/-- info: 'Foam.Counter.the_exit_from_now_is_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms the_exit_from_now_is_conserved

/-- info: 'Foam.Counter.the_glass_mobile_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_glass_mobile_home

end Foam.Counter
