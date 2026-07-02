import Counter.Third
import Counter.Bubble

namespace Foam.Counter

theorem observation_without_demand {A : Type} {H : Type} [Mul H] [One H]
    (S : Seat H) (p : S.Pos) {xs xs' : List A} {ys : List H}
    {zs zs' : List (A ⊕ H)}
    (h : Interleaves xs ys zs) (h' : Interleaves xs' ys zs') :
    (thirdSeat A H).Covers (pairSeat A H)
      ∧ (Settles S (ownFramesR zs) p ↔ Settles S (ownFramesR zs') p) :=
  ⟨third_covers_the_pair A H, no_cross_drain S p h h'⟩

/-- info: 'Foam.Counter.observation_without_demand' does not depend on any axioms -/
#guard_msgs in #print axioms observation_without_demand

end Foam.Counter
