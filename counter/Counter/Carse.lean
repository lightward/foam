import Counter.Enaction

namespace Foam.Counter

theorem carse {X : Type} (l : List X) {G : Type} [Mul G] [One G]
    (S : Seat G) (acts : Nat → G) (p : S.Pos) (n : Nat)
    {H : Type} (q : Quiver H) (e : H × H) :
    (playback l).at_ l.length = none
      ∧ (guardedRun S acts p).at_ n ≠ none
      ∧ (q.deposit e).length = q.length + 1 :=
  ⟨nth_length l, the_stream_never_ends_itself S acts p n, deposit_monotone q e⟩

/-- info: 'Foam.Counter.carse' does not depend on any axioms -/
#guard_msgs in #print axioms carse

end Foam.Counter
