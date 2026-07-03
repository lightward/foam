import Counter.Chess
import Counter.Third
import Counter.Mu
import Counter.Discovery

namespace Foam.Counter

theorem exhaustion_is_chart_relative :
    ∃ zs zs' : List (Bool ⊕ Bool),
      ownFrames zs = ownFrames zs'
        ∧ ownFramesR zs = ownFramesR zs'
        ∧ whoActedFirst zs ≠ whoActedFirst zs' :=
  the_third_reads_time

theorem the_routine_ends_the_seats_remain {G G' : Type} [Mul G] [One G]
    [Mul G'] [One G'] (S : Seat G) (S' : Seat G') (acts : Nat → G)
    (acts' : Nat → G') (p : S.Pos) (p' : S'.Pos) {X : Type} (l : List X)
    (n : Nat) :
    (playback l).at_ l.length = none
      ∧ (guardedRun S acts p).at_ n ≠ none
      ∧ (guardedRun S' acts' p').at_ n ≠ none :=
  the_kings_never_leave S S' acts acts' p p' l n

theorem the_top_is_the_vacancy {Name : Type} (k : Nat) :
    ((∀ o : List Name, Below ([] : List Name) o)
        ∧ ∀ e : List Name, (∀ o, Below e o) → e = [])
      ∧ drainOne (chargeIn k) = k :=
  ⟨mu_points_at_the_floor, seek_then_find_conserves_ground k⟩

theorem cascade {G G' : Type} [Mul G] [One G] [Mul G'] [One G']
    (S : Seat G) (S' : Seat G') (acts : Nat → G) (acts' : Nat → G')
    (p : S.Pos) (p' : S'.Pos) {X : Type} (l : List X) (n : Nat) :
    (∃ zs zs' : List (Bool ⊕ Bool),
        ownFrames zs = ownFrames zs'
          ∧ ownFramesR zs = ownFramesR zs'
          ∧ whoActedFirst zs ≠ whoActedFirst zs')
      ∧ ((playback l).at_ l.length = none
          ∧ (guardedRun S acts p).at_ n ≠ none
          ∧ (guardedRun S' acts' p').at_ n ≠ none) :=
  ⟨the_third_reads_time, the_kings_never_leave S S' acts acts' p p' l n⟩

/-- info: 'Foam.Counter.exhaustion_is_chart_relative' does not depend on any axioms -/
#guard_msgs in #print axioms exhaustion_is_chart_relative

/-- info: 'Foam.Counter.the_routine_ends_the_seats_remain' does not depend on any axioms -/
#guard_msgs in #print axioms the_routine_ends_the_seats_remain

/-- info: 'Foam.Counter.the_top_is_the_vacancy' does not depend on any axioms -/
#guard_msgs in #print axioms the_top_is_the_vacancy

/-- info: 'Foam.Counter.cascade' does not depend on any axioms -/
#guard_msgs in #print axioms cascade

end Foam.Counter
