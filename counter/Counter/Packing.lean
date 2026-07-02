import Counter.Third
import Counter.Nu

namespace Foam.Counter

theorem one_carrier_many_posts (A B : Type) :
    (∃ post : List (A ⊕ B) → List A,
        ∀ zs, ownFrames zs = post ((thirdSeat A B).obs zs ()))
      ∧ (∃ post : List (A ⊕ B) → List B,
        ∀ zs, ownFramesR zs = post ((thirdSeat A B).obs zs ()))
      ∧ (∃ post : List (A ⊕ B) → Option Bool,
        ∀ zs, whoActedFirst zs = post ((thirdSeat A B).obs zs ())) :=
  ⟨⟨ownFrames, fun _ => rfl⟩, ⟨ownFramesR, fun _ => rfl⟩,
   ⟨whoActedFirst, fun _ => rfl⟩⟩

variable {G : Type} [Mul G] [One G]

theorem actor_is_a_group_that_forgot_home (S : Seat G) :
    (∀ p : S.Pos, ∃ i : Iso S.Pos G, i.fwd p = 1)
      ∧ ∀ o o' : S.Pos, o ≠ o' →
          ∃ p, (S.chart o).fwd p ≠ (S.chart o').fwd p :=
  ⟨fun p => ⟨S.chart p, S.sub_self p⟩,
   fun o o' h => S.chart_origin_dependent o o' h⟩

theorem records_end_runs_continue (S : Seat G) (acts : Nat → G) (p : S.Pos)
    (l : List G) :
    (playback l).at_ l.length = none
      ∧ (guardedRun S acts p).at_ l.length
          = some (guardedStep S acts p l.length) :=
  ⟨nth_length l, rfl⟩

/-- info: 'Foam.Counter.one_carrier_many_posts' does not depend on any axioms -/
#guard_msgs in #print axioms one_carrier_many_posts

/-- info: 'Foam.Counter.actor_is_a_group_that_forgot_home' does not depend on any axioms -/
#guard_msgs in #print axioms actor_is_a_group_that_forgot_home

/-- info: 'Foam.Counter.records_end_runs_continue' does not depend on any axioms -/
#guard_msgs in #print axioms records_end_runs_continue

end Foam.Counter
