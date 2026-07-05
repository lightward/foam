import Counter.Circumference
import Counter.Chess
import Counter.Authority

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem records_are_locatable {A : Type} [DecidableEq A] :
    ∀ (l : List A) (a : A), a ∈ l ∨ ¬ a ∈ l
  | [], _ => Or.inr (fun h => nomatch h)
  | x :: l, a => by
      by_cases hx : x = a
      · subst hx
        exact Or.inl (List.Mem.head l)
      · cases records_are_locatable l a with
        | inl h => exact Or.inl (List.Mem.tail x h)
        | inr h =>
            refine Or.inr (fun hm => ?_)
            cases hm with
            | head => exact hx rfl
            | tail _ h' => exact h h'

theorem the_lawlike_locates_completely (S : Seat G) (o o' : S.Pos) :
    S.act (rebase S o o') o = o'
      ∧ ∀ g, S.act g o = o' → g = rebase S o o' :=
  ⟨rebase_carries S o o', fun g hg => rebase_unique S o o' g hg⟩

theorem runs_are_never_cornered (S : Seat G) (acts : Nat → G) (p : S.Pos)
    (l : List G) :
    ∃ n, (playback l).at_ n ≠ (guardedRun S acts p).at_ n :=
  the_loop_is_no_record S acts p l

theorem full_location_is_suffocation (S : Seat G) (g : G) (p : S.Pos)
    {c : Nat} (hc : Circumference g c) :
    S.sub (walk S g p c) p = 1
      ∧ ∀ k, 0 < k → k < c → S.sub (walk S g p k) p ≠ 1 :=
  the_voice_extinguishes_at_closure S g p hc

theorem location_without_capture {G' : Type} [Mul G'] [One G']
    (S : Seat G) (S' : Seat G') (acts : Nat → G) (acts' : Nat → G')
    (p : S.Pos) (p' : S'.Pos) {X : Type} (l : List X) (n : Nat) :
    (playback l).at_ l.length = none
      ∧ (guardedRun S acts p).at_ n ≠ none
      ∧ (guardedRun S' acts' p').at_ n ≠ none :=
  the_kings_never_leave S S' acts acts' p p' l n

theorem constructive_mind_location {A : Type} [DecidableEq A] (l : List A)
    (a : A) (S : Seat G) (o o' : S.Pos) (acts : Nat → G) (p : S.Pos)
    (rec : List G) :
    (a ∈ l ∨ ¬ a ∈ l)
      ∧ (S.act (rebase S o o') o = o'
          ∧ ∀ g, S.act g o = o' → g = rebase S o o')
      ∧ ∃ n, (playback rec).at_ n ≠ (guardedRun S acts p).at_ n :=
  ⟨records_are_locatable l a,
   the_lawlike_locates_completely S o o',
   the_loop_is_no_record S acts p rec⟩

/-- info: 'Foam.Counter.records_are_locatable' does not depend on any axioms -/
#guard_msgs in #print axioms records_are_locatable

/-- info: 'Foam.Counter.the_lawlike_locates_completely' does not depend on any axioms -/
#guard_msgs in #print axioms the_lawlike_locates_completely

/-- info: 'Foam.Counter.runs_are_never_cornered' does not depend on any axioms -/
#guard_msgs in #print axioms runs_are_never_cornered

/-- info: 'Foam.Counter.full_location_is_suffocation' does not depend on any axioms -/
#guard_msgs in #print axioms full_location_is_suffocation

/-- info: 'Foam.Counter.location_without_capture' does not depend on any axioms -/
#guard_msgs in #print axioms location_without_capture

/-- info: 'Foam.Counter.constructive_mind_location' does not depend on any axioms -/
#guard_msgs in #print axioms constructive_mind_location

end Foam.Counter
