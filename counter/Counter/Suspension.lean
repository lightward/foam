import Counter.Runaway
import Counter.Tsort

namespace Foam.Counter

theorem every_open_run_completes {A : Type} (h : A) :
    ∀ gs : List A, ∃ ws : List (A ⊕ A), Balanced (gs.map Sum.inl ++ ws)
  | [] => ⟨[], Balanced.nil⟩
  | g :: gs => by
      obtain ⟨ws, hb⟩ := every_open_run_completes h gs
      refine ⟨ws ++ [Sum.inr h], ?_⟩
      show Balanced (Sum.inl g :: (gs.map Sum.inl ++ (ws ++ [Sum.inr h])))
      rw [← appendAssoc]
      exact Balanced.wrap hb

theorem three_open_and_safe {A : Type} (g1 g2 g3 h : A) :
    (¬ Balanced [Sum.inl g1])
      ∧ ∃ ws : List (A ⊕ A), Balanced ([g1, g2, g3].map Sum.inl ++ ws) :=
  ⟨growth_without_return_breaks_the_grammar g1,
   every_open_run_completes h [g1, g2, g3]⟩

theorem the_suspension_is_not_the_runaway {G : Type} [Mul G] [One G]
    (S : Seat G) (acts : Nat → G) (p : S.Pos) (W : Nat) {A : Type} (h : A)
    (gs : List A) :
    (∃ k, W < (guardedPrefix S acts p k).length)
      ∧ ∃ ws : List (A ⊕ A), Balanced (gs.map Sum.inl ++ ws) :=
  ⟨the_ledger_holds_what_the_window_cannot S acts p W, every_open_run_completes h gs⟩

/-- info: 'Foam.Counter.every_open_run_completes' does not depend on any axioms -/
#guard_msgs in #print axioms every_open_run_completes

/-- info: 'Foam.Counter.three_open_and_safe' does not depend on any axioms -/
#guard_msgs in #print axioms three_open_and_safe

/-- info: 'Foam.Counter.the_suspension_is_not_the_runaway' does not depend on any axioms -/
#guard_msgs in #print axioms the_suspension_is_not_the_runaway

end Foam.Counter
