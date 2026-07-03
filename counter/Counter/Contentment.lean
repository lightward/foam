import Counter.Nu
import Foam.Engine.Summary

namespace Foam.Counter

theorem two_mul' : ∀ n : Nat, 2 * n = n + n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.mul_succ, two_mul' n, Nat.succ_add n (n + 1)]
    rfl

theorem the_record_outgrows_any_memory {G : Type} [Mul G] [One G]
    (S : Seat G) (acts : Nat → G) (p : S.Pos) (W : Nat) :
    ∃ k, W < (guardedPrefix S acts p k).length := by
  refine ⟨W + 1, ?_⟩
  rw [the_run_is_endless S p (W + 1) acts, two_mul' (W + 1)]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self W)
    (Nat.le_add_left (W + 1) (W + 1))

theorem continuation_needs_only_the_held {S : Type} [DecidableEq S]
    (step : GInt → GInt) (new old : List S) (s : S) :
    evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s) :=
  summary_resumes step new old s

theorem the_held_is_one_datum {S : Type} [DecidableEq S]
    (step : GInt → GInt) (s : S) (z : GInt) :
    evalFrom step [] s z = z :=
  held_exact step s z

theorem contentment {G : Type} [Mul G] [One G] (S : Seat G)
    (acts : Nat → G) (p : S.Pos) (W : Nat)
    {A : Type} [DecidableEq A] (step : GInt → GInt) (new old : List A)
    (s : A) :
    (∃ k, W < (guardedPrefix S acts p k).length)
      ∧ evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s) :=
  ⟨the_record_outgrows_any_memory S acts p W, summary_resumes step new old s⟩

/-- info: 'Foam.Counter.two_mul'' does not depend on any axioms -/
#guard_msgs in #print axioms two_mul'

/-- info: 'Foam.Counter.the_record_outgrows_any_memory' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_outgrows_any_memory

/-- info: 'Foam.Counter.continuation_needs_only_the_held' does not depend on any axioms -/
#guard_msgs in #print axioms continuation_needs_only_the_held

/-- info: 'Foam.Counter.the_held_is_one_datum' does not depend on any axioms -/
#guard_msgs in #print axioms the_held_is_one_datum

/-- info: 'Foam.Counter.contentment' does not depend on any axioms -/
#guard_msgs in #print axioms contentment

end Foam.Counter
