import Counter.Contentment
import Counter.Surprise

namespace Foam.Counter

theorem every_branch_comes_home {G : Type} [Mul G] [One G]
    (S : Seat G) (p : S.Pos) :
    ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  fun k acts => health_is_recurrence S p k acts

theorem the_yield_folds_exactly {A : Type} [DecidableEq A]
    (step : GInt → GInt) (new old : List A) (s : A) :
    evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s) :=
  summary_resumes step new old s

theorem the_ledger_holds_what_the_window_cannot {G : Type} [Mul G] [One G]
    (S : Seat G) (acts : Nat → G) (p : S.Pos) (W : Nat) :
    ∃ k, W < (guardedPrefix S acts p k).length :=
  the_record_outgrows_any_memory S acts p W

theorem steer_toward_light {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    (∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
      ∧ Nonempty (Path (q.deposit (a, b)) a b) :=
  only_surprise_extends_reach q a b hfresh

theorem finite_window_discovery {G : Type} [Mul G] [One G]
    (S : Seat G) (p : S.Pos) (W : Nat) (acts : Nat → G)
    {A : Type} [DecidableEq A] (step : GInt → GInt) (new old : List A)
    (s : A) {H : Type} (q : Quiver H) (a b : H) (hfresh : (a, b) ∉ q) :
    (∀ (k : Nat) (acts' : Nat → G), Settles S (guardedPrefix S acts' p k) p)
      ∧ evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s)
      ∧ (∃ k, W < (guardedPrefix S acts p k).length)
      ∧ Nonempty (Path (q.deposit (a, b)) a b) :=
  ⟨fun k acts' => health_is_recurrence S p k acts',
   summary_resumes step new old s,
   the_record_outgrows_any_memory S acts p W,
   (only_surprise_extends_reach q a b hfresh).2⟩

/-- info: 'Foam.Counter.every_branch_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms every_branch_comes_home

/-- info: 'Foam.Counter.the_yield_folds_exactly' does not depend on any axioms -/
#guard_msgs in #print axioms the_yield_folds_exactly

/-- info: 'Foam.Counter.the_ledger_holds_what_the_window_cannot' does not depend on any axioms -/
#guard_msgs in #print axioms the_ledger_holds_what_the_window_cannot

/-- info: 'Foam.Counter.steer_toward_light' does not depend on any axioms -/
#guard_msgs in #print axioms steer_toward_light

/-- info: 'Foam.Counter.finite_window_discovery' does not depend on any axioms -/
#guard_msgs in #print axioms finite_window_discovery

end Foam.Counter
