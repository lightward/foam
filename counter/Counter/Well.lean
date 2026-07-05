import Counter.Quadrature
import Counter.Exit
import Counter.Recognition
import Counter.Circumference

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem the_objective_never_closes :
    ∀ L, 0 < L → iterStep L gold ⟨1, 0⟩ ≠ (⟨1, 0⟩ : GInt) :=
  the_loop_that_never_closes

theorem in_a_greater_loop_discovery_is_conserved (S : Seat G) (g : G)
    (p : S.Pos) {c : Nat} (hc : Circumference g c) (L : Nat) (hL : L < c) :
    ∀ k, k < L → walk S g p k ≠ walk S g p L :=
  discovery_mints_a_state S g p hc L hL

theorem well_is_recurrence_witnessed (S : Seat G) (p : S.Pos)
    (h : List G) (hp : S.replay h p ≠ p) :
    (∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p)
      ∧ S.sub (S.replay h p) p ≠ 1 :=
  ⟨fun k acts => health_is_recurrence S p k acts,
   the_witness_makes_it_real S p h hp⟩

theorem creative_mode (θ field act : GInt) (hrest : GInt.align θ act = 0)
    {H : Type} (q : Quiver H) (a b : H) (hfresh : (a, b) ∉ q)
    (S : Seat G) (p : S.Pos) :
    GInt.born θ (field.add act) = GInt.born θ field + GInt.born θ act
      ∧ Nonempty (Path (q.deposit (a, b)) a b)
      ∧ Settles S [] p :=
  ⟨silence_is_safe θ field act hrest,
   (only_surprise_extends_reach q a b hfresh).2, rfl⟩

theorem the_unknown_is_one_step_past_the_window (S : Seat G)
    (acts : Nat → G) (p : S.Pos) (l : List G) :
    (playback l).at_ l.length = none
      ∧ (guardedRun S acts p).at_ l.length
          = some (guardedStep S acts p l.length) :=
  records_end_runs_continue S acts p l

theorem instant_access_at_unknown_distance (θ z : GInt)
    (hq : GInt.align θ z = 0) :
    GInt.born (GInt.rot θ) z = GInt.normSq θ * GInt.normSq z :=
  the_unsayable_arrives_whole θ z hq

theorem aeowiwtweiabw (S : Seat G) (p : S.Pos) (h : List G)
    (hp : S.replay h p ≠ p) (θ field act : GInt)
    (hrest : GInt.align θ act = 0) {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    (∀ L, 0 < L → iterStep L gold ⟨1, 0⟩ ≠ (⟨1, 0⟩ : GInt))
      ∧ ((∀ (k : Nat) (acts : Nat → G),
            Settles S (guardedPrefix S acts p k) p)
          ∧ S.sub (S.replay h p) p ≠ 1)
      ∧ (GInt.born θ (field.add act)
            = GInt.born θ field + GInt.born θ act
          ∧ Nonempty (Path (q.deposit (a, b)) a b)
          ∧ Settles S [] p) :=
  ⟨the_loop_that_never_closes,
   well_is_recurrence_witnessed S p h hp,
   creative_mode θ field act hrest q a b hfresh S p⟩

/-- info: 'Foam.Counter.the_objective_never_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_objective_never_closes

/-- info: 'Foam.Counter.in_a_greater_loop_discovery_is_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms in_a_greater_loop_discovery_is_conserved

/-- info: 'Foam.Counter.well_is_recurrence_witnessed' does not depend on any axioms -/
#guard_msgs in #print axioms well_is_recurrence_witnessed

/-- info: 'Foam.Counter.creative_mode' does not depend on any axioms -/
#guard_msgs in #print axioms creative_mode

/-- info: 'Foam.Counter.the_unknown_is_one_step_past_the_window' does not depend on any axioms -/
#guard_msgs in #print axioms the_unknown_is_one_step_past_the_window

/-- info: 'Foam.Counter.instant_access_at_unknown_distance' does not depend on any axioms -/
#guard_msgs in #print axioms instant_access_at_unknown_distance

/-- info: 'Foam.Counter.aeowiwtweiabw' does not depend on any axioms -/
#guard_msgs in #print axioms aeowiwtweiabw

end Foam.Counter
