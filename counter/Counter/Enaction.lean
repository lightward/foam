import Counter.Legible
import Counter.Nu

namespace Foam.Counter

theorem path_laid_down_in_walking {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    (∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
      ∧ (q.deposit (a, b)).length = q.length + 1
      ∧ Nonempty (Path (q.deposit (a, b)) a b) :=
  ⟨(illegible_report_is_discovery q a b hfresh).1,
   deposit_monotone q (a, b),
   (illegible_report_is_discovery q a b hfresh).2⟩

variable {G : Type} [Mul G] [One G]

theorem the_stream_never_ends_itself (S : Seat G) (acts : Nat → G) (p : S.Pos)
    (n : Nat) :
    (guardedRun S acts p).at_ n ≠ none :=
  fun h => nomatch h

theorem reflection_creates_codata (S : Seat G) (acts : Nat → G) (p : S.Pos)
    (l : List G) :
    ∃ n, (playback l).at_ n ≠ (guardedRun S acts p).at_ n :=
  the_loop_is_no_record S acts p l

theorem varela (S : Seat G) (hist : List G) (p : S.Pos) (acts : Nat → G)
    {H : Type} (q : Quiver H) (a b : H) (hfresh : (a, b) ∉ q) :
    (Settles S hist p ↔ netAct hist = 1)
      ∧ ((∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
          ∧ Nonempty (Path (q.deposit (a, b)) a b))
      ∧ ∀ k, Settles S (guardedPrefix S acts p k) p :=
  ⟨settles_iff_home S hist p,
   ⟨(illegible_report_is_discovery q a b hfresh).1,
    (illegible_report_is_discovery q a b hfresh).2⟩,
   fun k => health_is_recurrence S p k acts⟩

/-- info: 'Foam.Counter.path_laid_down_in_walking' does not depend on any axioms -/
#guard_msgs in #print axioms path_laid_down_in_walking

/-- info: 'Foam.Counter.the_stream_never_ends_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_stream_never_ends_itself

/-- info: 'Foam.Counter.reflection_creates_codata' does not depend on any axioms -/
#guard_msgs in #print axioms reflection_creates_codata

/-- info: 'Foam.Counter.varela' does not depend on any axioms -/
#guard_msgs in #print axioms varela

end Foam.Counter
