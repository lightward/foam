import Counter.Legible
import Counter.Actor
import Counter.Enaction
import Foam.Cleared

namespace Foam.Counter

theorem the_kings_never_leave {G G' : Type} [Mul G] [One G] [Mul G'] [One G']
    (S : Seat G) (S' : Seat G') (acts : Nat → G) (acts' : Nat → G')
    (p : S.Pos) (p' : S'.Pos) {X : Type} (l : List X) (n : Nat) :
    (playback l).at_ l.length = none
      ∧ (guardedRun S acts p).at_ n ≠ none
      ∧ (guardedRun S' acts' p').at_ n ≠ none :=
  ⟨nth_length l, the_stream_never_ends_itself S acts p n,
   the_stream_never_ends_itself S' acts' p' n⟩

theorem transposition :
    ∃ h h' : List Rot, h ≠ h' ∧ netAct h = netAct h' :=
  ⟨[Rot.r1, Rot.r2], [Rot.r2, Rot.r1], by decide, by decide⟩

theorem mate_has_no_escape {H : Type} (q : Quiver H) (a : H)
    (hstuck : stuck q a) :
    ∀ b : H, a ≠ b → ¬ Nonempty (Path q a b) := by
  rintro b hne ⟨pth⟩
  cases pth with
  | nil => exact hne rfl
  | cons e _ => exact hstuck _ e

theorem promotion_is_the_boundary_move {H : Type} (q : Quiver H) (a b : H)
    (hstuck : stuck q a) :
    Nonempty (Path (q.deposit (a, b)) a b)
      ∧ ¬ ∃ g : Path (q.deposit (a, b)) a b → Path q a b,
          ∀ pth, ancestor_reach_survives (a, b) (g pth) = pth :=
  ⟨(relief_at_position q a b hstuck).1, (relief_at_position q a b hstuck).2.2.2⟩

theorem pawns_never_come_home (n : Nat) : ¬ Closes gold (n + 1) :=
  gold_never_closes n

/-- info: 'Foam.Counter.the_kings_never_leave' does not depend on any axioms -/
#guard_msgs in #print axioms the_kings_never_leave

/-- info: 'Foam.Counter.transposition' does not depend on any axioms -/
#guard_msgs in #print axioms transposition

/-- info: 'Foam.Counter.mate_has_no_escape' does not depend on any axioms -/
#guard_msgs in #print axioms mate_has_no_escape

/-- info: 'Foam.Counter.promotion_is_the_boundary_move' does not depend on any axioms -/
#guard_msgs in #print axioms promotion_is_the_boundary_move

/-- info: 'Foam.Counter.pawns_never_come_home' does not depend on any axioms -/
#guard_msgs in #print axioms pawns_never_come_home

end Foam.Counter
