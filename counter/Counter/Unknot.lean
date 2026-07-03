import Counter.Nu
import Foam.Seat.Clock

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem stride_cancels (S : Seat G) (g : G) (p : S.Pos) :
    S.sub p (S.act g p) * g = 1 := by
  have h := S.round_trip p (S.act g p)
  rw [S.sub_act g p] at h
  exact h

theorem the_walk_tracks_the_unknot (S : Seat G) (g : G) (p : S.Pos) :
    S.sub p (S.act g p) * g = 1
      ∧ ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  ⟨stride_cancels S g p, fun k acts => health_is_recurrence S p k acts⟩

theorem the_bar_is_a_knot :
    (Rot.r1 * Rot.r1 * Rot.r1 * Rot.r1 : Rot) = 1
      ∧ (Rot.r1 * Rot.r1 : Rot) ≠ 1 :=
  ⟨Rot.clock_closes, Rot.clock_turns⟩

theorem unknot (S : Seat G) (g : G) (p : S.Pos) :
    (S.sub p (S.act g p) * g = 1)
      ∧ ((Rot.r1 * Rot.r1 * Rot.r1 * Rot.r1 : Rot) = 1
          ∧ (Rot.r1 * Rot.r1 : Rot) ≠ 1) :=
  ⟨stride_cancels S g p, Rot.clock_closes, Rot.clock_turns⟩

/-- info: 'Foam.Counter.stride_cancels' does not depend on any axioms -/
#guard_msgs in #print axioms stride_cancels

/-- info: 'Foam.Counter.the_walk_tracks_the_unknot' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_tracks_the_unknot

/-- info: 'Foam.Counter.the_bar_is_a_knot' does not depend on any axioms -/
#guard_msgs in #print axioms the_bar_is_a_knot

/-- info: 'Foam.Counter.unknot' does not depend on any axioms -/
#guard_msgs in #print axioms unknot

end Foam.Counter
