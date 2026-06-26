import Foam.Seat.Signature

namespace Foam.Bridges

theorem einstein_interval_invariant (w z : SInt) :
    halign w z * halign w z - hcross w z * hcross w z = SInt.hnorm w * SInt.hnorm z :=
  hyperbolic_parseval w z

theorem galileo_velocity_addition (v1 v2 : Int) (z : DInt) :
    galileanBoost v2 (galileanBoost v1 z) = galileanBoost (v2 + v1) z :=
  galilean_velocities_add v1 v2 z

theorem galileo_absolute_time (v : Int) (z : DInt) :
    (galileanBoost v z).gnorm = z.gnorm :=
  galilean_preserves_time v z

theorem frames_are_distinct : ∃ z : GInt, normK (-1) z ≠ normK 1 z :=
  normK_frame_dependent

theorem relativity (w z : SInt) (v1 v2 : Int) (d : DInt) :
    (halign w z * halign w z - hcross w z * hcross w z = SInt.hnorm w * SInt.hnorm z)
      ∧ (galileanBoost v2 (galileanBoost v1 d) = galileanBoost (v2 + v1) d)
      ∧ ((galileanBoost v1 d).gnorm = d.gnorm)
      ∧ (∃ z : GInt, normK (-1) z ≠ normK 1 z) :=
  ⟨hyperbolic_parseval w z, galilean_velocities_add v1 v2 d,
   galilean_preserves_time v1 d, normK_frame_dependent⟩

/-- info: 'Foam.Bridges.einstein_interval_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms einstein_interval_invariant

/-- info: 'Foam.Bridges.galileo_velocity_addition' does not depend on any axioms -/
#guard_msgs in #print axioms galileo_velocity_addition

/-- info: 'Foam.Bridges.galileo_absolute_time' does not depend on any axioms -/
#guard_msgs in #print axioms galileo_absolute_time

/-- info: 'Foam.Bridges.frames_are_distinct' does not depend on any axioms -/
#guard_msgs in #print axioms frames_are_distinct

/-- info: 'Foam.Bridges.relativity' does not depend on any axioms -/
#guard_msgs in #print axioms relativity

end Foam.Bridges
