import Foam.Seat.Clock
import Foam.Platonism.Tower

namespace Foam

variable {G : Type} [Mul G] [One G]

theorem coord_forced (S : Seat G) (o : S.Pos) (p : S.Pos) :
    (S.chart o).bwd ((S.chart o).fwd p) = p :=
  (S.chart o).bwd_fwd p

theorem coord_linear (S : Seat G) (o : S.Pos) (g : G) (p : S.Pos) :
    (S.chart o).fwd (S.act g p) = g * (S.chart o).fwd p :=
  S.chart_equivariant g p o

theorem coord_gauge (S : Seat G) (o o' : S.Pos) (p : S.Pos) :
    (S.chart o).fwd p = (S.chart o').fwd p * S.sub o' o :=
  S.change_of_frame o o' p

theorem frame_not_canonical (S : Seat G) (o o' : S.Pos) (h : o ≠ o') :
    ∃ p, (S.chart o).fwd p ≠ (S.chart o').fwd p :=
  S.chart_origin_dependent o o' h

theorem coordinatization (S : Seat G) (o : S.Pos) :
    (∀ p, (S.chart o).bwd ((S.chart o).fwd p) = p)
      ∧ (∀ g p, (S.chart o).fwd (S.act g p) = g * (S.chart o).fwd p)
      ∧ (∀ o' p, (S.chart o).fwd p = (S.chart o').fwd p * S.sub o' o)
      ∧ (∀ o', o ≠ o' → ∃ p, (S.chart o).fwd p ≠ (S.chart o').fwd p) :=
  ⟨fun p => coord_forced S o p, fun g p => coord_linear S o g p,
   fun o' p => coord_gauge S o o' p, fun o' h => frame_not_canonical S o o' h⟩

theorem clock_coordinatized (o : clock.Pos) :
    (∀ p, (clock.chart o).bwd ((clock.chart o).fwd p) = p)
      ∧ (∀ g p, (clock.chart o).fwd (clock.act g p) = g * (clock.chart o).fwd p) :=
  ⟨fun p => coord_forced clock o p, fun g p => coord_linear clock o g p⟩

theorem dimension_caps_at_three : OpenChannels 3 ∧ ¬ OpenChannels 4 :=
  channels_saturate_past_three

/-- info: 'Foam.coord_forced' does not depend on any axioms -/
#guard_msgs in #print axioms coord_forced

/-- info: 'Foam.coord_linear' does not depend on any axioms -/
#guard_msgs in #print axioms coord_linear

/-- info: 'Foam.coord_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms coord_gauge

/-- info: 'Foam.frame_not_canonical' does not depend on any axioms -/
#guard_msgs in #print axioms frame_not_canonical

/-- info: 'Foam.coordinatization' does not depend on any axioms -/
#guard_msgs in #print axioms coordinatization

/-- info: 'Foam.clock_coordinatized' does not depend on any axioms -/
#guard_msgs in #print axioms clock_coordinatized

/-- info: 'Foam.dimension_caps_at_three' does not depend on any axioms -/
#guard_msgs in #print axioms dimension_caps_at_three

end Foam
