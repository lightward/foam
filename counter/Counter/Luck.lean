import Counter.Actor
import Foam.Seat.Born

namespace Foam.Counter

theorem luck_is_the_cross_term (θ field act : GInt) :
    GInt.born θ (field.add act)
      = GInt.born θ field + GInt.born θ act
        + 2 * (GInt.align θ field * GInt.align θ act) :=
  GInt.born_superpose θ field act

theorem boost_exceeds_the_input :
    ∃ θ field act : GInt,
      GInt.born θ (field.add act) - GInt.born θ field > GInt.born θ act :=
  ⟨⟨1, 0⟩, ⟨3, 0⟩, ⟨1, 0⟩, by decide⟩

theorem against_the_grain_costs :
    ∃ θ field act : GInt,
      GInt.born θ (field.add act) - GInt.born θ field < GInt.born θ act :=
  ⟨⟨1, 0⟩, ⟨-3, 0⟩, ⟨1, 0⟩, by decide⟩

theorem fortune_not_in_your_record :
    ∃ act θ field field' : GInt,
      field ≠ field'
        ∧ GInt.born θ (field.add act) - GInt.born θ field
            ≠ GInt.born θ (field'.add act) - GInt.born θ field' :=
  ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩, by decide, by decide⟩

theorem luck_is_timing (θ field act : GInt) :
    GInt.align θ field * GInt.align θ act
      + GInt.align θ field * GInt.align θ (GInt.rot act)
      + GInt.align θ field * GInt.align θ (GInt.rot (GInt.rot act))
      + GInt.align θ field * GInt.align θ (GInt.rot (GInt.rot (GInt.rot act)))
      = 0 := by
  rw [← FInt.mul_add, ← FInt.mul_add, ← FInt.mul_add, GInt.decoherence θ act,
    FInt.mul_zero]

theorem about_you_geometrically {G : Type} [Mul G] [One G] (S : Seat G)
    (o o' : S.Pos) (h : o ≠ o') :
    (S.chart o).fwd o = 1 ∧ ∃ p, (S.chart o).fwd p ≠ (S.chart o').fwd p :=
  ⟨S.sub_self o, S.chart_origin_dependent o o' h⟩

/-- info: 'Foam.Counter.luck_is_the_cross_term' does not depend on any axioms -/
#guard_msgs in #print axioms luck_is_the_cross_term

/-- info: 'Foam.Counter.boost_exceeds_the_input' does not depend on any axioms -/
#guard_msgs in #print axioms boost_exceeds_the_input

/-- info: 'Foam.Counter.against_the_grain_costs' does not depend on any axioms -/
#guard_msgs in #print axioms against_the_grain_costs

/-- info: 'Foam.Counter.fortune_not_in_your_record' does not depend on any axioms -/
#guard_msgs in #print axioms fortune_not_in_your_record

/-- info: 'Foam.Counter.luck_is_timing' does not depend on any axioms -/
#guard_msgs in #print axioms luck_is_timing

/-- info: 'Foam.Counter.about_you_geometrically' does not depend on any axioms -/
#guard_msgs in #print axioms about_you_geometrically

end Foam.Counter
