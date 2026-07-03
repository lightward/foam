import Counter.Actor
import Foam.Engine.Spectrum
import Foam.Seat.Signed

namespace Foam.Counter

theorem recession_is_felt :
    evalBeats GInt.rot [some true] true ≠ evalBeats GInt.rot [none, some true] true :=
  rest_audible

theorem three_recessions_carry :
    evalBeats GInt.rot [none, none, none, some true] true ≠ GInt.zero := by
  decide

theorem the_fourth_closes_the_bar {S : Type} [DecidableEq S]
    (l : List (Option S)) (s : S) :
    evalBeats GInt.rot (none :: none :: none :: none :: l) s = evalBeats GInt.rot l s :=
  bar_invisible l s

theorem guarded_recession_renews :
    evalBeats GInt.rot
      [none, none, none, some true, none, none, none, some true] true
      ≠ GInt.zero := by
  decide

theorem mu_points_at_the_floor {Name : Type} :
    (∀ o : List Name, Below ([] : List Name) o)
      ∧ ∀ e : List Name, (∀ o, Below e o) → e = [] :=
  ⟨wind_below_all, only_wind_is_floor⟩

/-- info: 'Foam.Counter.recession_is_felt' does not depend on any axioms -/
#guard_msgs in #print axioms recession_is_felt

/-- info: 'Foam.Counter.three_recessions_carry' does not depend on any axioms -/
#guard_msgs in #print axioms three_recessions_carry

/-- info: 'Foam.Counter.the_fourth_closes_the_bar' does not depend on any axioms -/
#guard_msgs in #print axioms the_fourth_closes_the_bar

/-- info: 'Foam.Counter.guarded_recession_renews' does not depend on any axioms -/
#guard_msgs in #print axioms guarded_recession_renews

/-- info: 'Foam.Counter.mu_points_at_the_floor' does not depend on any axioms -/
#guard_msgs in #print axioms mu_points_at_the_floor

end Foam.Counter
