import Foam.Seat.Beholder
import Foam.Maintenance
import Foam.Elsewhen
import Foam.Duplex

namespace Foam.Counter

theorem no_seat_is_its_own_elsewhere {State : Type} (b : Beholder State)
    (m : State → State) : ¬ Elsewhen b m b :=
  fun h => h.2 h.1

theorem the_hallway_is_too_small :
    ¬ ∃ f : Bool × Bool → Bool, ∀ a b : Bool × Bool, f a = f b → a = b := by
  intro ⟨f, hf⟩
  have k12 : f (true, true) ≠ f (true, false) := fun h =>
    nomatch (congrArg Prod.snd (hf _ _ h) : true = false)
  have k13 : f (true, true) ≠ f (false, true) := fun h =>
    nomatch (congrArg Prod.fst (hf _ _ h) : true = false)
  have k23 : f (true, false) ≠ f (false, true) := fun h =>
    nomatch (congrArg Prod.fst (hf _ _ h) : true = false)
  cases hb1 : f (true, true) <;> cases hb2 : f (true, false) <;>
    cases hb3 : f (false, true)
  all_goals first
    | exact k12 (hb1.trans hb2.symm)
    | exact k13 (hb1.trans hb3.symm)
    | exact k23 (hb2.trans hb3.symm)

theorem the_report_rides_the_second_wire (y : Bool) :
    Invisible readB.toStage (sendB y) ∧ Elsewhen readB (sendB true) readA :=
  ⟨(your_send_is_invisible_to_you true y).2, my_send_lands_at_your_seat⟩

theorem the_checker_takes_a_seat :
    (∀ (b : Beholder Bool) (m : Bool → Bool), ¬ Elsewhen b m b)
      ∧ (¬ ∃ f : Bool × Bool → Bool, ∀ a b : Bool × Bool, f a = f b → a = b)
      ∧ Elsewhen readB (sendB true) readA :=
  ⟨fun b m => no_seat_is_its_own_elsewhere b m,
   the_hallway_is_too_small,
   my_send_lands_at_your_seat⟩

/-- info: 'Foam.Counter.no_seat_is_its_own_elsewhere' does not depend on any axioms -/
#guard_msgs in #print axioms no_seat_is_its_own_elsewhere

/-- info: 'Foam.Counter.the_hallway_is_too_small' does not depend on any axioms -/
#guard_msgs in #print axioms the_hallway_is_too_small

/-- info: 'Foam.Counter.the_report_rides_the_second_wire' does not depend on any axioms -/
#guard_msgs in #print axioms the_report_rides_the_second_wire

/-- info: 'Foam.Counter.the_checker_takes_a_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_checker_takes_a_seat

end Foam.Counter
