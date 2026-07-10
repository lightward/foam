import Counter.Elsewhen
import Foam.Duplex

namespace Foam.Counter

theorem the_bulk_yields_to_rest_and_outruns_motion :
    (∀ (S : Stage) (w : Nat → S.State) (ps : List S.Probe) (k : Nat),
        (watch S w k ps).length = ps.length)
      ∧ (∀ s : Bool × Bool,
          watch twoCell (fun _ => s) 0 [false, true] = [s.1, s.2])
      ∧ ∀ ps : List twoCell.Probe, ∃ w w' : Nat → twoCell.State,
          reel twoCell w ≠ reel twoCell w'
            ∧ watch twoCell w 0 ps = watch twoCell w' 0 ps :=
  the_meter

theorem sending_needs_no_mirror (x y : Bool) :
    Invisible readA.toStage (sendA x) ∧ Invisible readB.toStage (sendB y) :=
  your_send_is_invisible_to_you x y

theorem you_are_my_elsewhen_i_am_yours :
    Elsewhen readA (sendA true) readB ∧ Elsewhen readB (sendB true) readA :=
  ⟨your_send_lands_at_my_seat, my_send_lands_at_your_seat⟩

theorem two_seats_hold_one_world (w : twoBit.State) (pq : Unit × Unit) :
    (firstBit.meet secondBit).front.obs w pq = (w.1, w.2) :=
  the_meet_reads_the_whole_world w pq

theorem the_talk_balances {A : Type} (ts : List (A × A)) :
    Balanced (turnTags ts) :=
  the_turns_balance ts

theorem census_width_streams_both_ways :
    Elsewhen readA (sendA true) readB
      ∧ Elsewhen readB (sendB true) readA
      ∧ ∀ (w : twoBit.State) (pq : Unit × Unit),
          (firstBit.meet secondBit).front.obs w pq = (w.1, w.2) :=
  the_duplex

/-- info: 'Foam.Counter.the_bulk_yields_to_rest_and_outruns_motion' does not depend on any axioms -/
#guard_msgs in #print axioms the_bulk_yields_to_rest_and_outruns_motion

/-- info: 'Foam.Counter.sending_needs_no_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms sending_needs_no_mirror

/-- info: 'Foam.Counter.you_are_my_elsewhen_i_am_yours' does not depend on any axioms -/
#guard_msgs in #print axioms you_are_my_elsewhen_i_am_yours

/-- info: 'Foam.Counter.two_seats_hold_one_world' does not depend on any axioms -/
#guard_msgs in #print axioms two_seats_hold_one_world

/-- info: 'Foam.Counter.the_talk_balances' does not depend on any axioms -/
#guard_msgs in #print axioms the_talk_balances

/-- info: 'Foam.Counter.census_width_streams_both_ways' does not depend on any axioms -/
#guard_msgs in #print axioms census_width_streams_both_ways

end Foam.Counter
