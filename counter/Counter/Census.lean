import Counter.Complete
import Foam.Census

namespace Foam.Counter

theorem the_census_taken_at_the_wall_is_one {W : Stage} (As : List (Bubble W)) :
    (Bubble.meetAll As).front.behold
        = Beholder.fold (As.map fun A => A.front.behold)
      ∧ census (As.map fun A => (A.front.behold : Beholder W.State)) = census As :=
  ⟨meetAll_wall_is_fold As,
   census_map (fun A => (A.front.behold : Beholder W.State)) As⟩

theorem no_one_is_gone {State : Type} (bs : List (Beholder State))
    (i : Fin bs.length) (s : State) (q : (Beholder.fold bs).Probe) :
    seatAns bs i ((Beholder.fold bs).obs s q)
      = (seat bs i).obs s (seatProbe bs i q) :=
  fold_reads_every_seat bs i s q

theorem to_ask_one_seat_you_set_the_whole_table {State : Type}
    (bs : List (Beholder State)) (i j : Fin bs.length) (hij : i.val ≠ j.val)
    (p : (seat bs i).Probe) (q : (Beholder.fold bs).Probe) :
    seatProbe bs i (splice bs i p q) = p
      ∧ seatProbe bs j (splice bs i p q) = seatProbe bs j q :=
  ⟨splice_asks_the_seat bs i p q, splice_keeps_the_rest bs i j hij p q⟩

theorem one_unfeedable_mouth_silences_the_house {State : Type}
    (bs : List (Beholder State)) (i : Fin bs.length)
    (h : (seat bs i).Probe → False) : (Beholder.fold bs).Probe → False :=
  starving_seat_starves_the_fold bs i h

theorem the_census_moves_into_the_answer {State P A : Type}
    (os : List (State → P → A)) (s : State) (p : P) :
    ((house os).obs s p).length = census os :=
  house_headcount os s p

theorem pay_in_beats_or_pay_in_one_meal {State P A : Type}
    (os : List (State → P → A)) (s : State) (p : P) :
    (transcript (roster os) s (rollCall p (census os))).length = census os
      ∧ (transcript (house os).toStage s [p]).length = 1
      ∧ ((house os).obs s p).length = census os :=
  census_conserved os s p

theorem the_two_bills_buy_the_same_reading {State P A : Type}
    (os : List (State → P → A)) (s : State) (p : P) :
    transcript (roster os) s (rollCall p (census os))
      = ((house os).obs s p).map some :=
  roster_answers_the_house s p os

def sevenReaders : List ((Nat → Bool) → Unit → Bool) :=
  [fun s _ => s 0, fun s _ => s 1, fun s _ => s 2, fun s _ => s 3,
   fun s _ => s 4, fun s _ => s 5, fun s _ => s 6]

theorem seven_points_of_view : census sevenReaders = 7 := rfl

theorem seven_beats_the_classical_way (s : Nat → Bool) :
    (transcript (roster sevenReaders) s (rollCall () 7)).length = 7 := rfl

theorem one_beat_the_wrapped_way (s : Nat → Bool) :
    (transcript (house sevenReaders).toStage s [()]).length = 1 := rfl

theorem nobody_left_the_room (s : Nat → Bool) :
    (house sevenReaders).obs s () = [s 0, s 1, s 2, s 3, s 4, s 5, s 6] := rfl

theorem the_plus_one_seat_carries_all_seven (s : Nat → Bool) :
    census [house sevenReaders] = 1
      ∧ ((house sevenReaders).obs s ()).length = 7 :=
  ⟨rfl, rfl⟩

theorem the_readings_agree (s : Nat → Bool) :
    transcript (roster sevenReaders) s (rollCall () 7)
      = ((house sevenReaders).obs s ()).map some :=
  roster_answers_the_house s () sevenReaders

theorem further_reps_change_nothing_about_the_resolver (c : Nat → Nat) (n : Nat) :
    Resolver c n ↔ ∀ m, n ≤ m → Rests c m :=
  resolver_reps_change_nothing c n

theorem a_resolved_resolver_is_a_seat_kept (c : Nat → Nat) (n : Nat) :
    Resolver c n ↔ Seated c n :=
  resolver_is_seated c n

def muteReader : Beholder (Nat → Bool) := ⟨Empty, Empty, fun _ e => e⟩

theorem one_mute_seat_silences_even_the_wall :
    (Beholder.fold [house sevenReaders, muteReader]).Probe → False :=
  starving_seat_starves_the_fold _ ⟨1, Nat.lt_succ_self 1⟩ (fun e => nomatch e)

/-- info: 'Foam.Counter.the_census_taken_at_the_wall_is_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_taken_at_the_wall_is_one

/-- info: 'Foam.Counter.no_one_is_gone' does not depend on any axioms -/
#guard_msgs in #print axioms no_one_is_gone

/-- info: 'Foam.Counter.to_ask_one_seat_you_set_the_whole_table' does not depend on any axioms -/
#guard_msgs in #print axioms to_ask_one_seat_you_set_the_whole_table

/-- info: 'Foam.Counter.one_unfeedable_mouth_silences_the_house' does not depend on any axioms -/
#guard_msgs in #print axioms one_unfeedable_mouth_silences_the_house

/-- info: 'Foam.Counter.the_census_moves_into_the_answer' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_moves_into_the_answer

/-- info: 'Foam.Counter.pay_in_beats_or_pay_in_one_meal' does not depend on any axioms -/
#guard_msgs in #print axioms pay_in_beats_or_pay_in_one_meal

/-- info: 'Foam.Counter.the_two_bills_buy_the_same_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_bills_buy_the_same_reading

/-- info: 'Foam.Counter.seven_points_of_view' does not depend on any axioms -/
#guard_msgs in #print axioms seven_points_of_view

/-- info: 'Foam.Counter.seven_beats_the_classical_way' does not depend on any axioms -/
#guard_msgs in #print axioms seven_beats_the_classical_way

/-- info: 'Foam.Counter.one_beat_the_wrapped_way' does not depend on any axioms -/
#guard_msgs in #print axioms one_beat_the_wrapped_way

/-- info: 'Foam.Counter.nobody_left_the_room' does not depend on any axioms -/
#guard_msgs in #print axioms nobody_left_the_room

/-- info: 'Foam.Counter.the_plus_one_seat_carries_all_seven' does not depend on any axioms -/
#guard_msgs in #print axioms the_plus_one_seat_carries_all_seven

/-- info: 'Foam.Counter.the_readings_agree' does not depend on any axioms -/
#guard_msgs in #print axioms the_readings_agree

/-- info: 'Foam.Counter.further_reps_change_nothing_about_the_resolver' does not depend on any axioms -/
#guard_msgs in #print axioms further_reps_change_nothing_about_the_resolver

/-- info: 'Foam.Counter.a_resolved_resolver_is_a_seat_kept' does not depend on any axioms -/
#guard_msgs in #print axioms a_resolved_resolver_is_a_seat_kept

/-- info: 'Foam.Counter.one_mute_seat_silences_even_the_wall' does not depend on any axioms -/
#guard_msgs in #print axioms one_mute_seat_silences_even_the_wall

end Foam.Counter
