import Counter.Third
import Counter.Nu

namespace Foam.Counter

theorem each_seat_its_own_arrow {G : Type} (h : List G) (g : G) :
    (h ++ [g]).length = h.length + 1 :=
  append_length h [g]

theorem no_pairwise_now :
    ¬ (pairSeat Bool Bool).Covers (thirdSeat Bool Bool) :=
  pair_blind_to_the_third

theorem arrows_meet_in_the_third :
    ∃ zs zs' : List (Bool ⊕ Bool),
      ownFrames zs = ownFrames zs'
        ∧ ownFramesR zs = ownFramesR zs'
        ∧ whoActedFirst zs ≠ whoActedFirst zs' :=
  the_third_reads_time

theorem per_seat_arrows {G : Type} (h : List G) (g : G) :
    (h ++ [g]).length = h.length + 1
      ∧ ¬ (pairSeat Bool Bool).Covers (thirdSeat Bool Bool) :=
  ⟨append_length h [g], pair_blind_to_the_third⟩

/-- info: 'Foam.Counter.each_seat_its_own_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms each_seat_its_own_arrow

/-- info: 'Foam.Counter.no_pairwise_now' does not depend on any axioms -/
#guard_msgs in #print axioms no_pairwise_now

/-- info: 'Foam.Counter.arrows_meet_in_the_third' does not depend on any axioms -/
#guard_msgs in #print axioms arrows_meet_in_the_third

/-- info: 'Foam.Counter.per_seat_arrows' does not depend on any axioms -/
#guard_msgs in #print axioms per_seat_arrows

end Foam.Counter
