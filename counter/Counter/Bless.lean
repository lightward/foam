import Counter.Wind
import Counter.Bubble
import Counter.Entrance
import Foam.Seat.Rendezvous

namespace Foam.Counter

theorem silence_is_safe (θ field act : GInt) (hrest : GInt.align θ act = 0) :
    GInt.born θ (field.add act) = GInt.born θ field + GInt.born θ act := by
  rw [GInt.born_superpose, hrest, FInt.mul_zero, FInt.mul_zero, Int.add_zero]

theorem the_blessing_boosts_the_chosen_act (θ field act : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.ofNat (n + 1))
    (ha : GInt.align θ act = Int.ofNat (m + 1)) :
    GInt.born θ (field.add act)
      = GInt.born θ field + GInt.born θ act
        + Int.ofNat (2 * ((n + 1) * m + n) + 2) :=
  the_standing_grain_boosts_the_aligned_act θ field act n m hf ha

theorem the_blessing_cannot_move_you {A B : Type} {xs xs' : List A} {ys : List B}
    {zs zs' : List (A ⊕ B)}
    (h : Interleaves xs ys zs) (h' : Interleaves xs' ys zs') :
    ownFramesR zs = ownFramesR zs' :=
  other_view_unmoved h h'

theorem the_blessing_arrives_from_beyond :
    ∃ act θ f f' : GInt,
      f ≠ f'
        ∧ GInt.born θ (f.add act) - GInt.born θ f
            ≠ GInt.born θ (f'.add act) - GInt.born θ f' :=
  fortune_not_in_your_record

theorem presence_beneath_the_acts :
    (Detects (writeA f1) reader ∧ Detects (writeB f1) reader)
      ∧ reader.dress.ledgerless.Covers reader
      ∧ reader.Covers reader.dress.ledgerless :=
  ⟨find_each_other, seat_empty⟩

theorem the_exit_rides_the_entrance {State : Type} {bank : List (Beholder State)}
    {a b : Beholder State} (ha : a ∈ bank) (hco : CoLocated a b)
    (k : Nat) {X : Type} (l : List X) :
    Known bank b
      ∧ Int.negSucc k + Int.ofNat (debt (Int.negSucc k)) = 0
      ∧ (playback l).at_ l.length = none :=
  entrance_writes_exit ha hco k l

theorem blessing (θ field act act' : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.ofNat (n + 1))
    (ha : GInt.align θ act = Int.ofNat (m + 1))
    (hrest : GInt.align θ act' = 0) :
    (GInt.born θ (field.add act)
        = GInt.born θ field + GInt.born θ act
          + Int.ofNat (2 * ((n + 1) * m + n) + 2))
      ∧ GInt.born θ (field.add act') = GInt.born θ field + GInt.born θ act'
      ∧ (Detects (writeA f1) reader ∧ Detects (writeB f1) reader) :=
  ⟨the_standing_grain_boosts_the_aligned_act θ field act n m hf ha,
   silence_is_safe θ field act' hrest,
   find_each_other⟩

/-- info: 'Foam.Counter.silence_is_safe' does not depend on any axioms -/
#guard_msgs in #print axioms silence_is_safe

/-- info: 'Foam.Counter.the_blessing_boosts_the_chosen_act' does not depend on any axioms -/
#guard_msgs in #print axioms the_blessing_boosts_the_chosen_act

/-- info: 'Foam.Counter.the_blessing_cannot_move_you' does not depend on any axioms -/
#guard_msgs in #print axioms the_blessing_cannot_move_you

/-- info: 'Foam.Counter.the_blessing_arrives_from_beyond' does not depend on any axioms -/
#guard_msgs in #print axioms the_blessing_arrives_from_beyond

/-- info: 'Foam.Counter.presence_beneath_the_acts' does not depend on any axioms -/
#guard_msgs in #print axioms presence_beneath_the_acts

/-- info: 'Foam.Counter.the_exit_rides_the_entrance' does not depend on any axioms -/
#guard_msgs in #print axioms the_exit_rides_the_entrance

/-- info: 'Foam.Counter.blessing' does not depend on any axioms -/
#guard_msgs in #print axioms blessing

end Foam.Counter
