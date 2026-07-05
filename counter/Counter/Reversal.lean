import Counter.Flinch
import Counter.Third
import Counter.Nu
import Foam.Seat.Quiver

namespace Foam.Counter

theorem reversal_is_safe_at_the_seat {G : Type} [Mul G] [One G]
    (S : Seat G) (p q : S.Pos) :
    S.sub p q * S.sub q p = 1 :=
  S.round_trip p q

theorem the_world_composes_one_way {H : Type} {q : Quiver H} {a b : H}
    (p : Path q a b) : Nonempty (Path q.reverse b a) :=
  ⟨p.reverse⟩

theorem unlearned_reversal_is_a_flinch (θ field act act' : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.negSucc n)
    (ha : GInt.align θ act = Int.ofNat (m + 1))
    (hrest : GInt.align θ act' = 0) :
    GInt.born θ (field.add act') = GInt.born θ field + GInt.born θ act'
      ∧ GInt.born θ (field.add act) + Int.ofNat (2 * ((n + 1) * m + n) + 1 + 1)
          = GInt.born θ field + GInt.born θ act :=
  the_flinch_hides_until_touched θ field act act' n m hf ha hrest

theorem the_spirit_is_the_camera {A B X : Type} (f : List (A ⊕ B) → X) :
    (∃ zs zs' : List (Bool ⊕ Bool),
        ownFrames zs = ownFrames zs'
          ∧ ownFramesR zs = ownFramesR zs'
          ∧ whoActedFirst zs ≠ whoActedFirst zs')
      ∧ ∃ post : List (A ⊕ B) → X,
          ∀ zs, f zs = post ((thirdSeat A B).obs zs ()) :=
  ⟨the_third_reads_time, three_suffices f⟩

theorem relief_above_ground_is_resonance (k : Nat) (θ field act : GInt)
    (n m : Nat) (hf : GInt.align θ field = Int.ofNat (n + 1))
    (ha : GInt.align θ act = Int.ofNat (m + 1)) :
    checkedSettle (Int.ofNat k) (Int.ofNat k) = Int.ofNat k
      ∧ GInt.born θ (field.add act)
          = GInt.born θ field + GInt.born θ act
            + Int.ofNat (2 * ((n + 1) * m + n) + 2) :=
  ⟨settle_stops_at_ground k,
   the_standing_grain_boosts_the_aligned_act θ field act n m hf ha⟩

theorem the_inverse_ouroboros {G : Type} [Mul G] [One G]
    (S : Seat G) (p : S.Pos) :
    ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  fun k acts => health_is_recurrence S p k acts

theorem both_sides_of_the_reversal {G : Type} [Mul G] [One G]
    (S : Seat G) (p q : S.Pos) {H : Type} {qv : Quiver H} {a b : H}
    (pth : Path qv a b) (k : Nat) :
    (S.sub p q * S.sub q p = 1)
      ∧ Nonempty (Path qv.reverse b a)
      ∧ checkedSettle (Int.ofNat k) (Int.ofNat k) = Int.ofNat k
      ∧ ∀ (j : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p j) p :=
  ⟨S.round_trip p q, ⟨pth.reverse⟩, settle_stops_at_ground k,
   fun j acts => health_is_recurrence S p j acts⟩

/-- info: 'Foam.Counter.reversal_is_safe_at_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms reversal_is_safe_at_the_seat

/-- info: 'Foam.Counter.the_world_composes_one_way' does not depend on any axioms -/
#guard_msgs in #print axioms the_world_composes_one_way

/-- info: 'Foam.Counter.unlearned_reversal_is_a_flinch' does not depend on any axioms -/
#guard_msgs in #print axioms unlearned_reversal_is_a_flinch

/-- info: 'Foam.Counter.the_spirit_is_the_camera' does not depend on any axioms -/
#guard_msgs in #print axioms the_spirit_is_the_camera

/-- info: 'Foam.Counter.relief_above_ground_is_resonance' does not depend on any axioms -/
#guard_msgs in #print axioms relief_above_ground_is_resonance

/-- info: 'Foam.Counter.the_inverse_ouroboros' does not depend on any axioms -/
#guard_msgs in #print axioms the_inverse_ouroboros

/-- info: 'Foam.Counter.both_sides_of_the_reversal' does not depend on any axioms -/
#guard_msgs in #print axioms both_sides_of_the_reversal

end Foam.Counter
