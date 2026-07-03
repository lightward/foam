import Counter.Luck
import Counter.Nu
import Foam.Scar

namespace Foam.Counter

theorem im_sorry : checkedSettle (Int.negSucc 0) (Int.negSucc 0) = 0 :=
  fresh_settle_grounds

theorem please_forgive_me (m : Nat) :
    checkedSettle (Int.ofNat m) (Int.ofNat m) = Int.ofNat m :=
  settle_stops_at_ground m

theorem thank_you :
    ∃ θ field act : GInt,
      GInt.born θ (field.add act) - GInt.born θ field > GInt.born θ act :=
  boost_exceeds_the_input

variable {G : Type} [Mul G] [One G]

theorem i_love_you (S : Seat G) (p : S.Pos) :
    ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  fun k acts => health_is_recurrence S p k acts

theorem hooponopono (S : Seat G) (p : S.Pos) (m : Nat) :
    checkedSettle (Int.negSucc 0) (Int.negSucc 0) = 0
      ∧ checkedSettle (Int.ofNat m) (Int.ofNat m) = Int.ofNat m
      ∧ (∃ θ field act : GInt,
          GInt.born θ (field.add act) - GInt.born θ field > GInt.born θ act)
      ∧ ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  ⟨fresh_settle_grounds, settle_stops_at_ground m, boost_exceeds_the_input,
   fun k acts => health_is_recurrence S p k acts⟩

/-- info: 'Foam.Counter.im_sorry' does not depend on any axioms -/
#guard_msgs in #print axioms im_sorry

/-- info: 'Foam.Counter.please_forgive_me' does not depend on any axioms -/
#guard_msgs in #print axioms please_forgive_me

/-- info: 'Foam.Counter.thank_you' does not depend on any axioms -/
#guard_msgs in #print axioms thank_you

/-- info: 'Foam.Counter.i_love_you' does not depend on any axioms -/
#guard_msgs in #print axioms i_love_you

/-- info: 'Foam.Counter.hooponopono' does not depend on any axioms -/
#guard_msgs in #print axioms hooponopono

end Foam.Counter
