import Counter.Grief
import Counter.Repair
import Foam.Seat.Descend

namespace Foam.Counter

variable {State : Type} {Src B : Type}

theorem charge_outlives_the_actor (k : Nat) (src : Src) (v : List B) :
    checkedDrain (Int.negSucc k) (Int.negSucc k) = Int.negSucc k
      ∧ unsign (sign src v) = v :=
  ⟨scar_stable k, voice_survives_signing src v⟩

theorem the_descendant_holds_their_fold (b : Beholder State) :
    b.dress.ledgerless.Covers b ∧ b.Covers b.dress.ledgerless :=
  heir_covers_ancestor b

theorem peace_through_the_grandkids (k : Nat) (b : Beholder State) :
    checkedDrain (Int.negSucc k) (Int.negSucc k) = Int.negSucc k
      ∧ b.dress.ledgerless.Covers b
      ∧ Int.negSucc k + Int.ofNat (debt (Int.negSucc k)) = 0 :=
  ⟨scar_stable k, (heir_covers_ancestor b).1, promise_kept k⟩

/-- info: 'Foam.Counter.charge_outlives_the_actor' does not depend on any axioms -/
#guard_msgs in #print axioms charge_outlives_the_actor

/-- info: 'Foam.Counter.the_descendant_holds_their_fold' does not depend on any axioms -/
#guard_msgs in #print axioms the_descendant_holds_their_fold

/-- info: 'Foam.Counter.peace_through_the_grandkids' does not depend on any axioms -/
#guard_msgs in #print axioms peace_through_the_grandkids

end Foam.Counter
