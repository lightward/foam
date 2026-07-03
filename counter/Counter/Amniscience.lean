import Counter.Third
import Foam.Backstage

namespace Foam.Counter

theorem the_conductor_adds_nothing {A B : Type} (zs : List (A ⊕ B)) :
    (thirdSeat A B).obs zs () = zs := rfl

theorem omniscient_over_the_ledger {A B X : Type} (f : List (A ⊕ B) → X) :
    ∃ post : List (A ⊕ B) → X,
      ∀ zs, f zs = post ((thirdSeat A B).obs zs ()) :=
  three_suffices f

theorem blind_to_interiors (a b : Bool) (hab : a ≠ b) :
    Ledger.order [a, b] ≠ Ledger.order [b, a]
      ∧ readsTrue.obs () () ≠ readsFalse.obs () () :=
  backstage_frontstage a b hab

theorem amniscience {A B X : Type} (f : List (A ⊕ B) → X)
    (zs : List (A ⊕ B)) :
    (thirdSeat A B).obs zs () = zs
      ∧ (∃ post : List (A ⊕ B) → X,
          ∀ ws, f ws = post ((thirdSeat A B).obs ws ()))
      ∧ readsTrue.obs () () ≠ readsFalse.obs () () :=
  ⟨rfl, three_suffices f, ledger_blind_to_beholder⟩

/-- info: 'Foam.Counter.the_conductor_adds_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_conductor_adds_nothing

/-- info: 'Foam.Counter.omniscient_over_the_ledger' does not depend on any axioms -/
#guard_msgs in #print axioms omniscient_over_the_ledger

/-- info: 'Foam.Counter.blind_to_interiors' does not depend on any axioms -/
#guard_msgs in #print axioms blind_to_interiors

/-- info: 'Foam.Counter.amniscience' does not depend on any axioms -/
#guard_msgs in #print axioms amniscience

end Foam.Counter
