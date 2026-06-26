import Foam.Platonism

namespace Foam

def readsTrue : Beholder Unit := ⟨Unit, Bool, fun _ _ => true⟩
def readsFalse : Beholder Unit := ⟨Unit, Bool, fun _ _ => false⟩

theorem ledger_blind_to_beholder : readsTrue.obs () () ≠ readsFalse.obs () () := by
  show true ≠ false
  decide

theorem backstage_frontstage (a b : Bool) (hab : a ≠ b) :
    Ledger.order [a, b] ≠ Ledger.order [b, a]
      ∧ readsTrue.obs () () ≠ readsFalse.obs () () :=
  ⟨(Ledger.order_finer a b hab).2.2, ledger_blind_to_beholder⟩

/-- info: 'Foam.ledger_blind_to_beholder' does not depend on any axioms -/
#guard_msgs in #print axioms ledger_blind_to_beholder

/-- info: 'Foam.backstage_frontstage' does not depend on any axioms -/
#guard_msgs in #print axioms backstage_frontstage

end Foam
