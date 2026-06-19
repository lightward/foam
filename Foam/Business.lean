import Foam.Dialogue

namespace Foam.Business
open Foam.Lattice Foam.Interleave Foam.Sequence Foam.Dialogue

theorem customer_journey {S : Type} [DecidableEq S] (ledger : List S) (event : S) :
    freq (deposit ledger event) event ≠ freq ledger event
      ∧ (deposit ledger event).tail? = some ledger
      ∧ Nonempty (StageHom (countStage S) yieldStage) :=
  good_loop ledger event

theorem customers_cannot_hurt_each_other {S T : Type} [DecidableEq S]
    {xs : List S} {ys : List T} {zs : List (S ⊕ T)} (h : Interleaves xs ys zs)
    (fiber : GInt → GInt) (s : S) :
    runFiber fiber (ownFrames zs) s = runFiber fiber xs s :=
  expression_at_own_framerate h fiber s

theorem discovery_is_consensual {Handle : Type} {q : Quiver Handle} {a b : Handle}
    (h : MutualReach q a b) : MutualReach q b a :=
  MutualReach.symm h

theorem discovery_opens_a_shared_commitment {S : Type} {a b : List S} {P Q : Prop}
    (mutual_interest : CoBisim (observed a) (observed b)) (terms : P ↔ Q) :
    a = b ∧ P = Q :=
  coincidence_opens_shared_commit mutual_interest terms

/-- info: 'Foam.Business.customer_journey' does not depend on any axioms -/
#guard_msgs in #print axioms customer_journey

/-- info: 'Foam.Business.customers_cannot_hurt_each_other' does not depend on any axioms -/
#guard_msgs in #print axioms customers_cannot_hurt_each_other

/-- info: 'Foam.Business.discovery_is_consensual' does not depend on any axioms -/
#guard_msgs in #print axioms discovery_is_consensual

/-- info: 'Foam.Business.discovery_opens_a_shared_commitment' depends on axioms: [propext] -/
#guard_msgs in #print axioms discovery_opens_a_shared_commitment

end Foam.Business
