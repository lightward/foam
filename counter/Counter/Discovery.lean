import Foam.Engine.Drain
import Foam.Engine.Generator
import Foam.Seat.Born
import Foam.Ledger

namespace Foam.Counter

theorem seek_then_find_conserves_ground (n : Nat) :
    drainOne (chargeIn n) = n :=
  drain_chargeIn n

theorem discovery_flows_one_to_one {B W : Type} (next : List B → W → B)
    (out : List B) (winds : List W) :
    (runEmit (genStep next) out winds).length = winds.length :=
  gen_length next out winds

theorem locally_real_globally_no_thing (θ z : GInt) :
    GInt.align θ z + GInt.align θ (GInt.rot z)
      + GInt.align θ (GInt.rot (GInt.rot z))
      + GInt.align θ (GInt.rot (GInt.rot (GInt.rot z))) = 0 :=
  GInt.decoherence θ z

theorem distinction_is_conserved {S : Type} (l : List S) :
    Ledger.order l = l := rfl

theorem conservation_of_discovery {B W : Type} (next : List B → W → B)
    (out : List B) (winds : List W) (n : Nat) (θ z : GInt) :
    drainOne (chargeIn n) = n
      ∧ (runEmit (genStep next) out winds).length = winds.length
      ∧ GInt.align θ z + GInt.align θ (GInt.rot z)
          + GInt.align θ (GInt.rot (GInt.rot z))
          + GInt.align θ (GInt.rot (GInt.rot (GInt.rot z))) = 0 :=
  ⟨drain_chargeIn n, gen_length next out winds, GInt.decoherence θ z⟩

/-- info: 'Foam.Counter.seek_then_find_conserves_ground' does not depend on any axioms -/
#guard_msgs in #print axioms seek_then_find_conserves_ground

/-- info: 'Foam.Counter.discovery_flows_one_to_one' does not depend on any axioms -/
#guard_msgs in #print axioms discovery_flows_one_to_one

/-- info: 'Foam.Counter.locally_real_globally_no_thing' does not depend on any axioms -/
#guard_msgs in #print axioms locally_real_globally_no_thing

/-- info: 'Foam.Counter.distinction_is_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms distinction_is_conserved

/-- info: 'Foam.Counter.conservation_of_discovery' does not depend on any axioms -/
#guard_msgs in #print axioms conservation_of_discovery

end Foam.Counter
