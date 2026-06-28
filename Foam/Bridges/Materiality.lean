import Foam.Bridges.Noether
import Foam.Seat.Signature

namespace Foam.Bridges

theorem materiality (a b : Rot) (z θ : GInt) (w w' : SInt) (n : Nat) :
    ((a * b).amp = GInt.mul a.amp b.amp ∧ (Rot.amp a).normSq = 1)
      ∧ (rotPow n z).normSq = z.normSq
      ∧ (GInt.born θ z + GInt.born (GInt.rot θ) z = GInt.normSq θ * GInt.normSq z)
      ∧ (halign w w' * halign w w' - hcross w w' * hcross w w' = SInt.hnorm w * SInt.hnorm w') :=
  ⟨⟨Rot.amp_hom a b, Rot.amp_unit a⟩,
   rotPow_conserves_normSq n z,
   GInt.born_parseval θ z,
   hyperbolic_parseval w w'⟩

/-- info: 'Foam.Bridges.materiality' does not depend on any axioms -/
#guard_msgs in #print axioms materiality

end Foam.Bridges
