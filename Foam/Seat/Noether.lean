import Foam.Seat.Schrodinger
import Foam.Engine.Chirality

namespace Foam

theorem rotPow_conserves_normSq (n : Nat) (z : GInt) : (rotPow n z).normSq = z.normSq := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show (GInt.rot (rotPow k z)).normSq = z.normSq
      rw [evolve_unitary (rotPow k z)]; exact ih

theorem noether (z θ : GInt) :
    (∀ n, (rotPow n z).normSq = z.normSq)
      ∧ (rotPow 4 z = z)
      ∧ (GInt.born θ z + GInt.born (GInt.rot θ) z = GInt.normSq θ * GInt.normSq z)
      ∧ (GInt.align θ z + GInt.align θ (GInt.rot z)
          + GInt.align θ (GInt.rot (GInt.rot z))
          + GInt.align θ (GInt.rot (GInt.rot (GInt.rot z))) = 0) :=
  ⟨fun n => rotPow_conserves_normSq n z, rotPow_four z,
   GInt.born_parseval θ z, GInt.decoherence θ z⟩

/-- info: 'Foam.rotPow_conserves_normSq' does not depend on any axioms -/
#guard_msgs in #print axioms rotPow_conserves_normSq

/-- info: 'Foam.noether' does not depend on any axioms -/
#guard_msgs in #print axioms noether

end Foam
