import Foam.Bridges.Schrodinger
import Foam.Engine.Chirality
import Foam.Seat.Observer
import Foam.Maintenance

namespace Foam.Bridges

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

/-- info: 'Foam.Bridges.rotPow_conserves_normSq' does not depend on any axioms -/
#guard_msgs in #print axioms rotPow_conserves_normSq

/-- info: 'Foam.Bridges.noether' does not depend on any axioms -/
#guard_msgs in #print axioms noether

theorem a_license_is_a_symmetry (S : Stage) (F : Frontstage S)
    (m : S.State → S.State) (hm : ∀ s, F.rel (m s) s) :
    Invisible S m :=
  fun s p => F.respects (m s) s (hm s) p

theorem noether_for_licenses (S : Stage) (F : Frontstage S)
    (m : S.State → S.State) (hm : ∀ s, F.rel (m s) s)
    (ps : List S.Probe) (s : S.State) :
    transcriptWith S m s ps = transcript S s ps :=
  maintenance_unobservable S m (a_license_is_a_symmetry S F m hm) ps s

/-- info: 'Foam.Bridges.a_license_is_a_symmetry' does not depend on any axioms -/
#guard_msgs in #print axioms a_license_is_a_symmetry

/-- info: 'Foam.Bridges.noether_for_licenses' does not depend on any axioms -/
#guard_msgs in #print axioms noether_for_licenses

end Foam.Bridges
