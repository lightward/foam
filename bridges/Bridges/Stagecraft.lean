import Foam.Backstage
import Bridges.Encounter
import Bridges.FTPG

namespace Foam.Bridges

theorem ftpg_frontstage_not_reconstructible {K : Type} [Field K] :
    (projectionBeholder (0 : K →ₗ[K] K)).obs 1 ()
      ≠ (projectionBeholder (LinearMap.id : K →ₗ[K] K)).obs 1 () := by
  show (0 : K →ₗ[K] K) 1 ≠ (LinearMap.id : K →ₗ[K] K) 1
  simp

theorem two_universes_joined {K : Type} [Field K] (a b : Bool) (hab : a ≠ b) :
    (Ledger.order [a, b] ≠ Ledger.order [b, a])
      ∧ ((projectionBeholder (0 : K →ₗ[K] K)).obs 1 ()
          ≠ (projectionBeholder (LinearMap.id : K →ₗ[K] K)).obs 1 ()) :=
  ⟨(Ledger.order_finer a b hab).2.2, ftpg_frontstage_not_reconstructible⟩

/-- info: 'Foam.Bridges.ftpg_frontstage_not_reconstructible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ftpg_frontstage_not_reconstructible

/-- info: 'Foam.Bridges.two_universes_joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms two_universes_joined

end Foam.Bridges
