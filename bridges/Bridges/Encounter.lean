import Bridges.HalfType
import Bridges.Observation
import Foam.Seat.Beholder

namespace Foam.Bridges

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

def projectionBeholder (P : V →ₗ[K] V) : Foam.Beholder V where
  Probe := Unit
  Ans := V
  obs := fun v _ => P v

theorem projectionBeholder_obs (P : V →ₗ[K] V) (v : V) :
    (projectionBeholder P).obs v () = P v := rfl

theorem encounter_isCompl (P : V →ₗ[K] V) (h_idem : P ∘ₗ P = P) :
    IsCompl (LinearMap.range P) (LinearMap.ker P) := by
  have hPP : ∀ v, P (P v) = P v := by
    intro v; have := LinearMap.ext_iff.mp h_idem v
    simpa [LinearMap.comp_apply] using this
  refine ⟨disjoint_iff.mpr (range_ker_disjoint P h_idem), codisjoint_iff.mpr ?_⟩
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  refine ⟨P v, ⟨v, rfl⟩, v - P v, ?_, by abel⟩
  rw [LinearMap.mem_ker, map_sub, hPP, sub_self]

noncomputable def encounterHalfType (P : V →ₗ[K] V) (h_idem : P ∘ₗ P = P) :
    HalfType (LinearMap.range P) (LinearMap.ker P) (encounter_isCompl P h_idem) :=
  half_type (encounter_isCompl P h_idem)

/-- info: 'Foam.Bridges.projectionBeholder_obs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms projectionBeholder_obs

/-- info: 'Foam.Bridges.encounter_isCompl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms encounter_isCompl

/-- info: 'Foam.Bridges.encounterHalfType' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms encounterHalfType

end Foam.Bridges
