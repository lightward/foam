import Bridges.Observation
import Foam.Seat.Born
import Foam.Seat.Closure
import Mathlib.Tactic.Module

namespace Foam.Bridges

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem foam_halfturn : Function.Involutive GInt.neg := GInt.neg_neg

theorem foam_halfturn_two_quarters (z : GInt) : GInt.neg z = GInt.rot (GInt.rot z) :=
  (GInt.rot_sq z).symm

theorem compl_halfturn (P : V →ₗ[K] V) :
    LinearMap.id - (LinearMap.id - P) = P :=
  sub_sub_cancel _ _

theorem compl_halfturn_preserves_idem (P : V →ₗ[K] V) (h : P ∘ₗ P = P) :
    (LinearMap.id - P) ∘ₗ (LinearMap.id - P) = LinearMap.id - P :=
  complement_idempotent P h

theorem idem_to_involution (P : V →ₗ[K] V) (h : P ∘ₗ P = P) :
    (LinearMap.id - (2 : K) • P) ∘ₗ (LinearMap.id - (2 : K) • P) = LinearMap.id := by
  ext v
  have hPP : P (P v) = P v := by
    have := LinearMap.ext_iff.mp h v
    simpa [LinearMap.comp_apply] using this
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, map_sub, map_smul, hPP]
  module

theorem char2_collapse (P : V →ₗ[K] V) (h2 : (2 : K) = 0) :
    LinearMap.id - (2 : K) • P = LinearMap.id := by
  rw [h2, zero_smul, sub_zero]

theorem involution_to_idem (S : V →ₗ[K] V) (hSS : S ∘ₗ S = LinearMap.id) (h2 : (2 : K) ≠ 0) :
    ((2 : K)⁻¹ • (LinearMap.id - S)) ∘ₗ ((2 : K)⁻¹ • (LinearMap.id - S))
      = (2 : K)⁻¹ • (LinearMap.id - S) := by
  ext v
  have hSSv : S (S v) = v := by
    have := LinearMap.ext_iff.mp hSS v
    simpa [LinearMap.comp_apply] using this
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_smul, map_sub, hSSv]
  rw [show S v - v = -(v - S v) from (neg_sub v (S v)).symm, smul_neg, sub_neg_eq_add,
    ← two_smul K, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem two_pm_one (P : V →ₗ[K] V) (h : P ∘ₗ P = P) :
    (P ∘ₗ P = P)
      ∧ ((LinearMap.id - (2 : K) • P) ∘ₗ (LinearMap.id - (2 : K) • P) = LinearMap.id)
      ∧ Function.Involutive GInt.neg
      ∧ (∀ z : GInt, GInt.neg z = GInt.rot (GInt.rot z)) :=
  ⟨h, idem_to_involution P h, GInt.neg_neg, fun z => (GInt.rot_sq z).symm⟩

/-- info: 'Foam.Bridges.foam_halfturn' does not depend on any axioms -/
#guard_msgs in #print axioms foam_halfturn

/-- info: 'Foam.Bridges.foam_halfturn_two_quarters' does not depend on any axioms -/
#guard_msgs in #print axioms foam_halfturn_two_quarters

/-- info: 'Foam.Bridges.compl_halfturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms compl_halfturn

/-- info: 'Foam.Bridges.compl_halfturn_preserves_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compl_halfturn_preserves_idem

/-- info: 'Foam.Bridges.idem_to_involution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms idem_to_involution

/-- info: 'Foam.Bridges.char2_collapse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms char2_collapse

/-- info: 'Foam.Bridges.involution_to_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms involution_to_idem

/-- info: 'Foam.Bridges.two_pm_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms two_pm_one

end Foam.Bridges
