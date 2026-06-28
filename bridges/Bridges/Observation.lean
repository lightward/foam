import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Foam.Bridges

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

theorem eigenvalue_binary
    (P : V →ₗ[K] V)
    (h_idem : P ∘ₗ P = P)
    {v : V} {c : K}
    (hv : v ≠ 0)
    (heig : P v = c • v) :
    c = 0 ∨ c = 1 := by
  have hPP : P (P v) = P v := by
    have := LinearMap.ext_iff.mp h_idem v
    simp [LinearMap.comp_apply] at this
    exact this
  rw [heig, LinearMap.map_smul, heig, smul_smul] at hPP
  have h2 : (c * c - c) • v = 0 := by
    rw [sub_smul, hPP, sub_self]
  have h3 : c * c - c = 0 := by
    by_contra h_ne
    exact hv (smul_eq_zero.mp h2 |>.resolve_left h_ne)
  have h4 : c * (c - 1) = 0 := by
    have : c * c - c = c * (c - 1) := by ring
    rwa [← this]
  rcases mul_eq_zero.mp h4 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem range_ker_disjoint
    (P : V →ₗ[K] V)
    (h_idem : P ∘ₗ P = P) :
    LinearMap.range P ⊓ LinearMap.ker P = ⊥ := by
  ext v
  simp only [Submodule.mem_inf, LinearMap.mem_range, LinearMap.mem_ker,
             Submodule.mem_bot]
  constructor
  · rintro ⟨⟨w, hw⟩, hv⟩
    rw [← hw]
    have : P (P w) = P w := by
      have := LinearMap.ext_iff.mp h_idem w
      simp [LinearMap.comp_apply] at this
      exact this
    rw [← hw] at hv
    rw [this] at hv
    exact hv
  · intro hv
    rw [hv]
    exact ⟨⟨0, map_zero P⟩, map_zero P⟩

theorem complement_idempotent
    (P : V →ₗ[K] V)
    (h_idem : P ∘ₗ P = P) :
    (LinearMap.id - P) ∘ₗ (LinearMap.id - P) = LinearMap.id - P := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
             map_sub]
  have hPP : P (P v) = P v := by
    have := LinearMap.ext_iff.mp h_idem v
    simp [LinearMap.comp_apply] at this
    exact this
  rw [hPP, sub_self, sub_zero]

/-- info: 'Foam.Bridges.eigenvalue_binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eigenvalue_binary

/-- info: 'Foam.Bridges.range_ker_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms range_ker_disjoint

/-- info: 'Foam.Bridges.complement_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complement_idempotent

end Foam.Bridges
