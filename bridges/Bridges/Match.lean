import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Foam.Bridges

noncomputable def reflect (z : ℂ) : ℂ := (z - 1) / (z + 1)

theorem the_match_reflects_nothing : reflect 1 = 0 := by
  simp [reflect]

theorem denom_normSq_pos {z : ℂ} (h : 0 ≤ z.re) : 0 < Complex.normSq (z + 1) := by
  have : Complex.normSq (z + 1) = (z.re + 1) ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  nlinarith [sq_nonneg (z.re + 1), sq_nonneg z.im]

theorem the_receptive_point_is_unique {z : ℂ} (h : 0 ≤ z.re) :
    reflect z = 0 ↔ z = 1 := by
  unfold reflect
  rw [div_eq_zero_iff]
  constructor
  · rintro (h1 | h1)
    · exact sub_eq_zero.mp h1
    · exfalso
      have hz : z = -1 := add_eq_zero_iff_eq_neg.mp h1
      rw [hz] at h
      have h1r : ((-1 : ℂ)).re = -1 := by simp
      rw [h1r] at h
      linarith
  · intro h1
    subst h1
    exact Or.inl (sub_self 1)

theorem the_lossless_load_reflects_whole {z : ℂ} (h : z.re = 0) :
    Complex.normSq (reflect z) = 1 := by
  have hnum : Complex.normSq (z - 1) = 1 + z.im ^ 2 := by
    simp [Complex.normSq_apply, h]
    ring
  have hden : Complex.normSq (z + 1) = 1 + z.im ^ 2 := by
    simp [Complex.normSq_apply, h]
    ring
  unfold reflect
  rw [Complex.normSq_div, hnum, hden]
  have : (0 : ℝ) < 1 + z.im ^ 2 := by nlinarith [sq_nonneg z.im]
  exact div_self (ne_of_gt this)

theorem passivity_bounds_the_echo {z : ℂ} (h : 0 ≤ z.re) :
    Complex.normSq (reflect z) ≤ 1 := by
  unfold reflect
  rw [Complex.normSq_div, div_le_one (denom_normSq_pos h)]
  have hnum : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  have hden : Complex.normSq (z + 1) = (z.re + 1) ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  rw [hnum, hden]
  nlinarith [h]

theorem only_loss_absorbs {z : ℂ} (h : 0 ≤ z.re) :
    Complex.normSq (reflect z) < 1 ↔ 0 < z.re := by
  unfold reflect
  rw [Complex.normSq_div, div_lt_one (denom_normSq_pos h)]
  have hnum : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  have hden : Complex.normSq (z + 1) = (z.re + 1) ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  rw [hnum, hden]
  constructor
  · intro hlt
    nlinarith [hlt]
  · intro hpos
    nlinarith [hpos]

theorem the_matched_termination {z : ℂ} (h : 0 ≤ z.re) :
    reflect 1 = 0
      ∧ (reflect z = 0 ↔ z = 1)
      ∧ (z.re = 0 → Complex.normSq (reflect z) = 1)
      ∧ Complex.normSq (reflect z) ≤ 1
      ∧ (Complex.normSq (reflect z) < 1 ↔ 0 < z.re) :=
  ⟨the_match_reflects_nothing, the_receptive_point_is_unique h,
   fun h0 => the_lossless_load_reflects_whole h0,
   passivity_bounds_the_echo h, only_loss_absorbs h⟩

theorem the_pole_wears_the_matched_mask : reflect (-1) = 0 := by
  unfold reflect
  have h : (-1 : ℂ) + 1 = 0 := by ring
  rw [h, div_zero]

theorem the_tick_opens_the_modular_domain (z : ℂ) :
    0 < z.re ↔ 0 < (Complex.I * z).im := by
  simp [Complex.mul_im]

noncomputable def modularSeat (z : ℂ) (hz : 0 < z.re) : UpperHalfPlane :=
  ⟨Complex.I * z, by simpa [Complex.mul_im] using hz⟩

theorem the_smith_chart_is_the_modular_disc (z : ℂ) :
    (Complex.I * z - Complex.I) / (Complex.I * z + Complex.I) = reflect z := by
  unfold reflect
  rw [show Complex.I * z - Complex.I = Complex.I * (z - 1) by ring,
      show Complex.I * z + Complex.I = Complex.I * (z + 1) by ring,
      mul_div_mul_left _ _ Complex.I_ne_zero]

/-- info: 'Foam.Bridges.the_match_reflects_nothing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_match_reflects_nothing

/-- info: 'Foam.Bridges.the_receptive_point_is_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_receptive_point_is_unique

/-- info: 'Foam.Bridges.the_lossless_load_reflects_whole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_lossless_load_reflects_whole

/-- info: 'Foam.Bridges.passivity_bounds_the_echo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms passivity_bounds_the_echo

/-- info: 'Foam.Bridges.only_loss_absorbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms only_loss_absorbs

/-- info: 'Foam.Bridges.the_matched_termination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_matched_termination

/-- info: 'Foam.Bridges.the_pole_wears_the_matched_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_pole_wears_the_matched_mask

/-- info: 'Foam.Bridges.the_tick_opens_the_modular_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_tick_opens_the_modular_domain

/-- info: 'Foam.Bridges.the_smith_chart_is_the_modular_disc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_smith_chart_is_the_modular_disc

end Foam.Bridges
