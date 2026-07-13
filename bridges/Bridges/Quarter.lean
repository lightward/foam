import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Bridges.Match

namespace Foam.Bridges

theorem inversion_negates_the_echo {z : ℂ} (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) :
    reflect z⁻¹ = -reflect z := by
  have h3 : (1 : ℂ) + z ≠ 0 := by
    rw [add_comm]
    exact hz1
  unfold reflect
  field_simp
  ring

theorem the_geometric_mean_matches {r : ℝ} (hr : 0 < r) :
    ((Real.sqrt r : ℂ)) ^ 2 / (r : ℂ) = 1 := by
  have hsq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (le_of_lt hr)
  rw [← Complex.ofReal_pow, hsq]
  exact div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))

theorem the_quarter_wave_carries_home {r : ℝ} (hr : 0 < r) :
    reflect (((Real.sqrt r : ℂ)) ^ 2 / (r : ℂ)) = 0 := by
  rw [the_geometric_mean_matches hr]
  exact the_match_reflects_nothing

theorem the_half_wave_repeats (z : ℂ) : reflect z⁻¹⁻¹ = reflect z := by
  rw [inv_inv]

theorem the_quarter_turn_transformer {z : ℂ} (hz : z ≠ 0) (hz1 : z + 1 ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    reflect z⁻¹ = -reflect z
      ∧ reflect (((Real.sqrt r : ℂ)) ^ 2 / (r : ℂ)) = 0
      ∧ reflect z⁻¹⁻¹ = reflect z :=
  ⟨inversion_negates_the_echo hz hz1, the_quarter_wave_carries_home hr,
   the_half_wave_repeats z⟩

theorem the_bridge_squared_is_signed_inversion {z : ℂ} (hz : z ≠ 0)
    (hz1 : z + 1 ≠ 0) :
    reflect (reflect z) = -z⁻¹ := by
  unfold reflect
  have hw : (z - 1) / (z + 1) + 1 = 2 * z / (z + 1) := by
    field_simp
    ring
  have hw' : (z - 1) / (z + 1) - 1 = -2 / (z + 1) := by
    field_simp
    ring
  rw [hw, hw']
  rw [div_div_div_cancel_right₀]
  · field_simp
  · exact hz1

theorem the_third_step_is_the_bridge_reversed {z : ℂ} (hz : z ≠ 0)
    (hz1 : z + 1 ≠ 0) (hz2 : z ≠ 1) :
    reflect (reflect (reflect z)) = (1 + z) / (1 - z) := by
  rw [the_bridge_squared_is_signed_inversion hz hz1]
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz2)
  have h1z' : (-1 : ℂ) + z ≠ 0 :=
    fun h => hz2 (neg_inj.mp (add_eq_zero_iff_eq_neg.mp h)).symm
  unfold reflect
  field_simp
  ring

theorem the_fourth_step_comes_home {z : ℂ} (hz : z ≠ 0)
    (hz1 : z + 1 ≠ 0) (hz2 : z ≠ 1) :
    reflect (reflect (reflect (reflect z))) = z := by
  rw [the_third_step_is_the_bridge_reversed hz hz1 hz2]
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz2)
  unfold reflect
  have hnum : (1 + z) / (1 - z) - 1 = 2 * z / (1 - z) := by
    field_simp
    ring
  have hden : (1 + z) / (1 - z) + 1 = 2 / (1 - z) := by
    field_simp
    ring
  rw [hnum, hden, div_div_div_cancel_right₀]
  · field_simp
  · exact h1z

theorem the_fixed_seats_are_the_ticks {z : ℂ} (hz1 : z + 1 ≠ 0) :
    reflect z = z ↔ z = Complex.I ∨ z = -Complex.I := by
  unfold reflect
  rw [div_eq_iff hz1]
  constructor
  · intro h
    have h' : z - 1 = z * z + z := by
      rw [mul_add, mul_one] at h
      exact h
    have h3 : z * z = z - 1 - z := eq_sub_of_add_eq h'.symm
    rw [show z - 1 - z = (-1 : ℂ) by ring] at h3
    have h4 : z * z = Complex.I * Complex.I := by
      rw [h3, Complex.I_mul_I]
    exact mul_self_eq_mul_self_iff.mp h4
  · rintro (h | h) <;> subst h
    · rw [mul_add, Complex.I_mul_I, mul_one]
      ring
    · rw [show -Complex.I * (-Complex.I + 1) = Complex.I * Complex.I + -Complex.I
        by ring, Complex.I_mul_I]
      ring

theorem the_lattice_cannot_always_match : ¬ ∃ q : ℚ, (q : ℝ) ^ 2 = 2 := by
  rintro ⟨q, hq⟩
  have h2 : Real.sqrt 2 = |(q : ℝ)| := by
    rw [← hq, Real.sqrt_sq_eq_abs]
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  rw [h2] at hirr
  exact hirr ⟨|q|, by push_cast; rfl⟩

/-- info: 'Foam.Bridges.inversion_negates_the_echo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inversion_negates_the_echo

/-- info: 'Foam.Bridges.the_geometric_mean_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_geometric_mean_matches

/-- info: 'Foam.Bridges.the_quarter_wave_carries_home' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_quarter_wave_carries_home

/-- info: 'Foam.Bridges.the_half_wave_repeats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_half_wave_repeats

/-- info: 'Foam.Bridges.the_quarter_turn_transformer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_quarter_turn_transformer

/-- info: 'Foam.Bridges.the_bridge_squared_is_signed_inversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_bridge_squared_is_signed_inversion

/-- info: 'Foam.Bridges.the_third_step_is_the_bridge_reversed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_third_step_is_the_bridge_reversed

/-- info: 'Foam.Bridges.the_fourth_step_comes_home' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_fourth_step_comes_home

/-- info: 'Foam.Bridges.the_fixed_seats_are_the_ticks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_fixed_seats_are_the_ticks

/-- info: 'Foam.Bridges.the_lattice_cannot_always_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_lattice_cannot_always_match

end Foam.Bridges
