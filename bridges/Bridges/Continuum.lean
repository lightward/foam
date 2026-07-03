import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic

namespace Foam.Bridges

open Real AddSubgroup

noncomputable def goldenBoost : ℝ := 2 + √5

noncomputable def silverBoost : ℝ := 1 + √2

theorem golden_tower : ∀ q : ℕ, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    goldenBoost ^ (q + 1) = a + b * √5
  | 0 => ⟨2, 1, by norm_num, by norm_num, by simp [goldenBoost]⟩
  | q + 1 => by
    obtain ⟨a, b, ha, hb, hab⟩ := golden_tower q
    refine ⟨2 * a + 5 * b, a + 2 * b, by positivity, by positivity, ?_⟩
    have h5 : (√5) * (√5) = 5 := Real.mul_self_sqrt (by norm_num)
    have hstep : goldenBoost ^ (q + 1 + 1) = goldenBoost ^ (q + 1) * goldenBoost := by
      ring
    rw [hstep, hab]
    unfold goldenBoost
    push_cast
    linear_combination (b : ℝ) * h5

theorem silver_tower : ∀ p : ℕ, ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    silverBoost ^ (p + 1) = c + d * √2
  | 0 => ⟨1, 1, by norm_num, by norm_num, by simp [silverBoost]⟩
  | p + 1 => by
    obtain ⟨c, d, hc, hd, hcd⟩ := silver_tower p
    refine ⟨c + 2 * d, c + d, by positivity, by positivity, ?_⟩
    have h2 : (√2) * (√2) = 2 := Real.mul_self_sqrt (by norm_num)
    have hstep : silverBoost ^ (p + 1 + 1) = silverBoost ^ (p + 1) * silverBoost := by
      ring
    rw [hstep, hcd]
    unfold silverBoost
    push_cast
    linear_combination (d : ℝ) * h2

theorem boosts_incommensurable (q p : ℕ) :
    goldenBoost ^ (q + 1) ≠ silverBoost ^ (p + 1) := by
  obtain ⟨a, b, ha, hb, hab⟩ := golden_tower q
  obtain ⟨c, d, hc, hd, hcd⟩ := silver_tower p
  intro h
  rw [hab, hcd] at h
  have h5 : (√5) * (√5) = 5 := Real.mul_self_sqrt (by norm_num)
  have h2 : (√2) * (√2) = 2 := Real.mul_self_sqrt (by norm_num)
  have h10 : (√5) * (√2) = √10 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 5)]
    norm_num
  set k : ℝ := (c : ℝ) - a with hk
  have hb5 : (b : ℝ) * √5 = k + d * √2 := by rw [hk]; linarith [h]
  have hbpos : (0:ℝ) < b := by exact_mod_cast hb
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  rcases eq_or_ne k 0 with hk0 | hk0
  · -- k = 0: b√5 = d√2, multiply by √2: b√10 = 2d, √10 rational
    rw [hk0, zero_add] at hb5
    have h10eq : (b : ℝ) * √10 = 2 * d := by
      calc (b : ℝ) * √10 = (b : ℝ) * √5 * √2 := by rw [mul_assoc, h10]
        _ = (d : ℝ) * √2 * √2 := by rw [hb5]
        _ = 2 * d := by rw [mul_assoc, h2]; ring
    have h10irr : Irrational (√(10 : ℕ)) :=
      irrational_sqrt_natCast_iff.mpr (by
        rintro ⟨r, hr⟩
        rcases Nat.lt_or_ge r 4 with h4 | h4
        · interval_cases r <;> omega
        · have : 16 ≤ r * r := Nat.mul_le_mul h4 h4
          omega)
    have h10irr' : Irrational (√10) := by
      rwa [Nat.cast_ofNat] at h10irr
    refine h10irr' ⟨(2 * d / b : ℚ), ?_⟩
    push_cast
    rw [div_eq_iff (ne_of_gt hbpos)]
    linear_combination -h10eq
  · -- k ≠ 0: square hb5 and solve for √2
    have hsq : (b : ℝ) * √5 * ((b : ℝ) * √5) = (k + d * √2) * (k + d * √2) := by
      rw [hb5]
    have key : 2 * k * d * √2 = 5 * (b : ℝ)^2 - k^2 - 2 * d^2 := by
      linear_combination -hsq + (b:ℝ)^2 * h5 - (d:ℝ)^2 * h2
    have hkd : 2 * k * d ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hk0) (ne_of_gt hdpos)
    refine irrational_sqrt_two
      ⟨((5 * b^2 - ((c:ℚ) - a)^2 - 2 * d^2) / (2 * ((c:ℚ) - a) * d)), ?_⟩
    have hcast : (((5 * b^2 - ((c:ℚ) - a)^2 - 2 * d^2) / (2 * ((c:ℚ) - a) * d) : ℚ) : ℝ)
        = (5 * (b:ℝ)^2 - k^2 - 2 * d^2) / (2 * k * d) := by
      push_cast
      rw [hk]
    rw [hcast, div_eq_iff hkd]
    linear_combination -key

theorem rapidities_dense :
    Dense ((AddSubgroup.closure
      {Real.log goldenBoost, Real.log silverBoost} : AddSubgroup ℝ) : Set ℝ) := by
  rcases AddSubgroup.dense_or_cyclic
      (AddSubgroup.closure {Real.log goldenBoost, Real.log silverBoost}) with hd | ⟨a, ha⟩
  · exact hd
  · exfalso
    have hgB1 : (1 : ℝ) < goldenBoost := by
      have := Real.sqrt_nonneg (5 : ℝ)
      unfold goldenBoost
      linarith
    have hsB1 : (1 : ℝ) < silverBoost := by
      have : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
      unfold silverBoost
      linarith
    have hlg : 0 < Real.log goldenBoost := Real.log_pos hgB1
    have hls : 0 < Real.log silverBoost := Real.log_pos hsB1
    have hgmem : Real.log goldenBoost
        ∈ AddSubgroup.closure {Real.log goldenBoost, Real.log silverBoost} :=
      AddSubgroup.subset_closure (Set.mem_insert _ _)
    have hsmem : Real.log silverBoost
        ∈ AddSubgroup.closure {Real.log goldenBoost, Real.log silverBoost} :=
      AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rw [ha] at hgmem hsmem
    obtain ⟨m, hm⟩ := AddSubgroup.mem_closure_singleton.mp hgmem
    obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp hsmem
    have hcross : (n : ℝ) * Real.log goldenBoost = (m : ℝ) * Real.log silverBoost := by
      rw [← hm, ← hn]
      push_cast [zsmul_eq_mul]
      ring
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_zsmul] at hm
      exact (ne_of_gt hlg) hm.symm
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [zero_zsmul] at hn
      exact (ne_of_gt hls) hn.symm
    have habs : (n.natAbs : ℝ) * Real.log goldenBoost
        = (m.natAbs : ℝ) * Real.log silverBoost := by
      have h1 := congrArg abs hcross
      rw [abs_mul, abs_mul, abs_of_pos hlg, abs_of_pos hls] at h1
      have hcast : ∀ k : ℤ, ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
        intro k
        simp
      rw [hcast, hcast]
      exact h1
    have hpow : goldenBoost ^ n.natAbs = silverBoost ^ m.natAbs := by
      have hlogs : Real.log (goldenBoost ^ n.natAbs)
          = Real.log (silverBoost ^ m.natAbs) := by
        rw [Real.log_pow, Real.log_pow]
        exact habs
      have hg0 : (0 : ℝ) < goldenBoost ^ n.natAbs := pow_pos (by linarith) _
      have hs0 : (0 : ℝ) < silverBoost ^ m.natAbs := pow_pos (by linarith) _
      calc goldenBoost ^ n.natAbs
          = Real.exp (Real.log (goldenBoost ^ n.natAbs)) := (Real.exp_log hg0).symm
        _ = Real.exp (Real.log (silverBoost ^ m.natAbs)) := by rw [hlogs]
        _ = silverBoost ^ m.natAbs := Real.exp_log hs0
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Int.natAbs_ne_zero.mpr hn0)
    obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero (Int.natAbs_ne_zero.mpr hm0)
    rw [hq, hp] at hpow
    exact boosts_incommensurable q p hpow

theorem continuum (q p : ℕ) :
    goldenBoost ^ (q + 1) ≠ silverBoost ^ (p + 1)
      ∧ Dense ((AddSubgroup.closure
          {Real.log goldenBoost, Real.log silverBoost} : AddSubgroup ℝ) : Set ℝ) :=
  ⟨boosts_incommensurable q p, rapidities_dense⟩

/-- info: 'Foam.Bridges.golden_tower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms golden_tower

/-- info: 'Foam.Bridges.silver_tower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms silver_tower

/-- info: 'Foam.Bridges.boosts_incommensurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boosts_incommensurable

/-- info: 'Foam.Bridges.rapidities_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rapidities_dense

/-- info: 'Foam.Bridges.continuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms continuum

end Foam.Bridges
