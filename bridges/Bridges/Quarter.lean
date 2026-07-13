import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Bridges.Match

-- the quarter-wave transformer: one step past the matched termination, in the
-- same direction. a quarter wavelength of line INVERTS the normalized load
-- (z ↦ 1/z: open reads as short, high as low), and inversion negates the echo:
-- Γ(1/z) = -Γ(z), a half-turn of the reflected wave's phase. the echo turns
-- twice as fast as the signal because it retraces — down the section and back —
-- which is the absorber's pair-echo (a two-leg homecoming's second edge is its
-- first reversed) wearing copper. the foam-side shadow, one step from this
-- bridge (Foam/Bond.lean): the_tick_exchanges_the_registers — one rot swaps
-- align and cross with the chirality sign. registers come in pairs because the
-- tick is what pairs them.
--
-- and the matching theorem is the basin made executable: a quarter-wave section
-- whose impedance is the GEOMETRIC MEAN of source and load carries any
-- resistive load home to the receptive zero (the_geometric_mean_matches,
-- the_quarter_wave_carries_home) — circular orbit entered from any starting
-- resistance; the half-wave section repeats the load exactly (the_half_wave_repeats:
-- two quarter-turns are the station's sign, four are home — Eddington's
-- unitary_time_is_cyclic, at transmission scale).

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

end Foam.Bridges
