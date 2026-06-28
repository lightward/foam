import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

namespace Foam.Bridges

theorem dial_coordinatizes {K : Type} [Field K] (I : K) (hI : I ^ 2 = -1) (h2 : (2 : K) ≠ 0) :
    (Matrix.vandermonde ![1, I, -1, -I]).det ≠ 0 := by
  rw [Matrix.det_vandermonde_ne_zero_iff]
  have h1m1 : (1 : K) ≠ -1 := fun h => h2 (by linear_combination h)
  have hI1 : I ≠ 1 := fun h => h1m1 (by linear_combination hI - (I + 1) * h)
  have hI2 : I ≠ -1 := fun h => h1m1 (by linear_combination hI - (I - 1) * h)
  have hII : I ≠ -I := fun h => by
    have hz : I = 0 := by
      rcases mul_eq_zero.mp (show (2 : K) * I = 0 by linear_combination h) with h' | h'
      · exact absurd h' h2
      · exact h'
    exact h2 (by rw [hz] at hI; linear_combination 2 * hI)
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      eq_comm, neg_eq_iff_eq_neg]

/-- info: 'Foam.Bridges.dial_coordinatizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dial_coordinatizes

end Foam.Bridges
