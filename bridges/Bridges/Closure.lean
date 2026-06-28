import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul

namespace Foam.Bridges

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem conjugation_preserves_idempotent
    {R : Type*} [CommRing R]
    (P U Uinv : Matrix n n R)
    (hP : P * P = P)
    (_hUinv : U * Uinv = 1) (hUinv' : Uinv * U = 1) :
    (U * P * Uinv) * (U * P * Uinv) = U * P * Uinv := by
  calc (U * P * Uinv) * (U * P * Uinv)
      = U * P * (Uinv * U) * P * Uinv := by simp only [Matrix.mul_assoc]
    _ = U * P * 1 * P * Uinv := by rw [hUinv']
    _ = U * P * P * Uinv := by rw [Matrix.mul_one]
    _ = U * (P * P) * Uinv := by simp only [Matrix.mul_assoc]
    _ = U * P * Uinv := by rw [hP]

theorem orthogonal_conjugation_preserves_symmetric
    {R : Type*} [CommRing R]
    (P U : Matrix n n R)
    (hP_symm : Pᵀ = P)
    (_hU_orth : Uᵀ * U = 1) :
    (U * P * Uᵀ)ᵀ = U * P * Uᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hP_symm, Matrix.mul_assoc]

theorem observation_preserved_by_dynamics
    {R : Type*} [CommRing R]
    (P U : Matrix n n R)
    (hP_idem : P * P = P)
    (hP_symm : Pᵀ = P)
    (hU_orth : Uᵀ * U = 1)
    (hU_orth' : U * Uᵀ = 1) :
    (U * P * Uᵀ) * (U * P * Uᵀ) = U * P * Uᵀ ∧
      (U * P * Uᵀ)ᵀ = U * P * Uᵀ :=
  ⟨conjugation_preserves_idempotent P U Uᵀ hP_idem hU_orth' hU_orth,
   orthogonal_conjugation_preserves_symmetric P U hP_symm hU_orth⟩

/-- info: 'Foam.Bridges.conjugation_preserves_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conjugation_preserves_idempotent

/-- info: 'Foam.Bridges.observation_preserved_by_dynamics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms observation_preserved_by_dynamics

end Foam.Bridges
