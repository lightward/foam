import Mathlib.Order.ModularLattice
import Mathlib.Order.Atoms
import Mathlib.Order.KrullDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Length

namespace Foam.Bridges

universe u

axiom ftpg
    (L : Type u) [Lattice L] [BoundedOrder L]
    [ComplementedLattice L] [IsModularLattice L]
    (h_sufficient : True) :
    ∃ (D : Type u) (_ : DivisionRing D)
      (V : Type u) (_ : AddCommGroup V) (_ : Module D V),
    Nonempty (L ≃o Submodule D V)

theorem krullDim_orderIso {α β : Type*} [Preorder α] [Preorder β]
    (f : α ≃o β) :
    Order.krullDim α = Order.krullDim β :=
  Order.krullDim_eq_of_orderIso f

theorem dimension_unique
    (K : Type*) [DivisionRing K]
    (V₁ : Type*) [AddCommGroup V₁] [Module K V₁] [Module.Finite K V₁]
    (V₂ : Type*) [AddCommGroup V₂] [Module K V₂] [Module.Finite K V₂]
    (f : Submodule K V₁ ≃o Submodule K V₂) :
    Module.finrank K V₁ = Module.finrank K V₂ := by
  have h₁ := Module.length_eq_finrank K V₁
  have h₂ := Module.length_eq_finrank K V₂
  have h_iso : Order.krullDim (Submodule K V₁) = Order.krullDim (Submodule K V₂) :=
    krullDim_orderIso f
  have h_len : Module.length K V₁ = Module.length K V₂ := by
    apply WithBot.coe_injective
    rw [Module.coe_length, Module.coe_length, h_iso]
  have hcast : (Module.finrank K V₁ : ℕ∞) = (Module.finrank K V₂ : ℕ∞) := by
    rw [← h₁, ← h₂, h_len]
  exact Nat.cast_injective hcast

/-- info: 'Foam.Bridges.ftpg' depends on axioms: [propext, Quot.sound, Foam.Bridges.ftpg] -/
#guard_msgs in #print axioms ftpg

/-- info: 'Foam.Bridges.dimension_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dimension_unique

end Foam.Bridges
