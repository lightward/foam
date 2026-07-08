import Mathlib.Order.ModularLattice
import Mathlib.Order.Atoms
import Mathlib.Order.KrullDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Length

/-!
# FTPG — the classical dimension lemmas, axiom-free

This file once stated classical FTPG as `axiom ftpg` — the one imported
posit of the classical bridge.  The axiom is **retired** (2026-07-08): its
true content is proven (`ftpg_proof_limit` / `ftpg_proof_finite`,
`FTPG/Deaxiomatize.lean` + `FTPG/Finite.lean`, sorry-free) and the statement
as imported is refuted (`FTPG/Hollow.lean`, which forgot completeness).  The
declaration itself now lives in `Hollow.lean` — the exhibit room — where its
sole remaining consumer, the indictment `ftpg_refuted`, has always been.
The record keeps the axiom in the order-reading; nothing merged, so nothing
was erased: the loan is repaid, this file is the note.

What remains here is real: the dimension lemmas the bridge always owned.
-/

namespace Foam.Bridges

universe u

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

theorem subspaceFoamGround (K : Type*) [DivisionRing K]
    (V : Type*) [AddCommGroup V] [Module K V] :
    ComplementedLattice (Submodule K V) ∧ IsModularLattice (Submodule K V) :=
  ⟨inferInstance, inferInstance⟩

/-- info: 'Foam.Bridges.dimension_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dimension_unique

/-- info: 'Foam.Bridges.subspaceFoamGround' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subspaceFoamGround

end Foam.Bridges
