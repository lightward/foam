import Mathlib.Order.ModularLattice
import Mathlib.Order.Atoms
import Mathlib.Order.KrullDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Length

/-!
# The fundamental theorem of projective geometry — statement, and its deaxiomatization

`ftpg` below is classical FTPG as an axiom: every complemented modular (bounded)
lattice is order-isomorphic to the subspace lattice of a vector space over a
division ring. It is the one imported posit of the classical bridge.

The effort to *discharge* it — construct the division ring and the lattice iso
from the lattice itself, deleting the axiom — lives under `Bridges/FTPG/`, a lift
of the von Staudt / von Neumann coordinatization. State of that effort:

* both hard walls are proven axiom-free-modulo-classical — multiplicative
  associativity (`FTPG/MulAssoc`, `coord_mul_assoc`) and distributivity
  (`FTPG/LeftDistrib`, `FTPG/Distrib`);
* the open frontier is the coordinate ring's additive group (`FTPG/Additive`,
  two named geometric lemmas) and the coordinate map / lattice iso
  (`FTPG/Iso`, `FTPG/Deaxiomatize`).

`h_sufficient : True` marks where the genuine hypothesis (dim ≥ 3 / Arguesian)
belongs: the unrestricted statement is over-strong — the octonion projective
plane is a complemented modular lattice that is not a subspace lattice.
-/

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

theorem subspaceFoamGround (K : Type*) [DivisionRing K]
    (V : Type*) [AddCommGroup V] [Module K V] :
    ComplementedLattice (Submodule K V) ∧ IsModularLattice (Submodule K V) :=
  ⟨inferInstance, inferInstance⟩

/-- info: 'Foam.Bridges.ftpg' depends on axioms: [propext, Quot.sound, ftpg] -/
#guard_msgs in #print axioms ftpg

/-- info: 'Foam.Bridges.dimension_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dimension_unique

/-- info: 'Foam.Bridges.subspaceFoamGround' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subspaceFoamGround

end Foam.Bridges
