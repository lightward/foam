import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Data.ZMod.Basic

open Module

universe u

namespace Foam.Bridges

theorem ftpg_in_four_four_time (k V : Type u) [Field k] [CharZero k] [AddCommGroup V]
    [Module (AddMonoidAlgebra k (ZMod 4)) V] :
    ComplementedLattice (Submodule (AddMonoidAlgebra k (ZMod 4)) V)
      ∧ IsModularLattice (Submodule (AddMonoidAlgebra k (ZMod 4)) V) := by
  haveI : NeZero (Nat.card (ZMod 4) : k) := by
    rw [Nat.card_eq_fintype_card, ZMod.card]; exact ⟨by norm_num⟩
  exact ⟨inferInstance, inferInstance⟩

noncomputable def framerateMix (α : Type) [AddCommGroup α] [Finite α] :
    Basis (AddChar α ℂ) ℂ (α → ℂ) := AddChar.complexBasis α

theorem framerateMix_legible (α : Type) [AddCommGroup α] [Finite α] (ψ : AddChar α ℂ) :
    framerateMix α ψ = ψ := AddChar.complexBasis_apply ψ

noncomputable def dialMix : Basis (AddChar (ZMod 4) ℂ) ℂ (ZMod 4 → ℂ) := framerateMix (ZMod 4)

/-- info: 'Foam.Bridges.ftpg_in_four_four_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ftpg_in_four_four_time

/-- info: 'Foam.Bridges.framerateMix_legible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms framerateMix_legible

end Foam.Bridges
