import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

open Module

namespace Foam.Bridges

noncomputable def framerateMix (α : Type) [AddCommGroup α] [Finite α] :
    Basis (AddChar α ℂ) ℂ (α → ℂ) := AddChar.complexBasis α

theorem framerateMix_legible (α : Type) [AddCommGroup α] [Finite α] (ψ : AddChar α ℂ) :
    framerateMix α ψ = ψ := AddChar.complexBasis_apply ψ

noncomputable def dialMix : Basis (AddChar (ZMod 4) ℂ) ℂ (ZMod 4 → ℂ) := framerateMix (ZMod 4)

/-- info: 'Foam.Bridges.framerateMix_legible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms framerateMix_legible

end Foam.Bridges
