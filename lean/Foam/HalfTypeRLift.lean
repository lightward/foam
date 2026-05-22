/-
# R-lift as HalfType iso (s149 probe)

Tests whether the classical Hartshorne R-lift — the dimensional lift
through a height-≥-4 witness R off the plane π — is structurally a
HalfType iso.

Argument: in `Set.Iic (π ⊔ R)`, the pair `(⟨π, _⟩, ⟨R, _⟩)` is
complementary when `π ⊓ R = ⊥` (R off π). The HalfType iso for this
pair sends `Iic π ≃o Ici R` *within that interval* — which is exactly
"take a planar element, send it to its join with R" up to the
HalfType iso's exact direction.

If this builds, the s148 "joint hasn't been concretely walked" for
`dilation_compose_at_beta` becomes "the joint is
`IsCompl.IicOrderIsoIci` applied to (π, R) in `Iic (π ⊔ R)`, which
iterated-HalfType is bin-1-Mathlib."

If it fails, the failure surfaces what's blocking — possibly a
missing subtype-lattice lemma, possibly a deeper structural gap.
-/

import Foam.HalfType

namespace Foam

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
    [IsModularLattice L] [ComplementedLattice L]

/-! ## The (π, R)-complementary pair in `Iic (π ⊔ R)`. -/

/-- Given `π R : L` with `π ⊓ R = ⊥`, the elements
    `⟨π, le_sup_left⟩` and `⟨R, le_sup_right⟩` of `Set.Iic (π ⊔ R)`
    form a complementary pair within the interval. -/
example (π R : L) (h_disjoint : Disjoint π R) :
    IsCompl (⟨π, le_sup_left⟩ : Set.Iic (π ⊔ R))
            (⟨R, le_sup_right⟩ : Set.Iic (π ⊔ R)) := by
  constructor
  · -- Disjoint in the subtype: meet ≤ bot
    intro z hz_pi hz_R
    -- z ≤ π and z ≤ R as Iic elements
    -- z.val ≤ π and z.val ≤ R, so z.val ≤ π ⊓ R = ⊥
    show z ≤ ⊥
    exact le_inf hz_pi hz_R |>.trans (h_disjoint.le_bot.trans bot_le) |>.trans bot_le
  · -- Codisjoint in the subtype: join ≥ top
    intro z hz_pi hz_R
    -- top is ⟨π ⊔ R, le_refl⟩; z ≥ π and z ≥ R as Iic elements means z.val ≥ π ⊔ R
    show ⊤ ≤ z
    exact sup_le hz_pi hz_R

/-! ## R-lift as HalfType. -/

example (π R : L) (h_disjoint : Disjoint π R) :
    HalfType (⟨π, le_sup_left⟩ : Set.Iic (π ⊔ R))
             (⟨R, le_sup_right⟩ : Set.Iic (π ⊔ R))
             (by
                constructor
                · intro z hz_pi hz_R
                  show z ≤ ⊥
                  exact le_inf hz_pi hz_R |>.trans (h_disjoint.le_bot.trans bot_le) |>.trans bot_le
                · intro z hz_pi hz_R
                  show ⊤ ≤ z
                  exact sup_le hz_pi hz_R) :=
  half_type _

end Foam
