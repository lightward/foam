import Bridges.Mul
import Bridges.MulKeyIdentity
import Bridges.Dilation
import Bridges.Inverse

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

theorem dilation_compose_at_beta_x_eq_I (Γ : CoordSystem L)
    (y a : L) (hy : IsAtom y) (ha : IsAtom a)
    (hy_on : y ≤ Γ.O ⊔ Γ.U) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hy_ne_U : y ≠ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    dilation_ext Γ y (dilation_ext Γ Γ.I ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E))) =
      dilation_ext Γ (coord_mul Γ Γ.I y) ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) := by

  set βa := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) with hβa_def
  have hβa_atom : IsAtom βa := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hβa_plane : βa ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := beta_plane Γ ha_on
  have hβa_not_l : ¬ βa ≤ Γ.O ⊔ Γ.U := beta_not_l Γ ha ha_on ha_ne_O ha_ne_U

  have h_inner : dilation_ext Γ Γ.I βa = βa :=
    dilation_ext_identity Γ hβa_atom hβa_plane hβa_not_l

  have h_Iy : coord_mul Γ Γ.I y = y := coord_mul_left_one Γ y hy hy_on hy_ne_U
  rw [h_inner, h_Iy]

theorem dilation_compose_at_beta_y_eq_coord_inv_x (Γ : CoordSystem L)
    (x a : L) (hx : IsAtom x) (ha : IsAtom a)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (ha_ne_O : a ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    dilation_ext Γ (coord_inv Γ x)
        (dilation_ext Γ x ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E))) =
      dilation_ext Γ (coord_mul Γ x (coord_inv Γ x))
        ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) := by

  have h_xy_eq_I : coord_mul Γ x (coord_inv Γ x) = Γ.I :=
    coord_mul_right_inv Γ hx hx_on hx_ne_O hx_ne_U
  rw [h_xy_eq_I]
  set βa := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) with hβa_def
  have hβa_atom : IsAtom βa := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hβa_plane : βa ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := beta_plane Γ ha_on
  have hβa_not_l : ¬ βa ≤ Γ.O ⊔ Γ.U := beta_not_l Γ ha ha_on ha_ne_O ha_ne_U
  have h_RHS : dilation_ext Γ Γ.I βa = βa :=
    dilation_ext_identity Γ hβa_atom hβa_plane hβa_not_l
  rw [h_RHS]

  sorry

end Foam.Bridges
