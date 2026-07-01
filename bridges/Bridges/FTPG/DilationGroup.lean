import Bridges.FTPG.Dilation
import Bridges.FTPG.Inverse

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

structure Dilation (Γ : CoordSystem L) where

  toOrderIso : L ≃o L

  fixes_O : toOrderIso Γ.O = Γ.O

  preserves_l : toOrderIso (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U

  fixes_m : ∀ P : L, IsAtom P → P ≤ Γ.U ⊔ Γ.V → toOrderIso P = P

namespace Dilation

variable {Γ : CoordSystem L}

@[ext]
theorem ext {f g : Dilation Γ} (h : f.toOrderIso = g.toOrderIso) : f = g := by
  cases f
  cases g
  congr

def id (Γ : CoordSystem L) : Dilation Γ where
  toOrderIso := OrderIso.refl L
  fixes_O := rfl
  preserves_l := rfl
  fixes_m := fun _ _ _ => rfl

def comp (f g : Dilation Γ) : Dilation Γ where
  toOrderIso := f.toOrderIso.trans g.toOrderIso
  fixes_O := by

    simp [OrderIso.trans_apply, f.fixes_O, g.fixes_O]
  preserves_l := by

    rw [OrderIso.trans_apply, f.preserves_l, g.preserves_l]
  fixes_m := by
    intro P hP_atom hP_le

    simp [OrderIso.trans_apply, f.fixes_m P hP_atom hP_le,
          g.fixes_m P hP_atom hP_le]

instance : Mul (Dilation Γ) := ⟨comp⟩

instance : One (Dilation Γ) := ⟨id Γ⟩

instance : Monoid (Dilation Γ) where
  mul := comp
  one := id Γ
  mul_assoc f g h := by
    ext
    rfl
  one_mul f := by
    ext
    rfl
  mul_one f := by
    ext
    rfl

end Dilation

noncomputable def σ_toFun (Γ : CoordSystem L) (c : L) (P : L) : L := by
  classical
  exact
    if P ≤ Γ.O ⊔ Γ.U then coord_mul Γ P c
    else if P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V then dilation_ext Γ c P
    else P

noncomputable def σ_invFun (Γ : CoordSystem L) (c : L) (P : L) : L := by
  classical
  exact
    if P ≤ Γ.O ⊔ Γ.U then coord_mul Γ P (coord_inv Γ c)
    else if P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V then dilation_ext Γ (coord_inv Γ c) P
    else P

private theorem dg_E_sup_EI (Γ : CoordSystem L) : Γ.E ⊔ Γ.E_I = Γ.U ⊔ Γ.V := by
  have hE_lt : Γ.E < Γ.E ⊔ Γ.E_I :=
    lt_of_le_of_ne le_sup_left (fun h => Γ.hE_I_ne_E
      ((Γ.hE_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_I_atom.1))
  have hE_covBy_m : Γ.E ⋖ Γ.U ⊔ Γ.V := by
    rw [← CoordSystem.EU_eq_m]
    exact atom_covBy_join Γ.hE_atom Γ.hU CoordSystem.hEU
  exact (hE_covBy_m.eq_or_eq hE_lt.le
    (sup_le CoordSystem.hE_on_m Γ.hE_I_on_m)).resolve_left (ne_of_gt hE_lt)

private theorem dg_sigma_atom (Γ : CoordSystem L) (c : L) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_U : c ≠ Γ.U) :
    IsAtom ((Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I)) := by
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hc_ne_EI : c ≠ Γ.E_I := fun h =>
    hc_ne_U (Γ.atom_on_both_eq_U hc hc_on (h ▸ Γ.hE_I_on_m))
  rw [inf_comm]
  have hEI_sup_OC : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h_lt : Γ.O ⊔ Γ.C < Γ.E_I ⊔ (Γ.O ⊔ Γ.C) :=
      lt_of_le_of_ne le_sup_right (fun h => Γ.hE_I_not_OC (h ▸ le_sup_left))
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
      (sup_le (Γ.hE_I_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
        (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane))).resolve_left (ne_of_gt h_lt)
  have h_coplanar : c ⊔ Γ.E_I ≤ (Γ.O ⊔ Γ.C) ⊔ Γ.E_I := by
    rw [sup_comm (Γ.O ⊔ Γ.C) Γ.E_I, hEI_sup_OC]
    exact sup_le (hc_on.trans le_sup_left)
      (Γ.hE_I_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  exact perspect_atom Γ.hE_I_atom hc hc_ne_EI Γ.hO Γ.hC hOC Γ.hE_I_not_OC h_coplanar

/-- σ_c fixes the point U: `coord_mul Γ Γ.U c = Γ.U`. -/
theorem coord_mul_U_left (Γ : CoordSystem L) (c : L) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U) :
    coord_mul Γ Γ.U c = Γ.U := by
  unfold coord_mul
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hCV : Γ.C ≠ Γ.V := fun h => Γ.hC_not_m (h ▸ le_sup_right)
  have hV_not_UC : ¬ Γ.V ≤ Γ.U ⊔ Γ.C := by
    intro h
    have h_le : Γ.U ⊔ Γ.V ≤ Γ.U ⊔ Γ.C := sup_le le_sup_left h
    have h_eq := ((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
      (atom_covBy_join Γ.hU Γ.hV hUV).lt.le h_le).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hU Γ.hV hUV).lt)
    exact Γ.hC_not_m (le_sup_right.trans h_eq.symm.le)
  have hUCUV : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U :=
    modular_intersection Γ.hU Γ.hC Γ.hV hUC hUV hCV hV_not_UC
  rw [hUCUV]
  set σc := (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) with hσc
  have hσ_atom : IsAtom σc := dg_sigma_atom Γ c hc hc_on hc_ne_U
  have hσ_le_OC : σc ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσ_le_cEI : σc ≤ c ⊔ Γ.E_I := inf_le_right
  have hEI_ne_O : Γ.E_I ≠ Γ.O := fun h => Γ.hO_not_m (h ▸ Γ.hE_I_on_m)
  have hc_ne_EI : c ≠ Γ.E_I := fun h =>
    hc_ne_U (Γ.atom_on_both_eq_U hc hc_on (h ▸ Γ.hE_I_on_m))
  have hσ_ne_U : σc ≠ Γ.U := by
    intro h
    have hU_le_OC : Γ.U ≤ Γ.O ⊔ Γ.C := h ▸ hσ_le_OC
    have h_le : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left hU_le_OC
    have h_eq := ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
      (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le h_le).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)
    exact Γ.hC_not_l (le_sup_right.trans h_eq.symm.le)
  have hσ_ne_O : σc ≠ Γ.O := by
    intro h
    have hO_le : Γ.O ≤ c ⊔ Γ.E_I := h ▸ hσ_le_cEI
    have h_eq : c ⊔ Γ.E_I = c ⊔ Γ.O :=
      line_eq_of_atom_le hc Γ.hE_I_atom Γ.hO hc_ne_EI hc_ne_O hEI_ne_O hO_le
    have hEI_le_l : Γ.E_I ≤ Γ.O ⊔ Γ.U := by
      have : Γ.E_I ≤ c ⊔ Γ.O := h_eq ▸ (le_sup_right : Γ.E_I ≤ c ⊔ Γ.E_I)
      exact this.trans (sup_le hc_on le_sup_left)
    exact Γ.hE_I_not_l hEI_le_l
  have hOUOC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
    modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU hOC hUC Γ.hC_not_l
  have hO_not : ¬ Γ.O ≤ Γ.U ⊔ σc := by
    intro hO_le
    have h_le : Γ.U ⊔ Γ.O ≤ Γ.U ⊔ σc := sup_le le_sup_left hO_le
    have h_eq := ((atom_covBy_join Γ.hU hσ_atom hσ_ne_U.symm).eq_or_eq
      (atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).lt.le h_le).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).lt)
    have hσ_le_l : σc ≤ Γ.O ⊔ Γ.U := by
      have : σc ≤ Γ.U ⊔ Γ.O := h_eq.symm ▸ (le_sup_right : σc ≤ Γ.U ⊔ σc)
      exact this.trans (by rw [sup_comm])
    have hσ_le_O : σc ≤ Γ.O := hOUOC ▸ le_inf hσ_le_l hσ_le_OC
    exact hσ_ne_O ((Γ.hO.le_iff.mp hσ_le_O).resolve_left hσ_atom.1)
  rw [sup_comm σc Γ.U, sup_comm Γ.O Γ.U]
  exact modular_intersection Γ.hU hσ_atom Γ.hO hσ_ne_U.symm Γ.hOU.symm hσ_ne_O hO_not

/-- σ_c sends the line l = O⊔U to itself: `coord_mul Γ (Γ.O ⊔ Γ.U) c = Γ.O ⊔ Γ.U`. -/
theorem coord_mul_l_left (Γ : CoordSystem L) (c : L) (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_U : c ≠ Γ.U) :
    coord_mul Γ (Γ.O ⊔ Γ.U) c = Γ.O ⊔ Γ.U := by
  unfold coord_mul
  have hm_le_π : Γ.U ⊔ Γ.V ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hl_cov : (Γ.O ⊔ Γ.U) ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  have hlC : (Γ.O ⊔ Γ.U) ⊔ Γ.C = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ Γ.C :=
      lt_of_le_of_ne le_sup_left (fun h => Γ.hC_not_l (h ▸ le_sup_right))
    exact (hl_cov.eq_or_eq h_lt.le (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt)
  rw [hlC, inf_eq_right.mpr hm_le_π]
  have hσ_atom : IsAtom ((Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I)) := dg_sigma_atom Γ c hc hc_on hc_ne_U
  have hσ_le_OC : (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσ_le_cEI : (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) ≤ c ⊔ Γ.E_I := inf_le_right
  have hc_ne_EI : c ≠ Γ.E_I := fun h =>
    hc_ne_U (Γ.atom_on_both_eq_U hc hc_on (h ▸ Γ.hE_I_on_m))
  have hE_sup_EI : Γ.E ⊔ Γ.E_I = Γ.U ⊔ Γ.V := dg_E_sup_EI Γ
  have hσ_not_m : ¬ ((Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I)) ≤ Γ.U ⊔ Γ.V := by
    intro h
    have hσ_le_E : (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) ≤ Γ.E := by
      show _ ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
      exact le_inf hσ_le_OC h
    have hσ_eq_E : (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) = Γ.E :=
      (Γ.hE_atom.le_iff.mp hσ_le_E).resolve_left hσ_atom.1
    have hE_le : Γ.E ≤ c ⊔ Γ.E_I := hσ_eq_E ▸ hσ_le_cEI
    have hm_le : Γ.U ⊔ Γ.V ≤ c ⊔ Γ.E_I := by
      rw [← hE_sup_EI]; exact sup_le hE_le le_sup_right
    have hEI_cov : Γ.E_I ⋖ c ⊔ Γ.E_I := by
      rw [sup_comm]; exact atom_covBy_join Γ.hE_I_atom hc (Ne.symm hc_ne_EI)
    have hEI_lt_m : Γ.E_I < Γ.U ⊔ Γ.V :=
      (line_covers_its_atoms Γ.hU Γ.hV hUV Γ.hE_I_atom Γ.hE_I_on_m).lt
    have hm_eq : Γ.U ⊔ Γ.V = c ⊔ Γ.E_I :=
      (hEI_cov.eq_or_eq hEI_lt_m.le hm_le).resolve_left (ne_of_gt hEI_lt_m)
    have hc_le_m : c ≤ Γ.U ⊔ Γ.V := hm_eq.symm ▸ (le_sup_left : c ≤ c ⊔ Γ.E_I)
    exact hc_ne_U (Γ.atom_on_both_eq_U hc hc_on hc_le_m)
  have hσ_sup_m : (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) ⊔ (Γ.U ⊔ Γ.V) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h_lt : Γ.U ⊔ Γ.V < (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) ⊔ (Γ.U ⊔ Γ.V) :=
      lt_of_le_of_ne le_sup_right (fun h => by
        apply hσ_not_m
        calc (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I)
            ≤ (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) ⊔ (Γ.U ⊔ Γ.V) := le_sup_left
          _ = Γ.U ⊔ Γ.V := h.symm)
    exact (Γ.m_covBy_π.eq_or_eq h_lt.le
      (sup_le (hσ_le_OC.trans (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane))
        hm_le_π)).resolve_left (ne_of_gt h_lt)
  rw [hσ_sup_m]
  exact inf_eq_right.mpr le_sup_left

noncomputable def σ (Γ : CoordSystem L) (c : L)
    (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U) :
    Dilation Γ where
  toOrderIso :=
    { toFun := σ_toFun Γ c
      invFun := σ_invFun Γ c
      left_inv := by

        sorry
      right_inv := by

        sorry
      map_rel_iff' := by

        sorry }
  fixes_O := by

    show σ_toFun Γ c Γ.O = Γ.O
    unfold σ_toFun
    classical
    simp only [le_sup_left, if_true]
    exact coord_mul_left_zero Γ c hc hc_on hc_ne_U
  preserves_l := by
    show σ_toFun Γ c (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U
    unfold σ_toFun
    classical
    simp only [le_refl, if_true]
    exact coord_mul_l_left Γ c hc hc_on hc_ne_U
  fixes_m := by
    intro P hP hP_on_m

    show σ_toFun Γ c P = P
    unfold σ_toFun
    classical
    by_cases hP_on_l : P ≤ Γ.O ⊔ Γ.U
    · simp only [hP_on_l, if_true]

      have hP_eq_U : P = Γ.U := Γ.atom_on_both_eq_U hP hP_on_l hP_on_m
      subst hP_eq_U
      exact coord_mul_U_left Γ c hc hc_on hc_ne_O hc_ne_U
    · simp only [hP_on_l, if_false]
      have hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
        hP_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
      simp only [hP_plane, if_true]
      exact dilation_ext_fixes_m Γ hc hP hc_on hP_on_m hc_ne_O hP_on_l

theorem σ_mul (Γ : CoordSystem L) (a b : L)
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : IsAtom (coord_mul Γ a b))
    (hab_on : coord_mul Γ a b ≤ Γ.O ⊔ Γ.U)
    (hab_ne_O : coord_mul Γ a b ≠ Γ.O)
    (hab_ne_U : coord_mul Γ a b ≠ Γ.U) :
    σ Γ (coord_mul Γ a b) hab hab_on hab_ne_O hab_ne_U =
      σ Γ a ha ha_on ha_ne_O ha_ne_U * σ Γ b hb hb_on hb_ne_O hb_ne_U :=
  sorry

theorem σ_add_pointwise (Γ : CoordSystem L) (a b : L)
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : IsAtom (coord_add Γ a b))
    (hab_on : coord_add Γ a b ≤ Γ.O ⊔ Γ.U)
    (hab_ne_O : coord_add Γ a b ≠ Γ.O)
    (hab_ne_U : coord_add Γ a b ≠ Γ.U)
    (P : L) :
    (σ Γ (coord_add Γ a b) hab hab_on hab_ne_O hab_ne_U).toOrderIso P =
      coord_add Γ
        ((σ Γ a ha ha_on ha_ne_O ha_ne_U).toOrderIso P)
        ((σ Γ b hb hb_on hb_ne_O hb_ne_U).toOrderIso P) :=
  sorry

end Foam.Bridges
