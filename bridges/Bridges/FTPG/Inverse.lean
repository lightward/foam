import Bridges.FTPG.Mul

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

noncomputable def coord_inv (Γ : CoordSystem L) (a : L) : L :=
  ((Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U)

theorem coord_inv_on_l (Γ : CoordSystem L) (a : L) :
    coord_inv Γ a ≤ Γ.O ⊔ Γ.U := by
  unfold coord_inv; exact inf_le_right

private theorem l_covBy_π_inv (Γ : CoordSystem L) :
    (Γ.O ⊔ Γ.U) ⋖ (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
  have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
    (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
  have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
  rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this

private theorem d_a_atom (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    IsAtom ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by
  have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  exact perspect_atom Γ.hC ha hAC Γ.hU Γ.hV hUV Γ.hC_not_m
    (sup_le (ha_on.trans (le_sup_left.trans Γ.m_sup_C_eq_π.symm.le)) le_sup_right)

private theorem d_a_not_l (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    ¬ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U := by
  intro h
  have hd := d_a_atom Γ ha ha_on
  have hd_eq_U := Γ.atom_on_both_eq_U hd h inf_le_right
  have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := hd_eq_U.symm.le.trans inf_le_left
  have h_la_inf : (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) = a := by
    rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on
  have hU_le : Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) := le_inf le_sup_right hU_le_aC
  rw [h_la_inf] at hU_le
  exact ha_ne_U ((ha.le_iff.mp hU_le).resolve_left Γ.hU.1).symm

private theorem d_a_ne_E (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) :
    (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠ Γ.E := by
  intro hd_eq_E
  have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := hd_eq_E.symm.le.trans inf_le_left

  have hE_ne_C : Γ.E ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hC_lt : Γ.C < Γ.E ⊔ Γ.C := lt_of_le_of_ne le_sup_right
    (fun h => hE_ne_C ((Γ.hC.le_iff.mp
      (le_sup_left.trans h.symm.le)).resolve_left Γ.hE_atom.1))
  have hEC_le_OC : Γ.E ⊔ Γ.C ≤ Γ.O ⊔ Γ.C := sup_le CoordSystem.hE_le_OC le_sup_right
  have hcov_C : Γ.C ⋖ Γ.O ⊔ Γ.C := by
    have := atom_covBy_join Γ.hC Γ.hO hOC.symm
    rwa [sup_comm] at this
  have hEC_eq_OC : Γ.E ⊔ Γ.C = Γ.O ⊔ Γ.C :=
    (hcov_C.eq_or_eq hC_lt.le hEC_le_OC).resolve_left (ne_of_gt hC_lt)
  have hEC_le_aC : Γ.E ⊔ Γ.C ≤ a ⊔ Γ.C := sup_le hE_le_aC le_sup_right
  have hOC_le_aC : Γ.O ⊔ Γ.C ≤ a ⊔ Γ.C := hEC_eq_OC ▸ hEC_le_aC
  have hO_le_aC : Γ.O ≤ a ⊔ Γ.C := le_sup_left.trans hOC_le_aC
  have h_la_inf : (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) = a := by
    rw [show a ⊔ Γ.C = Γ.C ⊔ a from sup_comm _ _]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on
  have hO_le : Γ.O ≤ (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) := le_inf le_sup_left hO_le_aC
  rw [h_la_inf] at hO_le
  exact ha_ne_O ((ha.le_iff.mp hO_le).resolve_left Γ.hO.1).symm

private theorem I_ne_d_a (Γ : CoordSystem L)
    {a : L} (_ha : IsAtom a) (_ha_on : a ≤ Γ.O ⊔ Γ.U) :
    Γ.I ≠ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  intro h
  have hI_le_m : Γ.I ≤ Γ.U ⊔ Γ.V := h.symm ▸ inf_le_right
  have hI_le_lm : Γ.I ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) := le_inf Γ.hI_on hI_le_m
  rw [Γ.l_inf_m_eq_U] at hI_le_lm
  exact Γ.hUI ((Γ.hU.le_iff.mp hI_le_lm).resolve_left Γ.hI.1).symm

private theorem hI_not_OC (Γ : CoordSystem L) : ¬ Γ.I ≤ Γ.O ⊔ Γ.C := by
  intro h
  have hI_le : Γ.I ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) := le_inf Γ.hI_on h
  rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _,
      inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)] at hI_le
  exact Γ.hOI ((Γ.hO.le_iff.mp hI_le).resolve_left Γ.hI.1).symm

private theorem sigma'_atom (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    IsAtom ((Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V))) := by
  have hd := d_a_atom Γ ha ha_on
  have hI_ne_d := I_ne_d_a Γ ha ha_on
  have hId_le_π : Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (Γ.hI_on.trans le_sup_left)
      (inf_le_right.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  rw [show (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) =
      (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _]
  exact line_meets_m_at_atom Γ.hI hd hI_ne_d hId_le_π
    (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane)
    (CoordSystem.OC_covBy_π Γ) (hI_not_OC Γ)

private theorem sigma'_ne_E_I (Γ : CoordSystem L) (a : L) :
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≠ Γ.E_I :=
  fun h => Γ.hE_I_not_OC (h ▸ inf_le_left)

private theorem sigma'_ne_O (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≠ Γ.O := by
  intro h
  have hO_le_Id : Γ.O ≤ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := h.symm ▸ inf_le_right

  have hIO_eq_l : Γ.I ⊔ Γ.O = Γ.O ⊔ Γ.U := by
    have hIO_le : Γ.I ⊔ Γ.O ≤ Γ.O ⊔ Γ.U := sup_le Γ.hI_on le_sup_left
    have hI_lt : Γ.I < Γ.I ⊔ Γ.O := lt_of_le_of_ne le_sup_left
      (fun heq => Γ.hOI ((Γ.hI.le_iff.mp
        (le_sup_right.trans heq.symm.le)).resolve_left Γ.hO.1))
    exact ((line_covers_its_atoms Γ.hO Γ.hU Γ.hOU Γ.hI Γ.hI_on).eq_or_eq
      hI_lt.le hIO_le).resolve_left (ne_of_gt hI_lt)
  have hl_le_Id : Γ.O ⊔ Γ.U ≤ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
    rw [← hIO_eq_l]; exact sup_le le_sup_left hO_le_Id
  have hU_le_Id : Γ.U ≤ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := le_sup_right.trans hl_le_Id

  have hId_inf_m : (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.U ⊔ Γ.V) =
      (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    line_direction Γ.hI Γ.hI_not_m inf_le_right
  have hU_le_inf : Γ.U ≤ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.U ⊔ Γ.V) :=
    le_inf hU_le_Id le_sup_left
  rw [hId_inf_m] at hU_le_inf
  have hU_eq_d : Γ.U = (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    ((d_a_atom Γ ha ha_on).le_iff.mp hU_le_inf).resolve_left Γ.hU.1
  exact d_a_not_l Γ ha ha_on ha_ne_U (hU_eq_d.symm.le.trans le_sup_right)

private theorem sigma'_ne_E (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) :
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≠ Γ.E := by
  intro h

  have hE_le_Id : Γ.E ≤ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := h.symm ▸ inf_le_right
  have hId_inf_m : (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.U ⊔ Γ.V) =
      (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    line_direction Γ.hI Γ.hI_not_m inf_le_right
  have hE_le_inf : Γ.E ≤ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.U ⊔ Γ.V) :=
    le_inf hE_le_Id CoordSystem.hE_on_m
  rw [hId_inf_m] at hE_le_inf
  have hd_eq_E : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.E :=
    ((d_a_atom Γ ha ha_on).le_iff.mp hE_le_inf).resolve_left Γ.hE_atom.1 |>.symm
  exact d_a_ne_E Γ ha ha_on ha_ne_O hd_eq_E

private theorem sigma'_ne_C (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_I : a ≠ Γ.I) :
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≠ Γ.C := by
  intro h
  have hC_le_Id : Γ.C ≤ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := h.symm.le.trans inf_le_right
  have hd_atom := d_a_atom Γ ha ha_on
  have hI_ne_C : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hI_ne_d := I_ne_d_a Γ ha ha_on
  have hcov_IC : Γ.I ⋖ Γ.I ⊔ Γ.C := atom_covBy_join Γ.hI Γ.hC hI_ne_C
  have hcov_Id : Γ.I ⋖ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    atom_covBy_join Γ.hI hd_atom hI_ne_d
  have hIC_le_Id : Γ.I ⊔ Γ.C ≤ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    sup_le le_sup_left hC_le_Id
  have hIC_eq : Γ.I ⊔ Γ.C = Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    (hcov_Id.eq_or_eq hcov_IC.lt.le hIC_le_Id).resolve_left (ne_of_gt hcov_IC.lt)
  have hd_le_IC : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.I ⊔ Γ.C :=
    (le_sup_right : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤
      Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)).trans hIC_eq.symm.le
  have hmeet : (a ⊔ Γ.C) ⊓ (Γ.I ⊔ Γ.C) = Γ.C :=
    Γ.lines_through_C_meet ha Γ.hI ha_ne_I ha_on Γ.hI_on
  have hd_le_aC : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ a ⊔ Γ.C := inf_le_left
  have hd_le_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.C :=
    (le_inf hd_le_aC hd_le_IC).trans hmeet.le
  have hd_eq_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.C :=
    (Γ.hC.le_iff.mp hd_le_C).resolve_left hd_atom.1
  exact Γ.hC_not_m
    (hd_eq_C ▸ (inf_le_right : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V))

theorem coord_inv_atom (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    IsAtom (coord_inv Γ a) := by
  unfold coord_inv
  set σ' := (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) with hσ'_def
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have hσ'_ne_EI := sigma'_ne_E_I Γ a
  have hσ'_le_OC : σ' ≤ Γ.O ⊔ Γ.C := inf_le_left

  have hσ'_not_l : ¬ σ' ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hO_inf : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
    have hσ'_le_O : σ' ≤ Γ.O := hO_inf ▸ le_inf h hσ'_le_OC
    have hσ'_eq_O : σ' = Γ.O :=
      (Γ.hO.le_iff.mp hσ'_le_O).resolve_left hσ'_atom.1
    exact sigma'_ne_O Γ ha ha_on ha_ne_U hσ'_eq_O
  have hOC_le_π : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane
  have hσ'EI_le_π : σ' ⊔ Γ.E_I ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (hσ'_le_OC.trans hOC_le_π)
      (Γ.hE_I_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  exact line_meets_m_at_atom hσ'_atom Γ.hE_I_atom hσ'_ne_EI hσ'EI_le_π
    le_sup_left (l_covBy_π_inv Γ) hσ'_not_l

theorem coord_inv_ne_O (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    coord_inv Γ a ≠ Γ.O := by
  unfold coord_inv
  set σ' := (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) with hσ'_def
  intro h
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have hσ'_ne_EI := sigma'_ne_E_I Γ a

  have hO_le_σEI : Γ.O ≤ σ' ⊔ Γ.E_I := h.symm.le.trans inf_le_left

  have hO_ne_EI : Γ.O ≠ Γ.E_I := fun he => Γ.hO_not_m (he ▸ Γ.hE_I_on_m)
  have hOE_le_σE : Γ.O ⊔ Γ.E_I ≤ σ' ⊔ Γ.E_I := sup_le hO_le_σEI le_sup_right
  have hEI_lt_OE : Γ.E_I < Γ.O ⊔ Γ.E_I := lt_of_le_of_ne le_sup_right
    (fun he => hO_ne_EI ((Γ.hE_I_atom.le_iff.mp
      (le_sup_left.trans he.symm.le)).resolve_left Γ.hO.1))
  have hcov_EI : Γ.E_I ⋖ σ' ⊔ Γ.E_I := by
    have := atom_covBy_join Γ.hE_I_atom hσ'_atom (Ne.symm hσ'_ne_EI)
    rwa [sup_comm] at this
  have hOEI_eq : Γ.O ⊔ Γ.E_I = σ' ⊔ Γ.E_I :=
    (hcov_EI.eq_or_eq hEI_lt_OE.le hOE_le_σE).resolve_left (ne_of_gt hEI_lt_OE)

  have hσ'_le_OEI : σ' ≤ Γ.O ⊔ Γ.E_I := hOEI_eq ▸ le_sup_left
  have hσ'_le_OC : σ' ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hC_ne_EI : Γ.C ≠ Γ.E_I := fun h => Γ.hC_not_m (h ▸ Γ.hE_I_on_m)
  have hOC_inf_OEI : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.E_I) = Γ.O :=
    modular_intersection Γ.hO Γ.hC Γ.hE_I_atom hOC hO_ne_EI hC_ne_EI Γ.hE_I_not_OC
  have hσ'_le_O : σ' ≤ Γ.O := hOC_inf_OEI ▸ le_inf hσ'_le_OC hσ'_le_OEI
  have hσ'_eq_O : σ' = Γ.O :=
    (Γ.hO.le_iff.mp hσ'_le_O).resolve_left hσ'_atom.1
  exact sigma'_ne_O Γ ha ha_on ha_ne_U hσ'_eq_O

theorem coord_inv_ne_U (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_O : a ≠ Γ.O) :
    coord_inv Γ a ≠ Γ.U := by
  unfold coord_inv
  set σ' := (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) with hσ'_def
  intro h
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have hσ'_ne_EI := sigma'_ne_E_I Γ a

  have hU_le_σEI : Γ.U ≤ σ' ⊔ Γ.E_I := h.symm.le.trans inf_le_left

  have hU_ne_EI : Γ.U ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ le_sup_right)
  have hUE_le_σE : Γ.U ⊔ Γ.E_I ≤ σ' ⊔ Γ.E_I := sup_le hU_le_σEI le_sup_right
  have hEI_lt_UE : Γ.E_I < Γ.U ⊔ Γ.E_I := lt_of_le_of_ne le_sup_right
    (fun he => hU_ne_EI ((Γ.hE_I_atom.le_iff.mp
      (le_sup_left.trans he.symm.le)).resolve_left Γ.hU.1))
  have hcov_EI : Γ.E_I ⋖ σ' ⊔ Γ.E_I := by
    have := atom_covBy_join Γ.hE_I_atom hσ'_atom (Ne.symm hσ'_ne_EI)
    rwa [sup_comm] at this
  have hUEI_eq : Γ.U ⊔ Γ.E_I = σ' ⊔ Γ.E_I :=
    (hcov_EI.eq_or_eq hEI_lt_UE.le hUE_le_σE).resolve_left (ne_of_gt hEI_lt_UE)

  have hσ'_le_UEI : σ' ≤ Γ.U ⊔ Γ.E_I := hUEI_eq ▸ le_sup_left
  have hUEI_le_m : Γ.U ⊔ Γ.E_I ≤ Γ.U ⊔ Γ.V :=
    sup_le le_sup_left Γ.hE_I_on_m
  have hσ'_le_m : σ' ≤ Γ.U ⊔ Γ.V := hσ'_le_UEI.trans hUEI_le_m
  have hσ'_le_OC : σ' ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσ'_le_E : σ' ≤ Γ.E := by
    show σ' ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
    exact le_inf hσ'_le_OC hσ'_le_m
  have hσ'_eq_E : σ' = Γ.E :=
    (Γ.hE_atom.le_iff.mp hσ'_le_E).resolve_left hσ'_atom.1
  exact sigma'_ne_E Γ ha ha_on ha_ne_O hσ'_eq_E

theorem coord_mul_right_inv (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    coord_mul Γ a (coord_inv Γ a) = Γ.I := by
  unfold coord_mul coord_inv
  set σ' := (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) with hσ'_def
  set d_a := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) with hda_def
  set inv_a := (σ' ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) with hinv_def
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have hσ'_ne_EI := sigma'_ne_E_I Γ a
  have hd_atom := d_a_atom Γ ha ha_on
  have hinv_atom : IsAtom inv_a := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_le_l : inv_a ≤ Γ.O ⊔ Γ.U := inf_le_right
  have hinv_le_σEI : inv_a ≤ σ' ⊔ Γ.E_I := inf_le_left
  have hinv_ne_EI : inv_a ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hinv_le_l)

  have hinvEI_le : inv_a ⊔ Γ.E_I ≤ σ' ⊔ Γ.E_I := sup_le hinv_le_σEI le_sup_right
  have hEI_lt_invEI : Γ.E_I < inv_a ⊔ Γ.E_I := lt_of_le_of_ne le_sup_right
    (fun h => hinv_ne_EI ((Γ.hE_I_atom.le_iff.mp
      (le_sup_left.trans h.symm.le)).resolve_left hinv_atom.1))
  have hcov_EI : Γ.E_I ⋖ σ' ⊔ Γ.E_I := by
    have := atom_covBy_join Γ.hE_I_atom hσ'_atom (Ne.symm hσ'_ne_EI)
    rwa [sup_comm] at this
  have hinvEI_eq : inv_a ⊔ Γ.E_I = σ' ⊔ Γ.E_I :=
    (hcov_EI.eq_or_eq hEI_lt_invEI.le hinvEI_le).resolve_left (ne_of_gt hEI_lt_invEI)

  have hσ'_le_OC : σ' ≤ Γ.O ⊔ Γ.C := inf_le_left
  have h_dir_OC : (σ' ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) = σ' := by
    rw [show σ' ⊔ Γ.E_I = Γ.E_I ⊔ σ' from sup_comm _ _]
    exact line_direction Γ.hE_I_atom Γ.hE_I_not_OC hσ'_le_OC
  have hOC_inf_invEI : (Γ.O ⊔ Γ.C) ⊓ (inv_a ⊔ Γ.E_I) = σ' := by
    rw [hinvEI_eq, show (Γ.O ⊔ Γ.C) ⊓ (σ' ⊔ Γ.E_I) =
        (σ' ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _, h_dir_OC]

  have hσ'_le_Id : σ' ≤ Γ.I ⊔ d_a := inf_le_right
  have hI_ne_d := I_ne_d_a Γ ha ha_on
  have hσ'_ne_d : σ' ≠ d_a := by
    intro h
    have hσ'_le_m : σ' ≤ Γ.U ⊔ Γ.V := h.symm ▸ inf_le_right
    have hσ'_le_OC : σ' ≤ Γ.O ⊔ Γ.C := inf_le_left
    have hσ'_le_E : σ' ≤ Γ.E := by
      unfold CoordSystem.E CoordSystem.m; exact le_inf hσ'_le_OC hσ'_le_m
    have hσ'_eq_E : σ' = Γ.E :=
      (Γ.hE_atom.le_iff.mp hσ'_le_E).resolve_left hσ'_atom.1
    exact sigma'_ne_E Γ ha ha_on ha_ne_O hσ'_eq_E
  have hσd_le_Id : σ' ⊔ d_a ≤ Γ.I ⊔ d_a := sup_le hσ'_le_Id le_sup_right
  have hd_lt_σd : d_a < σ' ⊔ d_a := lt_of_le_of_ne le_sup_right
    (fun h => hσ'_ne_d ((hd_atom.le_iff.mp
      (le_sup_left.trans h.symm.le)).resolve_left hσ'_atom.1))
  have hcov_d : d_a ⋖ Γ.I ⊔ d_a := by
    have h2 : d_a ⋖ d_a ⊔ Γ.I := atom_covBy_join hd_atom Γ.hI hI_ne_d.symm
    exact (sup_comm d_a Γ.I) ▸ h2
  have hσd_eq : σ' ⊔ d_a = Γ.I ⊔ d_a :=
    (hcov_d.eq_or_eq hd_lt_σd.le hσd_le_Id).resolve_left (ne_of_gt hd_lt_σd)

  show ((Γ.O ⊔ Γ.C) ⊓ (inv_a ⊔ Γ.E_I) ⊔ d_a) ⊓ (Γ.O ⊔ Γ.U) = Γ.I
  rw [hOC_inf_invEI, hσd_eq]

  rw [show Γ.I ⊔ d_a = d_a ⊔ Γ.I from sup_comm _ _]
  exact line_direction hd_atom (d_a_not_l Γ ha ha_on ha_ne_U) Γ.hI_on

private theorem sigma_inv_eq_sigma_prime (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    (Γ.O ⊔ Γ.C) ⊓ (coord_inv Γ a ⊔ Γ.E_I) =
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by
  unfold coord_inv
  set σ' := (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) with hσ'_def
  set inv_a := (σ' ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) with hinv_def
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have hσ'_ne_EI := sigma'_ne_E_I Γ a
  have hinv_atom : IsAtom inv_a := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_le_l : inv_a ≤ Γ.O ⊔ Γ.U := inf_le_right
  have hinv_le_σEI : inv_a ≤ σ' ⊔ Γ.E_I := inf_le_left
  have hinv_ne_EI : inv_a ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hinv_le_l)
  have hinvEI_le : inv_a ⊔ Γ.E_I ≤ σ' ⊔ Γ.E_I := sup_le hinv_le_σEI le_sup_right
  have hEI_lt_invEI : Γ.E_I < inv_a ⊔ Γ.E_I := lt_of_le_of_ne le_sup_right
    (fun h => hinv_ne_EI ((Γ.hE_I_atom.le_iff.mp
      (le_sup_left.trans h.symm.le)).resolve_left hinv_atom.1))
  have hcov_EI : Γ.E_I ⋖ σ' ⊔ Γ.E_I := by
    have := atom_covBy_join Γ.hE_I_atom hσ'_atom (Ne.symm hσ'_ne_EI)
    rwa [sup_comm] at this
  have hinvEI_eq : inv_a ⊔ Γ.E_I = σ' ⊔ Γ.E_I :=
    (hcov_EI.eq_or_eq hEI_lt_invEI.le hinvEI_le).resolve_left (ne_of_gt hEI_lt_invEI)
  rw [hinvEI_eq, show (Γ.O ⊔ Γ.C) ⊓ (σ' ⊔ Γ.E_I) =
      (σ' ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _,
      show σ' ⊔ Γ.E_I = Γ.E_I ⊔ σ' from sup_comm _ _]
  exact line_direction Γ.hE_I_atom Γ.hE_I_not_OC inf_le_left

theorem coord_inv_I_eq_I (Γ : CoordSystem L) : coord_inv Γ Γ.I = Γ.I := by
  unfold coord_inv

  have hd_I : (Γ.I ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I := rfl
  rw [hd_I]

  have hI_ne_C : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hI_ne_EI : Γ.I ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ Γ.hI_on)
  have hC_ne_EI : Γ.C ≠ Γ.E_I := fun h => Γ.hC_not_m (h ▸ Γ.hE_I_on_m)
  have hOC_ne : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)

  have hcov_I_IC : Γ.I ⋖ Γ.I ⊔ Γ.C := atom_covBy_join Γ.hI Γ.hC hI_ne_C
  have hI_lt_IE : Γ.I < Γ.I ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
    (fun h => hI_ne_EI ((Γ.hI.le_iff.mp
      (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_I_atom.1).symm)
  have hIE_eq_IC : Γ.I ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
    (hcov_I_IC.eq_or_eq hI_lt_IE.le (sup_le le_sup_left Γ.hE_I_le_IC)).resolve_left
      (ne_of_gt hI_lt_IE)
  rw [hIE_eq_IC]

  have hOC_inf_IC : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ Γ.C) = Γ.C := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _,
        show Γ.I ⊔ Γ.C = Γ.C ⊔ Γ.I from sup_comm _ _]
    exact modular_intersection Γ.hC Γ.hO Γ.hI hOC_ne.symm hI_ne_C.symm Γ.hOI
      (sup_comm Γ.O Γ.C ▸ hI_not_OC Γ)
  rw [hOC_inf_IC]

  have hC_lt_CE : Γ.C < Γ.C ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
    (fun h => hC_ne_EI ((Γ.hC.le_iff.mp
      (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_I_atom.1).symm)
  have hcov_C_IC : Γ.C ⋖ Γ.I ⊔ Γ.C := by
    have := atom_covBy_join Γ.hC Γ.hI hI_ne_C.symm
    rwa [sup_comm] at this
  have hCE_eq_IC : Γ.C ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
    (hcov_C_IC.eq_or_eq hC_lt_CE.le (sup_le le_sup_right Γ.hE_I_le_IC)).resolve_left
      (ne_of_gt hC_lt_CE)
  rw [hCE_eq_IC]

  rw [show Γ.I ⊔ Γ.C = Γ.C ⊔ Γ.I from sup_comm _ _]
  exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on

private theorem sigma_a_atom (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    IsAtom ((Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I)) := by
  have ha_ne_EI : a ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ ha_on)
  have hOC_ne : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hOCEI_eq_π : Γ.O ⊔ Γ.C ⊔ Γ.E_I = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h_lt : Γ.O ⊔ Γ.C < Γ.O ⊔ Γ.C ⊔ Γ.E_I :=
      lt_of_le_of_ne le_sup_left (fun heq => Γ.hE_I_not_OC (heq ▸ le_sup_right))
    have h_le : Γ.O ⊔ Γ.C ⊔ Γ.E_I ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
      sup_le (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane)
        (Γ.hE_I_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
    exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  rw [show (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) = (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _]
  refine perspect_atom Γ.hE_I_atom ha ha_ne_EI Γ.hO Γ.hC hOC_ne Γ.hE_I_not_OC ?_
  exact sup_le ((ha_on.trans le_sup_left).trans hOCEI_eq_π.symm.le) le_sup_right

private theorem sigma_a_ne_E (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ Γ.E := by
  intro h
  have ha_ne_EI : a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ ha_on)
  have hE_le_aEI : Γ.E ≤ a ⊔ Γ.E_I := h.symm.le.trans inf_le_right
  have hEIE_le_aEI : Γ.E_I ⊔ Γ.E ≤ a ⊔ Γ.E_I := sup_le le_sup_right hE_le_aEI
  have h_cov_EI_aEI : Γ.E_I ⋖ a ⊔ Γ.E_I :=
    (sup_comm Γ.E_I a) ▸ atom_covBy_join Γ.hE_I_atom ha ha_ne_EI.symm
  have h_cov_EI_EIE : Γ.E_I ⋖ Γ.E_I ⊔ Γ.E :=
    atom_covBy_join Γ.hE_I_atom Γ.hE_atom Γ.hE_I_ne_E
  have h_eq : Γ.E_I ⊔ Γ.E = a ⊔ Γ.E_I :=
    (h_cov_EI_aEI.eq_or_eq h_cov_EI_EIE.lt.le hEIE_le_aEI).resolve_left
      (ne_of_gt h_cov_EI_EIE.lt)
  have ha_le_EIE : a ≤ Γ.E_I ⊔ Γ.E := h_eq.symm ▸ (le_sup_left : a ≤ a ⊔ Γ.E_I)
  have ha_le_m : a ≤ Γ.U ⊔ Γ.V :=
    ha_le_EIE.trans (sup_le Γ.hE_I_on_m CoordSystem.hE_on_m)
  have ha_le_U : a ≤ Γ.U := Γ.l_inf_m_eq_U ▸ le_inf ha_on ha_le_m
  exact ha_ne_U ((Γ.hU.le_iff.mp ha_le_U).resolve_left ha.1)

private theorem d_a_ne_d_inv (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U)
    (ha_ne_inv : a ≠ coord_inv Γ a) :
    (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠ (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  intro h
  set d_a := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  have hd_atom : IsAtom d_a := d_a_atom Γ ha ha_on
  have hinv_atom : IsAtom (coord_inv Γ a) := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_on : coord_inv Γ a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a

  have hd_le_aC : d_a ≤ a ⊔ Γ.C := inf_le_left
  have hd_le_invC : d_a ≤ coord_inv Γ a ⊔ Γ.C := h.le.trans inf_le_left

  have hmeet : (a ⊔ Γ.C) ⊓ (coord_inv Γ a ⊔ Γ.C) = Γ.C :=
    Γ.lines_through_C_meet ha hinv_atom ha_ne_inv ha_on hinv_on
  have hd_le_C : d_a ≤ Γ.C := hmeet ▸ le_inf hd_le_aC hd_le_invC
  have hd_eq_C : d_a = Γ.C :=
    (Γ.hC.le_iff.mp hd_le_C).resolve_left hd_atom.1
  exact Γ.hC_not_m (hd_eq_C ▸ (inf_le_right : d_a ≤ Γ.U ⊔ Γ.V))

private theorem ha_ne_I_of_distinct (Γ : CoordSystem L)
    {a : L} (_ha : IsAtom a) (ha_ne_inv : a ≠ coord_inv Γ a) :
    a ≠ Γ.I := by
  intro h
  exact ha_ne_inv (h.trans (coord_inv_I_eq_I Γ).symm |>.trans (h ▸ rfl))

private theorem sigma_a_ne_C (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_I : a ≠ Γ.I) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ Γ.C := by
  intro h

  have hC_le_aEI : Γ.C ≤ a ⊔ Γ.E_I := h.symm.le.trans inf_le_right

  have ha_ne_C : a ≠ Γ.C := fun he => Γ.hC_not_l (he ▸ ha_on)
  have ha_ne_EI : a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ ha_on)
  have h_aC_le : a ⊔ Γ.C ≤ a ⊔ Γ.E_I := sup_le le_sup_left hC_le_aEI
  have hcov_a_aC : a ⋖ a ⊔ Γ.C := atom_covBy_join ha Γ.hC ha_ne_C
  have hcov_a_aEI : a ⋖ a ⊔ Γ.E_I := atom_covBy_join ha Γ.hE_I_atom ha_ne_EI
  have h_aC_lt : a < a ⊔ Γ.C := hcov_a_aC.lt
  have h_aC_eq_aEI : a ⊔ Γ.C = a ⊔ Γ.E_I :=
    (hcov_a_aEI.eq_or_eq h_aC_lt.le h_aC_le).resolve_left (ne_of_gt h_aC_lt)

  have hEI_le_aC : Γ.E_I ≤ a ⊔ Γ.C := h_aC_eq_aEI.symm ▸ (le_sup_right : Γ.E_I ≤ a ⊔ Γ.E_I)
  have hEI_le_d : Γ.E_I ≤ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    le_inf hEI_le_aC Γ.hE_I_on_m

  have hd_atom : IsAtom ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := d_a_atom Γ ha ha_on
  have hd_eq_EI : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I :=
    ((hd_atom.le_iff.mp hEI_le_d).resolve_left Γ.hE_I_atom.1).symm

  have hd_le_IC : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.I ⊔ Γ.C := by
    rw [hd_eq_EI]; exact Γ.hE_I_le_IC
  have hd_le_aC : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ a ⊔ Γ.C := inf_le_left
  have hmeet : (a ⊔ Γ.C) ⊓ (Γ.I ⊔ Γ.C) = Γ.C :=
    Γ.lines_through_C_meet ha Γ.hI ha_ne_I ha_on Γ.hI_on
  have hd_le_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.C :=
    (le_inf hd_le_aC hd_le_IC).trans hmeet.le
  have hd_eq_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.C :=
    (Γ.hC.le_iff.mp hd_le_C).resolve_left hd_atom.1
  exact Γ.hC_not_m (hd_eq_C ▸ (inf_le_right : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V))

private theorem sigma_a_ne_O (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_O : a ≠ Γ.O) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ Γ.O := by
  intro h
  have hO_le_aEI : Γ.O ≤ a ⊔ Γ.E_I := h.symm.le.trans inf_le_right
  have ha_ne_EI : a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ ha_on)
  have hcov_a_aEI : a ⋖ a ⊔ Γ.E_I := atom_covBy_join ha Γ.hE_I_atom ha_ne_EI
  have hcov_a_aO : a ⋖ a ⊔ Γ.O := atom_covBy_join ha Γ.hO ha_ne_O
  have hOa_le : a ⊔ Γ.O ≤ a ⊔ Γ.E_I := sup_le le_sup_left hO_le_aEI
  have h_aO_eq : a ⊔ Γ.O = a ⊔ Γ.E_I :=
    (hcov_a_aEI.eq_or_eq hcov_a_aO.lt.le hOa_le).resolve_left (ne_of_gt hcov_a_aO.lt)
  have hEI_le_aO : Γ.E_I ≤ a ⊔ Γ.O :=
    h_aO_eq.symm ▸ (le_sup_right : Γ.E_I ≤ a ⊔ Γ.E_I)
  have haO_le_l : a ⊔ Γ.O ≤ Γ.O ⊔ Γ.U := sup_le ha_on le_sup_left
  exact Γ.hE_I_not_l (hEI_le_aO.trans haO_le_l)

private theorem sigma_a_ne_U (Γ : CoordSystem L)
    {a : L} (_ha : IsAtom a) (_ha_on : a ≤ Γ.O ⊔ Γ.U) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ Γ.U := by
  intro h
  have hU_le_OC : Γ.U ≤ Γ.O ⊔ Γ.C := h.symm.le.trans inf_le_left
  have hOC_inf_l : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
  have hU_le_O : Γ.U ≤ Γ.O := hOC_inf_l ▸ le_inf le_sup_right hU_le_OC
  exact Γ.hOU.symm ((Γ.hO.le_iff.mp hU_le_O).resolve_left Γ.hU.1)

private theorem sigma_a_ne_a (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_O : a ≠ Γ.O) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ a := by
  intro h
  have ha_le_OC : a ≤ Γ.O ⊔ Γ.C := h.symm.le.trans inf_le_left
  have hl_inf_OC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
  have ha_le_O : a ≤ Γ.O := hl_inf_OC ▸ le_inf ha_on ha_le_OC
  exact ha_ne_O ((Γ.hO.le_iff.mp ha_le_O).resolve_left ha.1)

private theorem sigma_a_ne_d_a (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  intro h
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have hσa_le_OC : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσa_le_m : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.U ⊔ Γ.V := h.le.trans inf_le_right
  have hσa_le_E : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.E := by
    show (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
    exact le_inf hσa_le_OC hσa_le_m
  have hσa_eq_E : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) = Γ.E :=
    (Γ.hE_atom.le_iff.mp hσa_le_E).resolve_left hσa_atom.1
  exact sigma_a_ne_E Γ ha ha_on ha_ne_U hσa_eq_E

private theorem inv_a_not_OC (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    ¬ coord_inv Γ a ≤ Γ.O ⊔ Γ.C := by
  intro h
  have hinv_atom : IsAtom (coord_inv Γ a) := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_on : coord_inv Γ a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a
  have hl_inf_OC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
  have hinv_le_O : coord_inv Γ a ≤ Γ.O := hl_inf_OC ▸ le_inf hinv_on h
  have hinv_eq_O : coord_inv Γ a = Γ.O :=
    (Γ.hO.le_iff.mp hinv_le_O).resolve_left hinv_atom.1
  exact coord_inv_ne_O Γ ha ha_on ha_ne_U hinv_eq_O

private theorem sigma_a_ne_inv_a (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ coord_inv Γ a := by
  intro h
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have hinv_on : coord_inv Γ a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a
  have hσa_le_OC : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσa_le_l : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.U := h.symm ▸ hinv_on
  have hl_inf_OC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
  have hσa_le_O : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O :=
    (le_inf hσa_le_l hσa_le_OC).trans hl_inf_OC.le
  have hσa_eq_O : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) = Γ.O :=
    (Γ.hO.le_iff.mp hσa_le_O).resolve_left hσa_atom.1
  exact sigma_a_ne_O Γ ha ha_on ha_ne_O hσa_eq_O

private theorem sigma_a_ne_sigma' (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U)
    (ha_ne_inv : a ≠ coord_inv Γ a) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by
  intro h

  have hσ_inv_eq := sigma_inv_eq_sigma_prime Γ ha ha_on ha_ne_U
  rw [← hσ_inv_eq] at h

  have hinv_atom : IsAtom (coord_inv Γ a) := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_on : coord_inv Γ a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have ha_ne_E_I : a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ ha_on)
  have hinv_ne_E_I : coord_inv Γ a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ hinv_on)

  have hσa_le_aEI : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ a ⊔ Γ.E_I := inf_le_right
  have hσa_le_invEI : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ coord_inv Γ a ⊔ Γ.E_I :=
    h.le.trans inf_le_right

  have hinv_not_aEI : ¬ coord_inv Γ a ≤ a ⊔ Γ.E_I := by
    intro hle
    have hl_inf : (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.E_I) = a := by
      rw [show a ⊔ Γ.E_I = Γ.E_I ⊔ a from sup_comm _ _]
      exact inf_sup_of_atom_not_le Γ.hE_I_atom Γ.hE_I_not_l ha_on
    have hinv_le_a : coord_inv Γ a ≤ a := (le_inf hinv_on hle).trans hl_inf.le
    exact ha_ne_inv ((ha.le_iff.mp hinv_le_a).resolve_left hinv_atom.1).symm

  have h_inter : (Γ.E_I ⊔ a) ⊓ (Γ.E_I ⊔ coord_inv Γ a) = Γ.E_I :=
    modular_intersection Γ.hE_I_atom ha hinv_atom
      ha_ne_E_I.symm hinv_ne_E_I.symm ha_ne_inv
      (by rw [sup_comm]; exact hinv_not_aEI)
  have hσa_le_E_I : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.E_I :=
    (le_inf
      (hσa_le_aEI.trans (sup_comm a Γ.E_I).le)
      (hσa_le_invEI.trans (sup_comm (coord_inv Γ a) Γ.E_I).le)).trans h_inter.le
  have hσa_eq_E_I : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) = Γ.E_I :=
    (Γ.hE_I_atom.le_iff.mp hσa_le_E_I).resolve_left hσa_atom.1
  exact Γ.hE_I_not_OC
    (hσa_eq_E_I ▸ (inf_le_left : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C))

private theorem h_sides_X23_mul (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_U : a ≠ Γ.U) (ha_ne_inv : a ≠ coord_inv Γ a) :
    coord_inv Γ a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠
    (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
      (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by
  intro h
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have hinv_atom : IsAtom (coord_inv Γ a) := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_not_OC : ¬ coord_inv Γ a ≤ Γ.O ⊔ Γ.C := inv_a_not_OC Γ ha ha_on ha_ne_U
  have hσa_le_OC : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσ'_le_OC : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤ Γ.O ⊔ Γ.C :=
    inf_le_left

  have hσ'_le_RHS : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := le_sup_right
  have hσ'_le_LHS : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      coord_inv Γ a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    hσ'_le_RHS.trans h.symm.le

  have hOC_inf : (Γ.O ⊔ Γ.C) ⊓ (coord_inv Γ a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I)) =
      (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    inf_sup_of_atom_not_le hinv_atom hinv_not_OC hσa_le_OC

  have hσ'_le_σa : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    (le_inf hσ'_le_OC hσ'_le_LHS).trans hOC_inf.le

  have hσ'_eq_σa := IsAtom.eq_of_le hσ'_atom hσa_atom hσ'_le_σa
  exact sigma_a_ne_sigma' Γ ha ha_on ha_ne_U ha_ne_inv hσ'_eq_σa.symm

private theorem h_sides_X13_mul (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (ha_ne_inv : a ≠ coord_inv Γ a) :
    a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠
    (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
      (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by
  intro h
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have ha_not_OC : ¬ a ≤ Γ.O ⊔ Γ.C := by
    intro hle
    have hl_inf_OC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
    exact ha_ne_O ((Γ.hO.le_iff.mp (hl_inf_OC ▸ le_inf ha_on hle)).resolve_left ha.1)
  have hσa_le_OC : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσ'_le_OC : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤ Γ.O ⊔ Γ.C :=
    inf_le_left

  have hσ'_le_RHS : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := le_sup_right
  have hσ'_le_LHS : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    hσ'_le_RHS.trans h.symm.le

  have hOC_inf : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I)) =
      (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    inf_sup_of_atom_not_le ha ha_not_OC hσa_le_OC
  have hσ'_le_σa : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    (le_inf hσ'_le_OC hσ'_le_LHS).trans hOC_inf.le
  have hσ'_eq_σa := IsAtom.eq_of_le hσ'_atom hσa_atom hσ'_le_σa
  exact sigma_a_ne_sigma' Γ ha ha_on ha_ne_U ha_ne_inv hσ'_eq_σa.symm

private theorem coord_first_desargues_mul (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (ha_ne_inv : a ≠ coord_inv Γ a)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    (coord_inv Γ a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I)) ⊓
    ((coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
       (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V))) ≤
    Γ.U ⊔ (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by

  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def
  set inv_a := coord_inv Γ a with hinv_def
  set σ_a := (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) with hσa_def
  set σ' := (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) with hσ'_def
  set d_a := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) with hda_def
  set d_inv := (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) with hdinv_def

  have hσa_atom : IsAtom σ_a := sigma_a_atom Γ ha ha_on
  have hσ'_atom : IsAtom σ' := sigma'_atom Γ ha ha_on
  have hd_atom : IsAtom d_a := d_a_atom Γ ha ha_on
  have hinv_atom : IsAtom inv_a := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_on : inv_a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a
  have hinv_ne_O : inv_a ≠ Γ.O := coord_inv_ne_O Γ ha ha_on ha_ne_U
  have hinv_ne_U : inv_a ≠ Γ.U := coord_inv_ne_U Γ ha ha_on ha_ne_O
  have hd_inv_atom : IsAtom d_inv := d_a_atom Γ hinv_atom hinv_on

  have ha_ne_I : a ≠ Γ.I := ha_ne_I_of_distinct Γ ha ha_ne_inv

  have hσa_ne_C : σ_a ≠ Γ.C := sigma_a_ne_C Γ ha ha_on ha_ne_I
  have hσa_ne_O : σ_a ≠ Γ.O := sigma_a_ne_O Γ ha ha_on ha_ne_O
  have hσa_ne_U : σ_a ≠ Γ.U := sigma_a_ne_U Γ ha ha_on
  have hσa_ne_E : σ_a ≠ Γ.E := sigma_a_ne_E Γ ha ha_on ha_ne_U
  have hσa_ne_a : σ_a ≠ a := sigma_a_ne_a Γ ha ha_on ha_ne_O
  have hσa_ne_d : σ_a ≠ d_a := sigma_a_ne_d_a Γ ha ha_on ha_ne_U
  have hσa_ne_inv : σ_a ≠ inv_a := sigma_a_ne_inv_a Γ ha ha_on ha_ne_O
  have hσa_ne_σ' : σ_a ≠ σ' := sigma_a_ne_sigma' Γ ha ha_on ha_ne_U ha_ne_inv
  have hσ'_ne_C : σ' ≠ Γ.C := sigma'_ne_C Γ ha ha_on ha_ne_I
  have hσ'_ne_O : σ' ≠ Γ.O := sigma'_ne_O Γ ha ha_on ha_ne_U
  have hσ'_ne_E : σ' ≠ Γ.E := sigma'_ne_E Γ ha ha_on ha_ne_O
  have hd_ne_d_inv : d_a ≠ d_inv := d_a_ne_d_inv Γ ha ha_on ha_ne_U ha_ne_inv

  have hC_le_π : Γ.C ≤ π := Γ.hC_plane
  have ha_le_π : a ≤ π := ha_on.trans le_sup_left
  have hinv_le_π : inv_a ≤ π := hinv_on.trans le_sup_left
  have hm_le_π : Γ.U ⊔ Γ.V ≤ π :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hd_le_π : d_a ≤ π := (inf_le_right : d_a ≤ Γ.U ⊔ Γ.V).trans hm_le_π
  have hd_inv_le_π : d_inv ≤ π := (inf_le_right : d_inv ≤ Γ.U ⊔ Γ.V).trans hm_le_π
  have hσa_le_OC : σ_a ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσ'_le_OC : σ' ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hOC_le_π : Γ.O ⊔ Γ.C ≤ π :=
    sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane
  have hσa_le_π : σ_a ≤ π := hσa_le_OC.trans hOC_le_π
  have hσ'_le_π : σ' ≤ π := hσ'_le_OC.trans hOC_le_π

  have hC_ne_a : Γ.C ≠ a := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hC_ne_inv : Γ.C ≠ inv_a := fun h => Γ.hC_not_l (h ▸ hinv_on)
  have hC_ne_σa : Γ.C ≠ σ_a := fun h => hσa_ne_C h.symm
  have hC_ne_d : Γ.C ≠ d_a := fun h =>
    Γ.hC_not_m (h ▸ (inf_le_right : d_a ≤ Γ.U ⊔ Γ.V))
  have hC_ne_d_inv : Γ.C ≠ d_inv := fun h =>
    Γ.hC_not_m (h ▸ (inf_le_right : d_inv ≤ Γ.U ⊔ Γ.V))
  have hC_ne_σ' : Γ.C ≠ σ' := fun h => hσ'_ne_C h.symm

  have ha_ne_d : a ≠ d_a := by
    intro h
    exact d_a_not_l Γ ha ha_on ha_ne_U (h ▸ ha_on : d_a ≤ Γ.O ⊔ Γ.U)
  have hinv_ne_d_inv : inv_a ≠ d_inv := by
    intro h
    exact d_a_not_l Γ hinv_atom hinv_on hinv_ne_U
      (h ▸ hinv_on : d_inv ≤ Γ.O ⊔ Γ.U)

  have hσ'_ne_d : σ' ≠ d_a := by
    intro h
    have hσ'_le_m : σ' ≤ Γ.U ⊔ Γ.V := h ▸ inf_le_right
    have hσ'_le_E : σ' ≤ Γ.E := by
      show σ' ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V); exact le_inf hσ'_le_OC hσ'_le_m
    exact hσ'_ne_E ((Γ.hE_atom.le_iff.mp hσ'_le_E).resolve_left hσ'_atom.1)
  have hσ'_ne_d_inv : σ' ≠ d_inv := by
    intro h
    have hσ'_le_m : σ' ≤ Γ.U ⊔ Γ.V := h ▸ inf_le_right
    have hσ'_le_E : σ' ≤ Γ.E := by
      show σ' ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V); exact le_inf hσ'_le_OC hσ'_le_m
    exact hσ'_ne_E ((Γ.hE_atom.le_iff.mp hσ'_le_E).resolve_left hσ'_atom.1)

  have hd_perspect : d_a ≤ Γ.C ⊔ a := by
    rw [show Γ.C ⊔ a = a ⊔ Γ.C from sup_comm _ _]; exact inf_le_left
  have hd_inv_perspect : d_inv ≤ Γ.C ⊔ inv_a := by
    rw [show Γ.C ⊔ inv_a = inv_a ⊔ Γ.C from sup_comm _ _]; exact inf_le_left
  have hσ'_perspect : σ' ≤ Γ.C ⊔ σ_a := by

    have hC_lt_Cσa : Γ.C < Γ.C ⊔ σ_a := lt_of_le_of_ne le_sup_left
      (fun h => hσa_ne_C ((Γ.hC.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left hσa_atom.1))
    have hCσa_le_OC : Γ.C ⊔ σ_a ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right hσa_le_OC
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have hC_cov_OC : Γ.C ⋖ Γ.O ⊔ Γ.C := by
      have := atom_covBy_join Γ.hC Γ.hO hOC.symm
      rwa [sup_comm] at this
    have hCσa_eq_OC : Γ.C ⊔ σ_a = Γ.O ⊔ Γ.C :=
      (hC_cov_OC.eq_or_eq hC_lt_Cσa.le hCσa_le_OC).resolve_left (ne_of_gt hC_lt_Cσa)
    exact hCσa_eq_OC ▸ hσ'_le_OC

  have ha_inv_eq_l : a ⊔ inv_a = Γ.O ⊔ Γ.U := by
    have h_le : a ⊔ inv_a ≤ Γ.O ⊔ Γ.U := sup_le ha_on hinv_on
    have h_lt : a < a ⊔ inv_a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_inv ((ha.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left hinv_atom.1).symm)
    have hcov : a ⋖ Γ.O ⊔ Γ.U := line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on
    exact (hcov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hd_d_inv_eq_m : d_a ⊔ d_inv = Γ.U ⊔ Γ.V := by
    have h_le : d_a ⊔ d_inv ≤ Γ.U ⊔ Γ.V := sup_le inf_le_right inf_le_right
    have h_lt : d_a < d_a ⊔ d_inv := lt_of_le_of_ne le_sup_left
      (fun h => hd_ne_d_inv ((hd_atom.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left hd_inv_atom.1).symm)
    have hcov : d_a ⋖ Γ.U ⊔ Γ.V :=
      line_covers_its_atoms Γ.hU Γ.hV hUV hd_atom inf_le_right
    exact (hcov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)

  have hs12 : a ⊔ inv_a ≠ d_a ⊔ d_inv := by
    rw [ha_inv_eq_l, hd_d_inv_eq_m]
    intro h
    exact Γ.hO_not_m (h ▸ (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U))

  have hσa_not_l : ¬ σ_a ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hl_inf_OC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
    have hσa_le_O : σ_a ≤ Γ.O := hl_inf_OC ▸ le_inf h hσa_le_OC
    exact hσa_ne_O ((Γ.hO.le_iff.mp hσa_le_O).resolve_left hσa_atom.1)
  have hσ'_not_m : ¬ σ' ≤ Γ.U ⊔ Γ.V := by
    intro h
    have hσ'_le_E : σ' ≤ Γ.E := by
      show σ' ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V); exact le_inf hσ'_le_OC h
    exact hσ'_ne_E ((Γ.hE_atom.le_iff.mp hσ'_le_E).resolve_left hσ'_atom.1)

  have hπA : a ⊔ inv_a ⊔ σ_a = π := by
    rw [ha_inv_eq_l]
    have h_lt : (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U ⊔ σ_a := lt_of_le_of_ne le_sup_left
      (fun heq => hσa_not_l (le_sup_right.trans heq.symm.le))
    have h_le : Γ.O ⊔ Γ.U ⊔ σ_a ≤ π := sup_le le_sup_left hσa_le_π
    exact ((l_covBy_π_inv Γ).eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  have hπB : d_a ⊔ d_inv ⊔ σ' = π := by
    rw [hd_d_inv_eq_m]
    have h_lt : Γ.U ⊔ Γ.V < Γ.U ⊔ Γ.V ⊔ σ' := lt_of_le_of_ne le_sup_left
      (fun heq => hσ'_not_m (le_sup_right.trans heq.symm.le))
    have h_le : Γ.U ⊔ Γ.V ⊔ σ' ≤ π := sup_le hm_le_π hσ'_le_π
    exact (Γ.m_covBy_π.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)

  have hcov12 : a ⊔ inv_a ⋖ π := ha_inv_eq_l ▸ l_covBy_π_inv Γ

  have h_a_lt_l : a < Γ.O ⊔ Γ.U := lt_of_le_of_ne ha_on
    (fun heq => ha_ne_O ((ha.le_iff.mp
      (le_sup_left.trans heq.symm.le)).resolve_left Γ.hO.1).symm)
  have h_inv_lt_l : inv_a < Γ.O ⊔ Γ.U := lt_of_le_of_ne hinv_on
    (fun heq => hinv_ne_O ((hinv_atom.le_iff.mp
      (le_sup_left.trans heq.symm.le)).resolve_left Γ.hO.1).symm)

  have h_not_collinear_13 : ¬ inv_a ≤ a ⊔ σ_a := by
    intro h
    have hl_le : Γ.O ⊔ Γ.U ≤ a ⊔ σ_a := ha_inv_eq_l ▸ sup_le le_sup_left h
    have h_cov_aσa : a ⋖ a ⊔ σ_a := atom_covBy_join ha hσa_atom (Ne.symm hσa_ne_a)
    have hl_eq_aσa : Γ.O ⊔ Γ.U = a ⊔ σ_a :=
      (h_cov_aσa.eq_or_eq h_a_lt_l.le hl_le).resolve_left (ne_of_gt h_a_lt_l)
    exact hσa_not_l (hl_eq_aσa.symm ▸ (le_sup_right : σ_a ≤ a ⊔ σ_a))
  have h_not_collinear_23 : ¬ a ≤ inv_a ⊔ σ_a := by
    intro h
    have hl_le : Γ.O ⊔ Γ.U ≤ inv_a ⊔ σ_a := ha_inv_eq_l ▸ sup_le h le_sup_left
    have h_cov_invσa : inv_a ⋖ inv_a ⊔ σ_a :=
      atom_covBy_join hinv_atom hσa_atom hσa_ne_inv.symm
    have hl_eq_invσa : Γ.O ⊔ Γ.U = inv_a ⊔ σ_a :=
      (h_cov_invσa.eq_or_eq h_inv_lt_l.le hl_le).resolve_left (ne_of_gt h_inv_lt_l)
    exact hσa_not_l (hl_eq_invσa.symm ▸ (le_sup_right : σ_a ≤ inv_a ⊔ σ_a))
  have hcov13 : a ⊔ σ_a ⋖ π := by
    have hπ_eq : a ⊔ σ_a ⊔ inv_a = π := by
      rw [sup_assoc, sup_comm σ_a inv_a, ← sup_assoc]; exact hπA
    exact hπ_eq ▸ line_covBy_plane ha hσa_atom hinv_atom
      (Ne.symm hσa_ne_a) ha_ne_inv hσa_ne_inv h_not_collinear_13
  have hcov23 : inv_a ⊔ σ_a ⋖ π := by
    have hπ_eq : inv_a ⊔ σ_a ⊔ a = π := by
      rw [show inv_a ⊔ σ_a ⊔ a = a ⊔ inv_a ⊔ σ_a from by
        rw [sup_assoc, sup_comm (σ_a) a, ← sup_assoc, sup_comm inv_a a]]
      exact hπA
    exact hπ_eq ▸ line_covBy_plane hinv_atom hσa_atom ha
      hσa_ne_inv.symm ha_ne_inv.symm hσa_ne_a h_not_collinear_23

  have hs13 : a ⊔ σ_a ≠ d_a ⊔ σ' :=
    h_sides_X13_mul Γ ha ha_on ha_ne_O ha_ne_U ha_ne_inv
  have hs23 : inv_a ⊔ σ_a ≠ d_inv ⊔ σ' :=
    h_sides_X23_mul Γ ha ha_on ha_ne_U ha_ne_inv

  obtain ⟨axis, h_axis_le, h_axis_ne, h₁₂, h₁₃, h₂₃⟩ := desargues_planar
    Γ.hC ha hinv_atom hσa_atom hd_atom hd_inv_atom hσ'_atom
    hC_le_π ha_le_π hinv_le_π hσa_le_π hd_le_π hd_inv_le_π hσ'_le_π
    hd_perspect hd_inv_perspect hσ'_perspect
    ha_ne_inv (Ne.symm hσa_ne_a) (Ne.symm hσa_ne_inv)
    hd_ne_d_inv (Ne.symm hσ'_ne_d) (Ne.symm hσ'_ne_d_inv)
    hs12 hs13 hs23
    hπA hπB
    hC_ne_a hC_ne_inv hC_ne_σa hC_ne_d hC_ne_d_inv hC_ne_σ'
    ha_ne_d hinv_ne_d_inv hσa_ne_σ'
    R hR hR_not h_irred
    hcov12 hcov13 hcov23

  have hX12_eq_U : (a ⊔ inv_a) ⊓ (d_a ⊔ d_inv) = Γ.U := by
    rw [ha_inv_eq_l, hd_d_inv_eq_m]; exact Γ.l_inf_m_eq_U
  have hU_le_axis : Γ.U ≤ axis := hX12_eq_U ▸ h₁₂

  have ha_ne_E_I : a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ ha_on)
  have hI_ne_d := I_ne_d_a Γ ha ha_on
  have h_aσa_eq_aEI : a ⊔ σ_a = a ⊔ Γ.E_I := by
    have hσa_le_aEI : σ_a ≤ a ⊔ Γ.E_I := inf_le_right
    have h_lt : a < a ⊔ σ_a := lt_of_le_of_ne le_sup_left
      (fun h => hσa_ne_a ((ha.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left hσa_atom.1))
    have h_le : a ⊔ σ_a ≤ a ⊔ Γ.E_I := sup_le le_sup_left hσa_le_aEI
    have h_cov : a ⋖ a ⊔ Γ.E_I := atom_covBy_join ha Γ.hE_I_atom ha_ne_E_I
    exact (h_cov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  have h_dσ'_eq_Id : d_a ⊔ σ' = Γ.I ⊔ d_a := by
    have hσ'_le_Id : σ' ≤ Γ.I ⊔ d_a := inf_le_right
    have h_lt : d_a < d_a ⊔ σ' := lt_of_le_of_ne le_sup_left
      (fun h => hσ'_ne_d ((hd_atom.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left hσ'_atom.1))
    have h_le : d_a ⊔ σ' ≤ Γ.I ⊔ d_a := sup_le le_sup_right hσ'_le_Id
    have h_cov : d_a ⋖ Γ.I ⊔ d_a := by
      have := atom_covBy_join hd_atom Γ.hI hI_ne_d.symm
      rwa [sup_comm] at this
    exact (h_cov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  have hX13_eq : (a ⊔ σ_a) ⊓ (d_a ⊔ σ') = (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ d_a) := by
    rw [h_aσa_eq_aEI, h_dσ'_eq_Id]
  have hX13_le_axis : (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ d_a) ≤ axis := hX13_eq ▸ h₁₃

  set X₁₃ := (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ d_a) with hX13_def
  have hl_cov_π : Γ.O ⊔ Γ.U ⋖ π := l_covBy_π_inv Γ
  have ha_ne_E_I : a ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ ha_on)
  have hI_ne_d := I_ne_d_a Γ ha ha_on

  have h_aEI_inf_l : (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = a := by
    rw [show a ⊔ Γ.E_I = Γ.E_I ⊔ a from sup_comm _ _]
    exact line_direction Γ.hE_I_atom Γ.hE_I_not_l ha_on
  have h_Id_inf_l : (Γ.I ⊔ d_a) ⊓ (Γ.O ⊔ Γ.U) = Γ.I := by
    rw [show Γ.I ⊔ d_a = d_a ⊔ Γ.I from sup_comm _ _]
    exact line_direction hd_atom (d_a_not_l Γ ha ha_on ha_ne_U) Γ.hI_on

  have haEI_le_π : a ⊔ Γ.E_I ≤ π :=
    sup_le ha_le_π (Γ.hE_I_on_m.trans hm_le_π)
  have hId_le_π : Γ.I ⊔ d_a ≤ π :=
    sup_le (Γ.hI_on.trans le_sup_left) hd_le_π

  have hO_not_aEI : ¬ Γ.O ≤ a ⊔ Γ.E_I := by
    intro hO_le
    have hO_le_inf : Γ.O ≤ (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) := le_inf hO_le le_sup_left
    rw [h_aEI_inf_l] at hO_le_inf
    exact ha_ne_O ((ha.le_iff.mp hO_le_inf).resolve_left Γ.hO.1).symm
  have hE_I_ne_O : Γ.E_I ≠ Γ.O := fun h => Γ.hE_I_not_l (h ▸ le_sup_left)
  have hOa_eq_l : Γ.O ⊔ a = Γ.O ⊔ Γ.U :=
    (line_eq_of_atom_le Γ.hO Γ.hU ha Γ.hOU ha_ne_O.symm
      ha_ne_U.symm ha_on).symm
  have h_lEI_lt : Γ.O ⊔ Γ.U < Γ.O ⊔ Γ.U ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
    (fun heq => Γ.hE_I_not_l (le_sup_right.trans heq.symm.le))
  have h_lEI_le_π : Γ.O ⊔ Γ.U ⊔ Γ.E_I ≤ π :=
    sup_le le_sup_left (Γ.hE_I_on_m.trans hm_le_π)
  have h_lEI_eq_π : Γ.O ⊔ Γ.U ⊔ Γ.E_I = π :=
    (hl_cov_π.eq_or_eq h_lEI_lt.le h_lEI_le_π).resolve_left (ne_of_gt h_lEI_lt)
  have h_aEIO_eq_π : a ⊔ Γ.E_I ⊔ Γ.O = π := by
    have h1 : a ⊔ Γ.E_I ⊔ Γ.O = Γ.O ⊔ a ⊔ Γ.E_I := by
      rw [sup_comm (a ⊔ Γ.E_I) Γ.O, sup_assoc]
    rw [h1, hOa_eq_l, h_lEI_eq_π]
  have h_aEI_cov_π : a ⊔ Γ.E_I ⋖ π := by
    rw [← h_aEIO_eq_π]
    exact line_covBy_plane ha Γ.hE_I_atom Γ.hO ha_ne_E_I ha_ne_O
      hE_I_ne_O hO_not_aEI

  have h_not_aEI_le_Id : ¬ a ⊔ Γ.E_I ≤ Γ.I ⊔ d_a := by
    intro hle
    have ha_le_Id : a ≤ Γ.I ⊔ d_a := le_sup_left.trans hle
    have ha_le_inf : a ≤ (Γ.I ⊔ d_a) ⊓ (Γ.O ⊔ Γ.U) := le_inf ha_le_Id ha_on
    rw [h_Id_inf_l] at ha_le_inf
    exact ha_ne_I ((Γ.hI.le_iff.mp ha_le_inf).resolve_left ha.1)

  have hI_lt_Id : Γ.I < Γ.I ⊔ d_a := lt_of_le_of_ne le_sup_left
    (fun heq => hI_ne_d.symm ((Γ.hI.le_iff.mp
      (le_sup_right.trans heq.symm.le)).resolve_left hd_atom.1))
  have h_not_Id_le_aEI : ¬ Γ.I ⊔ d_a ≤ a ⊔ Γ.E_I := by
    intro hle
    have hI_le_aEI : Γ.I ≤ a ⊔ Γ.E_I := le_sup_left.trans hle
    have hI_le_inf : Γ.I ≤ (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) := le_inf hI_le_aEI Γ.hI_on
    rw [h_aEI_inf_l] at hI_le_inf
    exact ha_ne_I.symm ((ha.le_iff.mp hI_le_inf).resolve_left Γ.hI.1)
  have h_meet_ne : (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ d_a) ≠ ⊥ :=
    lines_meet_if_coplanar h_aEI_cov_π hId_le_π h_not_Id_le_aEI Γ.hI hI_lt_Id

  have hX13_atom : IsAtom X₁₃ :=
    meet_of_lines_is_atom ha Γ.hE_I_atom Γ.hI hd_atom ha_ne_E_I hI_ne_d
      h_not_aEI_le_Id h_meet_ne

  have hX13_le_π : X₁₃ ≤ π := inf_le_left.trans haEI_le_π

  have h_core : ¬ X₁₃ ≤ Γ.O ⊔ Γ.U := by
    intro hX_l
    have hX_le_aEI : X₁₃ ≤ a ⊔ Γ.E_I := inf_le_left
    have hX_le_Id : X₁₃ ≤ Γ.I ⊔ d_a := inf_le_right
    have hX_le_a : X₁₃ ≤ a := by
      have := le_inf hX_le_aEI hX_l
      rwa [h_aEI_inf_l] at this
    have hX_le_I : X₁₃ ≤ Γ.I := by
      have := le_inf hX_le_Id hX_l
      rwa [h_Id_inf_l] at this
    have hX_eq_a : X₁₃ = a :=
      (ha.le_iff.mp hX_le_a).resolve_left hX13_atom.1
    have hX_eq_I : X₁₃ = Γ.I :=
      (Γ.hI.le_iff.mp hX_le_I).resolve_left hX13_atom.1
    exact ha_ne_I (hX_eq_a.symm.trans hX_eq_I)

  have hU_ne_X : Γ.U ≠ X₁₃ := fun h => h_core (h ▸ le_sup_right)
  have hX_ne_O : X₁₃ ≠ Γ.O := fun h => h_core (h ▸ le_sup_left)
  have hO_not_UX : ¬ Γ.O ≤ Γ.U ⊔ X₁₃ := by
    intro hO_le

    have hUX_eq : Γ.U ⊔ X₁₃ = Γ.U ⊔ Γ.O :=
      line_eq_of_atom_le Γ.hU hX13_atom Γ.hO hU_ne_X Γ.hOU.symm hX_ne_O hO_le
    have hUX_eq_l : Γ.U ⊔ X₁₃ = Γ.O ⊔ Γ.U := hUX_eq.trans (sup_comm _ _)
    exact h_core (le_sup_right.trans hUX_eq_l.le)

  have hUX_le_π : Γ.U ⊔ X₁₃ ≤ π :=
    sup_le (le_sup_right.trans le_sup_left) hX13_le_π
  have hl_lt_lX : Γ.O ⊔ Γ.U < Γ.O ⊔ Γ.U ⊔ X₁₃ := lt_of_le_of_ne le_sup_left
    (fun heq => h_core (le_sup_right.trans heq.symm.le))
  have hlX_le_π : Γ.O ⊔ Γ.U ⊔ X₁₃ ≤ π := sup_le le_sup_left hX13_le_π
  have hlX_eq_π : Γ.O ⊔ Γ.U ⊔ X₁₃ = π :=
    (hl_cov_π.eq_or_eq hl_lt_lX.le hlX_le_π).resolve_left (ne_of_gt hl_lt_lX)
  have h_UXO_eq_π : Γ.U ⊔ X₁₃ ⊔ Γ.O = π := by
    have h1 : Γ.U ⊔ X₁₃ ⊔ Γ.O = Γ.O ⊔ Γ.U ⊔ X₁₃ := by
      rw [sup_comm (Γ.U ⊔ X₁₃) Γ.O, sup_assoc]
    rw [h1, hlX_eq_π]

  have hcov_UX13 : Γ.U ⊔ X₁₃ ⋖ π := by
    rw [← h_UXO_eq_π]
    exact line_covBy_plane Γ.hU hX13_atom Γ.hO hU_ne_X Γ.hOU.symm hX_ne_O hO_not_UX
  exact collinear_of_common_bound hcov_UX13 h_axis_le h_axis_ne
    hU_le_axis hX13_le_axis h₂₃

private theorem axis_to_sigma_a_le (Γ : CoordSystem L)
    {a : L} (_ha : IsAtom a) (_ha_on : a ≤ Γ.O ⊔ Γ.U)
    (_ha_ne_O : a ≠ Γ.O) (_ha_ne_U : a ≠ Γ.U)
    (_ha_ne_inv : a ≠ coord_inv Γ a)
    (_R : L) (_hR : IsAtom _R) (_hR_not : ¬ _R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (_h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q)
    (_h_axis : (coord_inv Γ a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I)) ⊓
      ((coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
         (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V))) ≤
      Γ.U ⊔ (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V))) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤
      Γ.I ⊔ (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  sorry

private theorem sigma_a_le_I_sup_d_inv_distinct (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (ha_ne_inv : a ≠ coord_inv Γ a)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤
      Γ.I ⊔ (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
  axis_to_sigma_a_le Γ ha ha_on ha_ne_O ha_ne_U ha_ne_inv R hR hR_not h_irred
    (coord_first_desargues_mul Γ ha ha_on ha_ne_O ha_ne_U ha_ne_inv R hR hR_not h_irred)

private theorem sigma_a_le_I_sup_d_inv (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤
      Γ.I ⊔ (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  by_cases ha_self : a = coord_inv Γ a
  ·

    have h := sigma_inv_eq_sigma_prime Γ ha ha_on ha_ne_U
    rw [← ha_self] at h
    rw [h, ← ha_self]
    exact inf_le_right
  · exact sigma_a_le_I_sup_d_inv_distinct Γ ha ha_on ha_ne_O ha_ne_U
      ha_self R hR hR_not h_irred

theorem coord_mul_left_inv (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_mul Γ (coord_inv Γ a) a = Γ.I := by
  unfold coord_mul
  set σ_a := (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) with hσa_def
  set d_inv := (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) with hdinv_def
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have hσa_ne_E := sigma_a_ne_E Γ ha ha_on ha_ne_U
  have hinv_atom : IsAtom (coord_inv Γ a) := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_on : coord_inv Γ a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a
  have hinv_ne_U : coord_inv Γ a ≠ Γ.U := coord_inv_ne_U Γ ha ha_on ha_ne_O
  have hd_inv_atom : IsAtom d_inv := d_a_atom Γ hinv_atom hinv_on
  have hd_inv_not_l : ¬ d_inv ≤ Γ.O ⊔ Γ.U := d_a_not_l Γ hinv_atom hinv_on hinv_ne_U
  have hI_ne_dinv : Γ.I ≠ d_inv := I_ne_d_a Γ hinv_atom hinv_on

  have hσa_le_Id : σ_a ≤ Γ.I ⊔ d_inv :=
    sigma_a_le_I_sup_d_inv Γ ha ha_on ha_ne_O ha_ne_U R hR hR_not h_irred

  have hσa_ne_dinv : σ_a ≠ d_inv := by
    intro h
    have hσa_le_m : σ_a ≤ Γ.U ⊔ Γ.V := h.symm ▸ inf_le_right
    have hσa_le_OC : σ_a ≤ Γ.O ⊔ Γ.C := inf_le_left
    have hσa_le_E : σ_a ≤ Γ.E := by
      unfold CoordSystem.E CoordSystem.m
      exact le_inf hσa_le_OC hσa_le_m
    exact hσa_ne_E ((Γ.hE_atom.le_iff.mp hσa_le_E).resolve_left hσa_atom.1)

  have hσd_le_Id : σ_a ⊔ d_inv ≤ Γ.I ⊔ d_inv := sup_le hσa_le_Id le_sup_right
  have hd_lt_σd : d_inv < σ_a ⊔ d_inv := lt_of_le_of_ne le_sup_right
    (fun h => hσa_ne_dinv ((hd_inv_atom.le_iff.mp
      (le_sup_left.trans h.symm.le)).resolve_left hσa_atom.1))
  have hcov_d : d_inv ⋖ Γ.I ⊔ d_inv := by
    have h2 : d_inv ⋖ d_inv ⊔ Γ.I := atom_covBy_join hd_inv_atom Γ.hI hI_ne_dinv.symm
    exact (sup_comm d_inv Γ.I) ▸ h2
  have hσd_eq : σ_a ⊔ d_inv = Γ.I ⊔ d_inv :=
    (hcov_d.eq_or_eq hd_lt_σd.le hσd_le_Id).resolve_left (ne_of_gt hd_lt_σd)

  show (σ_a ⊔ d_inv) ⊓ (Γ.O ⊔ Γ.U) = Γ.I
  rw [hσd_eq, show Γ.I ⊔ d_inv = d_inv ⊔ Γ.I from sup_comm _ _]
  exact line_direction hd_inv_atom hd_inv_not_l Γ.hI_on

end Foam.Bridges
