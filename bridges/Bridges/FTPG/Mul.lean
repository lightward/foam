import Bridges.FTPG.Coord
import Bridges.FTPG.AddComm
import Bridges.FTPG.Parallelogram

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

noncomputable def CoordSystem.E_I (Γ : CoordSystem L) : L := (Γ.I ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)

variable (Γ : CoordSystem L)

theorem CoordSystem.hI_not_m : ¬ Γ.I ≤ Γ.U ⊔ Γ.V :=
  fun h => Γ.hUI (Γ.atom_on_both_eq_U Γ.hI Γ.hI_on h).symm

theorem CoordSystem.hE_I_atom : IsAtom Γ.E_I :=
  line_meets_m_at_atom Γ.hI Γ.hC (fun h => Γ.hC_not_l (h ▸ Γ.hI_on))
    (sup_le (Γ.hI_on.trans le_sup_left) Γ.hC_plane)
    (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    Γ.m_covBy_π Γ.hI_not_m

theorem CoordSystem.hE_I_on_m : Γ.E_I ≤ Γ.U ⊔ Γ.V := inf_le_right

theorem CoordSystem.hE_I_le_IC : Γ.E_I ≤ Γ.I ⊔ Γ.C := inf_le_left

theorem CoordSystem.hE_I_not_OC : ¬ Γ.E_I ≤ Γ.O ⊔ Γ.C := by
  intro h
  have hIC : Γ.I ≠ Γ.C := fun h' => Γ.hC_not_l (h' ▸ Γ.hI_on)
  have hOC : Γ.O ≠ Γ.C := fun h' => Γ.hC_not_l (h' ▸ le_sup_left)
  have hEI_ne_C : Γ.E_I ≠ Γ.C := fun h' => Γ.hC_not_m (h' ▸ Γ.hE_I_on_m)

  have hEI_eq_E : Γ.E_I = Γ.E :=
    (Γ.hE_atom.le_iff.mp (le_inf h Γ.hE_I_on_m)).resolve_left Γ.hE_I_atom.1

  have hCEI_eq_IC : Γ.C ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
    ((sup_comm Γ.C Γ.I ▸ atom_covBy_join Γ.hC Γ.hI hIC.symm).eq_or_eq
      (lt_of_le_of_ne le_sup_left (fun h' => hEI_ne_C
        ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_I_atom.1))).le
      (sup_le le_sup_right Γ.hE_I_le_IC)).resolve_left
      (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h' => hEI_ne_C
        ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_I_atom.1))))

  have hE_ne_C : Γ.E ≠ Γ.C := fun h' => Γ.hC_not_m (h' ▸ CoordSystem.hE_on_m)
  have hCE_eq_OC : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C :=
    ((sup_comm Γ.C Γ.O ▸ atom_covBy_join Γ.hC Γ.hO hOC.symm).eq_or_eq
      (lt_of_le_of_ne le_sup_left (fun h' => hE_ne_C
        ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_atom.1))).le
      (sup_le le_sup_right CoordSystem.hE_le_OC)).resolve_left
      (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h' => hE_ne_C
        ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_atom.1))))

  have hI_le : Γ.I ≤ Γ.O ⊔ Γ.C := by
    have : Γ.I ⊔ Γ.C = Γ.O ⊔ Γ.C := by rw [← hCEI_eq_IC, hEI_eq_E, hCE_eq_OC]
    exact le_sup_left.trans this.le

  have h_lOC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm Γ.O Γ.C]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l le_sup_left
  exact Γ.hOI.symm ((Γ.hO.le_iff.mp ((le_inf Γ.hI_on hI_le).trans h_lOC.le)).resolve_left
    Γ.hI.1)

theorem CoordSystem.hE_I_ne_E : Γ.E_I ≠ Γ.E :=
  fun h => Γ.hE_I_not_OC (h ▸ CoordSystem.hE_le_OC)

theorem CoordSystem.hE_I_not_l : ¬ Γ.E_I ≤ Γ.O ⊔ Γ.U := by
  intro h
  have : Γ.E_I ≤ Γ.U := (le_inf h Γ.hE_I_on_m).trans Γ.l_inf_m_eq_U.le
  have hEI_eq_U : Γ.E_I = Γ.U :=
    (Γ.hU.le_iff.mp this).resolve_left Γ.hE_I_atom.1

  have hI_eq_U : Γ.I = Γ.U := by
    have hU_le_IC : Γ.U ≤ Γ.I ⊔ Γ.C := hEI_eq_U ▸ Γ.hE_I_le_IC
    have h_lIC := inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (Γ.hI_on : Γ.I ≤ Γ.O ⊔ Γ.U)

    rw [sup_comm Γ.C Γ.I] at h_lIC
    exact ((Γ.hI.le_iff.mp ((le_inf (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U) hU_le_IC).trans
      h_lIC.le)).resolve_left Γ.hU.1).symm
  exact Γ.hUI hI_eq_U.symm

noncomputable def coord_mul (Γ : CoordSystem L) (a b : L) : L :=
  ((Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ Γ.U)

theorem coord_mul_eq_two_persp (Γ : CoordSystem L) (a b : L) :
    coord_mul Γ a b = two_persp Γ (Γ.O ⊔ Γ.C) (b ⊔ Γ.E_I) (a ⊔ Γ.C) (Γ.U ⊔ Γ.V) := rfl

private theorem EI_sup_OC_eq_π : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
  have h_lt : Γ.O ⊔ Γ.C < Γ.E_I ⊔ (Γ.O ⊔ Γ.C) :=
    lt_of_le_of_ne le_sup_right (fun h => Γ.hE_I_not_OC (h ▸ le_sup_left))
  have h_le : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (Γ.hE_I_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
      (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane)
  exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)

theorem coord_mul_left_one (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    coord_mul Γ Γ.I a = a := by
  unfold coord_mul

  change ((Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = a

  have haEI_le_π : a ⊔ Γ.E_I ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (ha_on.trans le_sup_left)
      (Γ.hE_I_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
  have hED : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ⊔ Γ.E_I = a ⊔ Γ.E_I :=
    calc (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ⊔ Γ.E_I
        = Γ.E_I ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) := sup_comm _ _
      _ = (Γ.E_I ⊔ (Γ.O ⊔ Γ.C)) ⊓ (a ⊔ Γ.E_I) :=
            (sup_inf_assoc_of_le _ le_sup_right).symm
      _ = (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊓ (a ⊔ Γ.E_I) := by rw [EI_sup_OC_eq_π]
      _ = a ⊔ Γ.E_I := inf_eq_right.mpr haEI_le_π
  rw [hED]

  have ha_le : a ≤ (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left ha_on
  have haEI : a ≠ Γ.E_I := fun h => ha_ne_U
    (Γ.atom_on_both_eq_U ha ha_on (h ▸ Γ.hE_I_on_m))
  have h_lt : (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro h
    have hl_le : Γ.O ⊔ Γ.U ≤ a ⊔ Γ.E_I := inf_eq_right.mp h
    have h_eq := ((atom_covBy_join ha Γ.hE_I_atom haEI).eq_or_eq
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le hl_le).resolve_left
      (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)
    exact Γ.hE_I_not_l (le_sup_right.trans (le_of_eq h_eq.symm))
  exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le ha.bot_lt ha_le) h_lt
    |>.le_iff.mp ha_le).resolve_left ha.1).symm

private theorem I_sup_EI_eq_IC : Γ.I ⊔ Γ.E_I = Γ.I ⊔ Γ.C := by
  have hIEI_le : Γ.I ⊔ Γ.E_I ≤ Γ.I ⊔ Γ.C := sup_le le_sup_left Γ.hE_I_le_IC
  have hI_ne_EI : Γ.I ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ Γ.hI_on)
  have hIC : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  exact ((atom_covBy_join Γ.hI Γ.hC hIC).eq_or_eq
    (atom_covBy_join Γ.hI Γ.hE_I_atom hI_ne_EI).lt.le hIEI_le).resolve_left
    (ne_of_gt (atom_covBy_join Γ.hI Γ.hE_I_atom hI_ne_EI).lt)

private theorem OC_inf_IC_eq_C : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ Γ.C) = Γ.C := by
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hIC : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hI_not_OC : ¬ Γ.I ≤ Γ.O ⊔ Γ.C := by
    intro h
    have hI_le : Γ.I ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) := le_inf Γ.hI_on h
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _,
        inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)] at hI_le
    exact Γ.hOI ((Γ.hO.le_iff.mp hI_le).resolve_left Γ.hI.1).symm
  rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _,
      show Γ.I ⊔ Γ.C = Γ.C ⊔ Γ.I from sup_comm _ _]
  exact modular_intersection Γ.hC Γ.hO Γ.hI hOC.symm hIC.symm Γ.hOI
    (show ¬ Γ.I ≤ Γ.C ⊔ Γ.O from sup_comm Γ.O Γ.C ▸ hI_not_OC)

theorem coord_mul_right_one (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    coord_mul Γ a Γ.I = a := by
  unfold coord_mul
  rw [I_sup_EI_eq_IC, OC_inf_IC_eq_C]

  have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have ha'C_le : Γ.C ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ a ⊔ Γ.C :=
    sup_le le_sup_right inf_le_left
  have ha_lt_aC : a < a ⊔ Γ.C := by
    apply lt_of_le_of_ne le_sup_left; intro h
    exact Γ.hC_not_l ((ha.le_iff.mp (h ▸ le_sup_right)).resolve_left Γ.hC.1 ▸ ha_on)
  have ha'_ne_bot : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠ ⊥ := by
    have h_meet := lines_meet_if_coplanar Γ.m_covBy_π
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane)
      (fun h => Γ.hC_not_m (le_trans le_sup_right h))
      ha ha_lt_aC
    rwa [@inf_comm L _] at h_meet
  have hC_lt : Γ.C < Γ.C ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
    apply lt_of_le_of_ne le_sup_left; intro h
    have ha'_le_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.C := le_sup_right.trans h.symm.le
    have hCm : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ := by
      rcases Γ.hC.le_iff.mp inf_le_left with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right) Γ.hC_not_m
    have : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ ⊥ := hCm ▸ le_inf ha'_le_C inf_le_right
    exact ha'_ne_bot (le_antisymm this bot_le)
  have h_cov_Ca : Γ.C ⋖ a ⊔ Γ.C := by
    have := atom_covBy_join Γ.hC ha hAC.symm; rwa [sup_comm] at this
  have ha'C_eq : Γ.C ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = a ⊔ Γ.C :=
    (h_cov_Ca.eq_or_eq hC_lt.le ha'C_le).resolve_left (ne_of_gt hC_lt)
  rw [ha'C_eq]

  have ha_le : a ≤ (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) := le_inf le_sup_left ha_on
  have h_lt : (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro h
    have hl_le := inf_eq_right.mp h
    have h_eq := ((atom_covBy_join ha Γ.hC hAC).eq_or_eq
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le hl_le).resolve_left
      (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)
    exact Γ.hC_not_l (le_sup_right.trans (le_of_eq h_eq.symm))
  exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le ha.bot_lt ha_le) h_lt
    |>.le_iff.mp ha_le).resolve_left ha.1).symm

private theorem OC_inf_l_eq_O : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.O := by
  rw [sup_comm Γ.O Γ.C, inf_comm]
  exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l le_sup_left

private theorem E_sup_EI_eq_m : Γ.E ⊔ Γ.E_I = Γ.U ⊔ Γ.V := by
  have hE_lt : Γ.E < Γ.E ⊔ Γ.E_I :=
    lt_of_le_of_ne le_sup_left (fun h => Γ.hE_I_ne_E
      ((Γ.hE_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_I_atom.1))

  have hE_covBy_m : Γ.E ⋖ Γ.U ⊔ Γ.V := by
    rw [← CoordSystem.EU_eq_m]
    exact atom_covBy_join Γ.hE_atom Γ.hU CoordSystem.hEU
  exact (hE_covBy_m.eq_or_eq hE_lt.le
    (sup_le CoordSystem.hE_on_m Γ.hE_I_on_m)).resolve_left (ne_of_gt hE_lt)

private theorem hC_ne_EI : Γ.C ≠ Γ.E_I :=
  fun h => Γ.hC_not_m (h ▸ Γ.hE_I_on_m)

theorem coord_mul_left_zero (Γ : CoordSystem L)
    (b : L) (hb : IsAtom b) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hb_ne_U : b ≠ Γ.U) :
    coord_mul Γ Γ.O b = Γ.O := by
  unfold coord_mul

  change ((Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = Γ.O
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hb_ne_EI : b ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hb_on)

  have h_upper : ((Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) ≤ Γ.O := by
    calc _ ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) :=
          inf_le_inf_right _ (sup_le inf_le_left CoordSystem.hE_le_OC)
      _ = Γ.O := OC_inf_l_eq_O Γ

  have hσ_ne_E : (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ≠ Γ.E := by
    intro h
    have hE_le : Γ.E ≤ b ⊔ Γ.E_I := h ▸ inf_le_right
    have hm_le : Γ.U ⊔ Γ.V ≤ b ⊔ Γ.E_I := by
      rw [← E_sup_EI_eq_m]; exact sup_le hE_le le_sup_right

    have hEI_covBy : Γ.E_I ⋖ b ⊔ Γ.E_I := by
      rw [sup_comm]; exact atom_covBy_join Γ.hE_I_atom hb hb_ne_EI.symm
    have hEI_lt_m : Γ.E_I < Γ.U ⊔ Γ.V := by
      apply lt_of_le_of_ne Γ.hE_I_on_m; intro h_eq
      exact Γ.hE_I_not_l (((Γ.hE_I_atom.le_iff.mp
        (le_sup_left.trans h_eq.symm.le)).resolve_left Γ.hU.1).symm.le.trans le_sup_right)
    have hm_eq : Γ.U ⊔ Γ.V = b ⊔ Γ.E_I :=
      (hEI_covBy.eq_or_eq hEI_lt_m.le hm_le).resolve_left (ne_of_gt hEI_lt_m)
    have hb_on_m : b ≤ Γ.U ⊔ Γ.V := le_sup_left.trans hm_eq.symm.le
    exact hb_ne_U (Γ.atom_on_both_eq_U hb hb_on hb_on_m)

  have hσ_ne_bot : (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ≠ ⊥ := by
    apply lines_meet_if_coplanar (CoordSystem.OC_covBy_π Γ)
      (sup_le (hb_on.trans le_sup_left)
        (Γ.hE_I_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)))
      (fun h => Γ.hE_I_not_OC (le_sup_right.trans h))
      hb
    exact lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_EI ((hb.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_I_atom.1).symm)

  have hσ_not_le_E : ¬ ((Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ≤ Γ.E) :=
    fun h => (Γ.hE_atom.le_iff.mp h).elim (fun h => hσ_ne_bot h) (fun h => hσ_ne_E h)
  have hE_lt : Γ.E < (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ Γ.E :=
    lt_of_le_of_ne le_sup_right (fun h => hσ_not_le_E (h ▸ le_sup_left))
  have hσE_eq : (Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ Γ.E = Γ.O ⊔ Γ.C :=
    ((line_covers_its_atoms Γ.hO Γ.hC hOC Γ.hE_atom CoordSystem.hE_le_OC).eq_or_eq
      hE_lt.le (sup_le inf_le_left CoordSystem.hE_le_OC)).resolve_left (ne_of_gt hE_lt)

  rw [hσE_eq, OC_inf_l_eq_O]

theorem coord_mul_right_zero (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    coord_mul Γ a Γ.O = Γ.O := by
  unfold coord_mul

  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hOE_I : Γ.O ≠ Γ.E_I := fun h => Γ.hO_not_m (h ▸ Γ.hE_I_on_m)
  have hC_ne_EI : Γ.C ≠ Γ.E_I := fun h => Γ.hC_not_m (h ▸ Γ.hE_I_on_m)

  have hEI_not_OC := Γ.hE_I_not_OC

  have h_first : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.E_I) = Γ.O :=
    modular_intersection Γ.hO Γ.hC Γ.hE_I_atom hOC hOE_I hC_ne_EI hEI_not_OC
  rw [h_first]

  set d_a := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have ha_not_m : ¬ a ≤ Γ.U ⊔ Γ.V :=
    fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hda_atom : IsAtom d_a :=
    line_meets_m_at_atom ha Γ.hC hAC
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
      Γ.m_covBy_π ha_not_m
  have hda_on_m : d_a ≤ Γ.U ⊔ Γ.V := inf_le_right
  have hda_ne_O : d_a ≠ Γ.O := fun h => Γ.hO_not_m (h ▸ hda_on_m)

  have hda_not_l : ¬ d_a ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hda_le_U : d_a ≤ Γ.U := by
      rw [← Γ.l_inf_m_eq_U]; exact le_inf h hda_on_m
    have hda_eq_U : d_a = Γ.U :=
      (Γ.hU.le_iff.mp hda_le_U).resolve_left hda_atom.1

    have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := hda_eq_U ▸ inf_le_left
    have hU_le_lq : Γ.U ≤ (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) := le_inf le_sup_right hU_le_aC
    have ha_le_lq : a ≤ (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) := le_inf ha_on le_sup_left

    have h_lt : (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) < Γ.O ⊔ Γ.U := by
      apply lt_of_le_of_ne inf_le_left; intro h

      have hl_le := inf_eq_left.mp h
      exact Γ.hC_not_l (le_sup_right.trans
        ((atom_covBy_join ha Γ.hC hAC).eq_or_eq
          (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le hl_le
        |>.resolve_left (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)).symm.le)
    have h_atom := line_height_two Γ.hO Γ.hU Γ.hOU
      (lt_of_lt_of_le ha.bot_lt ha_le_lq) h_lt
    exact ha_ne_U ((h_atom.le_iff.mp hU_le_lq).resolve_left Γ.hU.1 ▸
      (h_atom.le_iff.mp ha_le_lq).resolve_left ha.1)

  have hO_le : Γ.O ≤ (Γ.O ⊔ d_a) ⊓ (Γ.O ⊔ Γ.U) :=
    le_inf le_sup_left le_sup_left
  have h_lt : (Γ.O ⊔ d_a) ⊓ (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_right; intro h

    have hl_le : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ d_a := inf_eq_right.mp h
    have h_eq := ((atom_covBy_join Γ.hO hda_atom hda_ne_O.symm).eq_or_eq
      (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le hl_le).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)
    exact hda_not_l (le_sup_right.trans h_eq.symm.le)
  exact ((line_height_two Γ.hO Γ.hU Γ.hOU (lt_of_lt_of_le Γ.hO.bot_lt hO_le) h_lt
    |>.le_iff.mp hO_le).resolve_left Γ.hO.1).symm

theorem coord_mul_atom (Γ : CoordSystem L)
    (a c : L) (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (_hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U) :
    IsAtom (coord_mul Γ a c) := by
  set l := Γ.O ⊔ Γ.U
  set m := Γ.U ⊔ Γ.V
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  show IsAtom (((Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) ⊔ (a ⊔ Γ.C) ⊓ m) ⊓ l)
  set σ_c := (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I)
  set d_a := (a ⊔ Γ.C) ⊓ m
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right

  have hda_atom : IsAtom d_a :=
    line_meets_m_at_atom ha Γ.hC ha_ne_C
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane) hm_le_π Γ.m_covBy_π ha_not_m

  have hda_not_l : ¬ d_a ≤ l := by
    intro h
    have hda_le_U : d_a ≤ Γ.U := Γ.l_inf_m_eq_U ▸ le_inf h inf_le_right
    have hda_eq_U := (Γ.hU.le_iff.mp hda_le_U).resolve_left hda_atom.1
    have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := hda_eq_U ▸ inf_le_left
    have h_lt : (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) < Γ.O ⊔ Γ.U := by
      apply lt_of_le_of_ne inf_le_left; intro h
      exact Γ.hC_not_l (le_sup_right.trans
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq
          (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le (inf_eq_left.mp h)
        |>.resolve_left (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)).symm.le)
    have h_atom := line_height_two Γ.hO Γ.hU Γ.hOU
      (lt_of_lt_of_le ha.bot_lt (le_inf ha_on le_sup_left)) h_lt
    exact ha_ne_U ((h_atom.le_iff.mp (le_inf le_sup_right hU_le_aC)).resolve_left Γ.hU.1 ▸
      (h_atom.le_iff.mp (le_inf ha_on le_sup_left)).resolve_left ha.1)

  have hc_ne_EI : c ≠ Γ.E_I :=
    fun h => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on (h ▸ Γ.hE_I_on_m))
  have hσ_atom : IsAtom σ_c := by

    have h_eq : σ_c = (c ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) := inf_comm _ _
    rw [h_eq]

    have hEI_sup_OC : Γ.E_I ⊔ (Γ.O ⊔ Γ.C) = π := by
      have h_lt : Γ.O ⊔ Γ.C < Γ.E_I ⊔ (Γ.O ⊔ Γ.C) :=
        lt_of_le_of_ne le_sup_right (fun h => Γ.hE_I_not_OC (h ▸ le_sup_left))
      exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq h_lt.le
        (sup_le (Γ.hE_I_on_m.trans hm_le_π) (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane))
      ).resolve_left (ne_of_gt h_lt)

    have h_coplanar : c ⊔ Γ.E_I ≤ (Γ.O ⊔ Γ.C) ⊔ Γ.E_I := by
      rw [sup_comm (Γ.O ⊔ Γ.C) Γ.E_I, hEI_sup_OC]
      exact sup_le (hc_on.trans le_sup_left) (Γ.hE_I_on_m.trans hm_le_π)
    exact perspect_atom Γ.hE_I_atom hc hc_ne_EI Γ.hO Γ.hC hOC Γ.hE_I_not_OC h_coplanar

  have hda_ne_σ : d_a ≠ σ_c := by
    intro h_eq
    have hda_le_OC : d_a ≤ Γ.O ⊔ Γ.C := h_eq ▸ inf_le_left
    have hda_eq_E : d_a = Γ.E := by
      have h1 : d_a ≤ Γ.E := by
        show d_a ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
        exact le_inf hda_le_OC inf_le_right
      exact (Γ.hE_atom.le_iff.mp h1).resolve_left hda_atom.1
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := hda_eq_E ▸ inf_le_left
    have hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C := CoordSystem.hE_le_OC
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have hOa_eq_l : Γ.O ⊔ a = l := by
        have h_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
          (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
        exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
          (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt h_lt)
      have hl_le_aC : l ≤ a ⊔ Γ.C := hOa_eq_l.symm.le.trans (sup_le hle le_sup_left)
      exact Γ.hC_not_l (le_sup_right.trans
        ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq
          (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt.le hl_le_aC
        |>.resolve_left (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)).symm.le)
    have hmod := modular_intersection Γ.hC ha Γ.hO ha_ne_C.symm hOC.symm ha_ne_O
      (show ¬ Γ.O ≤ Γ.C ⊔ a from by rw [sup_comm]; exact hO_not_aC)
    have hE_le_C : Γ.E ≤ Γ.C :=
      calc Γ.E ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.O) :=
            le_inf (by rw [sup_comm]; exact hE_le_aC) (by rw [sup_comm]; exact hE_le_OC)
        _ = Γ.C := hmod
    have hE_eq_C := (Γ.hC.le_iff.mp hE_le_C).resolve_left Γ.hE_atom.1
    exact Γ.hC_not_m (hE_eq_C ▸ CoordSystem.hE_on_m)

  have hσ_plane : σ_c ≤ π :=
    (inf_le_left : σ_c ≤ Γ.O ⊔ Γ.C).trans (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane)
  have hda_plane : d_a ≤ π := (inf_le_right : d_a ≤ m).trans hm_le_π
  have hl_covBy : l ⋖ π := by
    have hV_disj : Γ.V ⊓ l = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ l = π from by
      show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V; rw [sup_comm]] at this
  have hl_sup_da : l ⊔ d_a = π :=
    (hl_covBy.eq_or_eq (lt_of_le_of_ne le_sup_left
      (fun h => hda_not_l (le_sup_right.trans h.symm.le))).le
      (sup_le le_sup_left hda_plane)).resolve_left
      (ne_of_gt (lt_of_le_of_ne le_sup_left
        (fun h => hda_not_l (le_sup_right.trans h.symm.le))))
  exact perspect_atom hda_atom hσ_atom hda_ne_σ.symm Γ.hO Γ.hU Γ.hOU hda_not_l
    (hl_sup_da.symm ▸ sup_le hσ_plane hda_plane)

/-- info: 'Foam.Bridges.CoordSystem.hI_not_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CoordSystem.hI_not_m

/-- info: 'Foam.Bridges.CoordSystem.hE_I_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CoordSystem.hE_I_atom

/-- info: 'Foam.Bridges.CoordSystem.hE_I_on_m' does not depend on any axioms -/
#guard_msgs in #print axioms CoordSystem.hE_I_on_m

/-- info: 'Foam.Bridges.CoordSystem.hE_I_le_IC' does not depend on any axioms -/
#guard_msgs in #print axioms CoordSystem.hE_I_le_IC

/-- info: 'Foam.Bridges.CoordSystem.hE_I_not_OC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CoordSystem.hE_I_not_OC

/-- info: 'Foam.Bridges.CoordSystem.hE_I_ne_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CoordSystem.hE_I_ne_E

/-- info: 'Foam.Bridges.CoordSystem.hE_I_not_l' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CoordSystem.hE_I_not_l

/-- info: 'Foam.Bridges.coord_mul_eq_two_persp' does not depend on any axioms -/
#guard_msgs in #print axioms coord_mul_eq_two_persp

/-- info: 'Foam.Bridges.coord_mul_left_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_mul_left_one

/-- info: 'Foam.Bridges.coord_mul_right_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_mul_right_one

/-- info: 'Foam.Bridges.coord_mul_left_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_mul_left_zero

/-- info: 'Foam.Bridges.coord_mul_right_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_mul_right_zero

/-- info: 'Foam.Bridges.coord_mul_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_mul_atom

end Foam.Bridges
