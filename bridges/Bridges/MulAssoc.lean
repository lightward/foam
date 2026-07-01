import Bridges.MulKeyIdentity

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

theorem dilation_determined_by_param (Γ : CoordSystem L)
    {a₁ a₂ P : L} (ha₁ : IsAtom a₁) (ha₂ : IsAtom a₂)
    (ha₁_on : a₁ ≤ Γ.O ⊔ Γ.U) (ha₂_on : a₂ ≤ Γ.O ⊔ Γ.U)
    (_ha₁_ne_O : a₁ ≠ Γ.O) (_ha₂_ne_O : a₂ ≠ Γ.O)
    (_ha₁_ne_U : a₁ ≠ Γ.U) (_ha₂_ne_U : a₂ ≠ Γ.U)
    (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (_hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (_hP_ne_I : P ≠ Γ.I)
    (h_agree : dilation_ext Γ a₁ P = dilation_ext Γ a₂ P) :
    a₁ = a₂ := by
  set l := Γ.O ⊔ Γ.U
  set m := Γ.U ⊔ Γ.V
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set d_P := (Γ.I ⊔ P) ⊓ m

  have hP_ne_O : P ≠ Γ.O := fun h => hP_not_l (h ▸ le_sup_left)
  have hP_ne_I : P ≠ Γ.I := fun h => hP_not_l (h ▸ Γ.hI_on)
  have hm_le_π : m ≤ π :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right

  have hd_P_atom : IsAtom d_P :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m

  have hI_covBy_IP : Γ.I ⋖ Γ.I ⊔ P := atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)
  have hI_lt_l : Γ.I < l := by
    show Γ.I < Γ.O ⊔ Γ.U
    exact lt_of_le_of_ne Γ.hI_on
      (fun h => Γ.hOI ((Γ.hI.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left Γ.hO.1))

  have hd_P_ne_U : d_P ≠ Γ.U := by
    intro h
    have hU_le_IP : Γ.U ≤ Γ.I ⊔ P := h.symm.le.trans inf_le_left
    have hIU_le_IP : Γ.I ⊔ Γ.U ≤ Γ.I ⊔ P := sup_le le_sup_left hU_le_IP
    have hIU_eq_l : Γ.I ⊔ Γ.U = l := by
      show Γ.I ⊔ Γ.U = Γ.O ⊔ Γ.U
      have hU_lt : Γ.U < Γ.I ⊔ Γ.U := lt_of_le_of_ne le_sup_right
        (fun h => Γ.hUI ((Γ.hU.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left Γ.hI.1).symm)
      have hU_covBy_l : Γ.U ⋖ Γ.O ⊔ Γ.U := by
        rw [sup_comm]; exact atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm
      exact (hU_covBy_l.eq_or_eq hU_lt.le (sup_le Γ.hI_on le_sup_right)).resolve_left
        (ne_of_gt hU_lt)
    have hl_le_IP : l ≤ Γ.I ⊔ P := hIU_eq_l ▸ hIU_le_IP
    have hl_eq_IP : l = Γ.I ⊔ P :=
      (hI_covBy_IP.eq_or_eq hI_lt_l.le hl_le_IP).resolve_left (ne_of_gt hI_lt_l)
    exact hP_not_l (le_sup_right.trans hl_eq_IP.symm.le)

  have hd_P_not_l : ¬ d_P ≤ l := by
    intro h
    have hd_le_U : d_P ≤ Γ.U := by
      have h_meet : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := Γ.l_inf_m_eq_U
      exact h_meet ▸ le_inf h inf_le_right
    exact hd_P_ne_U ((Γ.hU.le_iff.mp hd_le_U).resolve_left hd_P_atom.1)

  have hd_P_not_OP : ¬ d_P ≤ Γ.O ⊔ P := by
    intro h
    have hO_not_IP : ¬ Γ.O ≤ Γ.I ⊔ P := by
      intro hO_le
      have hOI_le_IP : Γ.O ⊔ Γ.I ≤ Γ.I ⊔ P := sup_le hO_le le_sup_left
      have hOI_eq_l : Γ.O ⊔ Γ.I = l := by
        show Γ.O ⊔ Γ.I = Γ.O ⊔ Γ.U
        have hO_lt : Γ.O < Γ.O ⊔ Γ.I := lt_of_le_of_ne le_sup_left
          (fun h => Γ.hOI ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hI.1).symm)
        exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
          (sup_le le_sup_left Γ.hI_on)).resolve_left (ne_of_gt hO_lt)
      have hl_le_IP : l ≤ Γ.I ⊔ P := hOI_eq_l ▸ hOI_le_IP
      have hl_eq_IP : l = Γ.I ⊔ P :=
        (hI_covBy_IP.eq_or_eq hI_lt_l.le hl_le_IP).resolve_left (ne_of_gt hI_lt_l)
      exact hP_not_l (le_sup_right.trans hl_eq_IP.symm.le)
    have hPI_PO_eq_P : (P ⊔ Γ.I) ⊓ (P ⊔ Γ.O) = P :=
      modular_intersection hP Γ.hI Γ.hO hP_ne_I hP_ne_O Γ.hOI.symm
        (fun h => hO_not_IP (sup_comm P Γ.I ▸ h))
    have hd_le_meet : d_P ≤ (P ⊔ Γ.I) ⊓ (P ⊔ Γ.O) := by
      rw [show P ⊔ Γ.I = Γ.I ⊔ P from sup_comm _ _,
          show P ⊔ Γ.O = Γ.O ⊔ P from sup_comm _ _]
      exact le_inf inf_le_left h
    have hd_le_P : d_P ≤ P := hd_le_meet.trans hPI_PO_eq_P.le
    have hd_eq_P : d_P = P := (hP.le_iff.mp hd_le_P).resolve_left hd_P_atom.1
    exact hP_not_m (hd_eq_P ▸ (inf_le_right : d_P ≤ m))

  have hl_covBy_π : l ⋖ π := by
    show Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
    have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  have hOP_covBy_π : Γ.O ⊔ P ⋖ π := by
    have hU_not_OP : ¬ Γ.U ≤ Γ.O ⊔ P := by
      intro h
      have hOU_le_OP : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ P := sup_le le_sup_left h
      have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
      have hO_lt_l : Γ.O < l :=
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
      have hl_eq_OP : l = Γ.O ⊔ P :=
        (hO_covBy_OP.eq_or_eq hO_lt_l.le hOU_le_OP).resolve_left (ne_of_gt hO_lt_l)
      exact hP_not_l (le_sup_right.trans hl_eq_OP.symm.le)
    have hOPU_eq : Γ.O ⊔ P ⊔ Γ.U = π := by
      show Γ.O ⊔ P ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V
      rw [show Γ.O ⊔ P ⊔ Γ.U = (Γ.O ⊔ Γ.U) ⊔ P from by ac_rfl]
      have hl_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ P := lt_of_le_of_ne le_sup_left
        (fun h => hP_not_l (le_sup_right.trans h.symm.le))
      exact (hl_covBy_π.eq_or_eq hl_lt.le
        (sup_le hl_covBy_π.le hP_plane)).resolve_left (ne_of_gt hl_lt)
    rw [← hOPU_eq]
    exact line_covBy_plane Γ.hO hP Γ.hU (Ne.symm hP_ne_O) Γ.hOU
      (fun h => hU_not_OP (h ▸ le_sup_right)) hU_not_OP
  have hl_d_eq : l ⊔ d_P = π := by
    have hl_lt : l < l ⊔ d_P := lt_of_le_of_ne le_sup_left
      (fun h => hd_P_not_l (le_sup_right.trans h.symm.le))
    exact (hl_covBy_π.eq_or_eq hl_lt.le
      (sup_le hl_covBy_π.le ((inf_le_right : d_P ≤ m).trans hm_le_π))).resolve_left
      (ne_of_gt hl_lt)
  have hOP_d_eq : (Γ.O ⊔ P) ⊔ d_P = π := by
    have hOP_lt : Γ.O ⊔ P < (Γ.O ⊔ P) ⊔ d_P := lt_of_le_of_ne le_sup_left
      (fun h => hd_P_not_OP (le_sup_right.trans h.symm.le))
    exact (hOP_covBy_π.eq_or_eq hOP_lt.le
      (sup_le hOP_covBy_π.le ((inf_le_right : d_P ≤ m).trans hm_le_π))).resolve_left
      (ne_of_gt hOP_lt)
  have h_coplanar : Γ.O ⊔ Γ.U ⊔ d_P = (Γ.O ⊔ P) ⊔ d_P := by rw [hl_d_eq, hOP_d_eq]

  have h_persp_eq : (a₁ ⊔ d_P) ⊓ (Γ.O ⊔ P) = (a₂ ⊔ d_P) ⊓ (Γ.O ⊔ P) := by
    have h1 : dilation_ext Γ a₁ P = (a₁ ⊔ d_P) ⊓ (Γ.O ⊔ P) := by
      show (Γ.O ⊔ P) ⊓ (a₁ ⊔ (Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V)) = (a₁ ⊔ d_P) ⊓ (Γ.O ⊔ P)
      exact inf_comm _ _
    have h2 : dilation_ext Γ a₂ P = (a₂ ⊔ d_P) ⊓ (Γ.O ⊔ P) := by
      show (Γ.O ⊔ P) ⊓ (a₂ ⊔ (Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V)) = (a₂ ⊔ d_P) ⊓ (Γ.O ⊔ P)
      exact inf_comm _ _
    rw [← h1, ← h2]; exact h_agree

  by_contra h_ne
  have hp₁ : (⟨a₁, ha₁, ha₁_on⟩ : AtomsOn (Γ.O ⊔ Γ.U)) ≠ ⟨a₂, ha₂, ha₂_on⟩ :=
    fun h => h_ne (congrArg Subtype.val h)
  exact perspectivity_injective hd_P_atom Γ.hO Γ.hU Γ.hO hP Γ.hOU
    (Ne.symm hP_ne_O) hd_P_not_l hd_P_not_OP h_coplanar hp₁ (Subtype.ext h_persp_eq)

noncomputable def beta_cast (Γ : CoordSystem L) (P : L) : L :=
  (Γ.U ⊔ Γ.C) ⊓ (P ⊔ Γ.E)

theorem recovery_via_E (Γ : CoordSystem L)
    (c : L) (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U) (hc_ne_I : c ≠ Γ.I)
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_not_q : ¬ P ≤ Γ.U ⊔ Γ.C)
    (hP_ne_I : P ≠ Γ.I)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ c P =
      (dilation_ext Γ c (beta_cast Γ P) ⊔ Γ.E) ⊓ (Γ.O ⊔ P) := by
  set m := Γ.U ⊔ Γ.V
  set q := Γ.U ⊔ Γ.C
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set P' := beta_cast Γ P with hP'_def
  set σP := dilation_ext Γ c P
  set σP' := dilation_ext Γ c P'

  have hP_ne_O : P ≠ Γ.O := fun h => hP_not_l (h ▸ le_sup_left)
  have hOC_ne : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUC_ne : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)

  have hC_ne_E : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
  have hCE_eq_OC : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
    have hC_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hC_ne_E ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have hC_covBy : Γ.C ⋖ Γ.O ⊔ Γ.C := by
      rw [sup_comm]; exact atom_covBy_join Γ.hC Γ.hO hOC_ne.symm
    exact (hC_covBy.eq_or_eq hC_lt.le (sup_le le_sup_right CoordSystem.hE_le_OC)).resolve_left
      (ne_of_gt hC_lt)

  have hP_not_CE : ¬ P ≤ Γ.C ⊔ Γ.E := fun h => hP_not_OC (hCE_eq_OC ▸ h)

  have hU_ne_E : Γ.U ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ le_sup_right)
  have hUE_le_m : Γ.U ⊔ Γ.E ≤ m := sup_le le_sup_left Γ.hE_on_m

  have hP_not_UE : ¬ P ≤ Γ.U ⊔ Γ.E := fun h => hP_not_m (h.trans hUE_le_m)

  have hP_ne_E : P ≠ Γ.E := fun h => hP_not_m (h ▸ Γ.hE_on_m)

  have hPE_covBy_P : P ⋖ P ⊔ Γ.E := atom_covBy_join hP Γ.hE_atom hP_ne_E

  have hq_covBy_π : q ⋖ π := by

    have hq_inf_m : q ⊓ m = Γ.U := by
      change (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
      rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
      have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
        (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
      rw [this, sup_bot_eq]

    have hUV_ne : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    have h_inf : m ⊓ q ⋖ m := by
      rw [inf_comm, hq_inf_m]; exact atom_covBy_join Γ.hU Γ.hV hUV_ne
    have h1 := covBy_sup_of_inf_covBy_left h_inf
    have hmq : m ⊔ q = m ⊔ Γ.C := by
      change m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
      rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
    have hmC : m ⊔ Γ.C = π :=
      (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
        (sup_le Γ.m_covBy_π.le Γ.hC_plane)).resolve_left
        (ne_of_gt (lt_of_le_of_ne le_sup_left
          (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
    rwa [hmq, hmC] at h1

  have hPE_le_π : P ⊔ Γ.E ≤ π :=
    sup_le hP_plane (Γ.hE_on_m.trans Γ.m_covBy_π.le)

  have hE_not_OP : ¬ Γ.E ≤ Γ.O ⊔ P := by
    intro h
    have hO_ne_E : Γ.O ≠ Γ.E := fun h' => Γ.hO_not_m (h' ▸ Γ.hE_on_m)
    have hOE_le_OC : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left CoordSystem.hE_le_OC
    have hO_lt_OE : Γ.O < Γ.O ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h' => hO_ne_E ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have hO_covBy_OC : Γ.O ⋖ Γ.O ⊔ Γ.C := atom_covBy_join Γ.hO Γ.hC hOC_ne
    have hOE_eq_OC : Γ.O ⊔ Γ.E = Γ.O ⊔ Γ.C :=
      (hO_covBy_OC.eq_or_eq hO_lt_OE.le hOE_le_OC).resolve_left (ne_of_gt hO_lt_OE)
    have hOE_le_OP : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ P := sup_le le_sup_left h
    have hOC_le_OP : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ P := hOE_eq_OC ▸ hOE_le_OP
    have hO_lt_OC : Γ.O < Γ.O ⊔ Γ.C := hO_covBy_OC.lt
    have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
    have hOC_eq_OP : Γ.O ⊔ Γ.C = Γ.O ⊔ P :=
      (hO_covBy_OP.eq_or_eq hO_lt_OC.le hOC_le_OP).resolve_left (ne_of_gt hO_lt_OC)
    exact hP_not_OC (le_sup_right.trans hOC_eq_OP.symm.le)

  have hO_not_PE : ¬ Γ.O ≤ P ⊔ Γ.E := by
    intro h
    have hOP_le : Γ.O ⊔ P ≤ P ⊔ Γ.E := sup_le h le_sup_left
    have hP_lt : P < Γ.O ⊔ P := lt_of_le_of_ne le_sup_right
      (fun h' => hP_ne_O ((hP.le_iff.mp (le_sup_left.trans h'.symm.le)).resolve_left
        Γ.hO.1).symm)
    have hPE_eq : P ⊔ Γ.E = Γ.O ⊔ P :=
      (hPE_covBy_P.eq_or_eq hP_lt.le hOP_le).resolve_left (ne_of_gt hP_lt) |>.symm
    exact hE_not_OP (le_sup_right.trans hPE_eq.le)

  have hPE_covBy_π : P ⊔ Γ.E ⋖ π := by
    have hPEO_eq : P ⊔ Γ.E ⊔ Γ.O = π := by

      have hOP_covBy_π : Γ.O ⊔ P ⋖ π := by
        have hU_not_OP : ¬ Γ.U ≤ Γ.O ⊔ P := by
          intro h
          have hOU_le_OP : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ P := sup_le le_sup_left h
          have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
          have hO_lt_l : Γ.O < Γ.O ⊔ Γ.U := (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
          have hl_eq_OP : Γ.O ⊔ Γ.U = Γ.O ⊔ P :=
            (hO_covBy_OP.eq_or_eq hO_lt_l.le hOU_le_OP).resolve_left (ne_of_gt hO_lt_l)
          exact hP_not_l (le_sup_right.trans hl_eq_OP.symm.le)
        have hOPU_eq : Γ.O ⊔ P ⊔ Γ.U = π := by
          show Γ.O ⊔ P ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V
          have hl_covBy_π : Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
            have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
              (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
            have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
            rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
          rw [show Γ.O ⊔ P ⊔ Γ.U = (Γ.O ⊔ Γ.U) ⊔ P from by ac_rfl]
          have hl_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ P := lt_of_le_of_ne le_sup_left
            (fun h => hP_not_l (le_sup_right.trans h.symm.le))
          exact (hl_covBy_π.eq_or_eq hl_lt.le
            (sup_le hl_covBy_π.le hP_plane)).resolve_left (ne_of_gt hl_lt)
        rw [← hOPU_eq]
        exact line_covBy_plane Γ.hO hP Γ.hU (Ne.symm hP_ne_O) Γ.hOU
          (fun h => hU_not_OP (h ▸ le_sup_right)) hU_not_OP
      have hOP_lt : Γ.O ⊔ P < P ⊔ Γ.E ⊔ Γ.O := by
        apply lt_of_le_of_ne
        · rw [show P ⊔ Γ.E ⊔ Γ.O = Γ.O ⊔ P ⊔ Γ.E from by ac_rfl]
          exact le_sup_left
        · intro h

          have hE_le : Γ.E ≤ Γ.O ⊔ P := by
            rw [h]; exact le_sup_right.trans le_sup_left
          exact hE_not_OP hE_le
      exact (hOP_covBy_π.eq_or_eq hOP_lt.le
        (sup_le hPE_le_π (le_sup_left.trans le_sup_left))).resolve_left (ne_of_gt hOP_lt)
    have hE_ne_O : Γ.E ≠ Γ.O := fun h => Γ.hO_not_m (h ▸ Γ.hE_on_m)
    rw [← hPEO_eq]
    exact line_covBy_plane hP Γ.hE_atom Γ.hO hP_ne_E hP_ne_O hE_ne_O hO_not_PE

  have hE_not_q : ¬ Γ.E ≤ q := by
    intro h
    have hE_le_U : Γ.E ≤ Γ.U := by
      have hqm : q ⊓ m = Γ.U := by
        change (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
        rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
        have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
          (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h' => Γ.hC_not_m (h' ▸ inf_le_right))
        rw [this, sup_bot_eq]
      exact hqm ▸ le_inf h Γ.hE_on_m
    exact hU_ne_E ((Γ.hU.le_iff.mp hE_le_U).resolve_left Γ.hE_atom.1).symm
  have hq_ne_PE : q ≠ P ⊔ Γ.E := fun h => hE_not_q (h ▸ le_sup_right)

  have h_meet := planes_meet_covBy hq_covBy_π hPE_covBy_π hq_ne_PE
  have hP'_atom : IsAtom P' := by
    show IsAtom (q ⊓ (P ⊔ Γ.E))

    have h_ne_bot : q ⊓ (P ⊔ Γ.E) ≠ ⊥ := by
      intro h_eq
      have h_bot_covBy : ⊥ ⋖ q := h_eq ▸ h_meet.1
      have hC_pos : ⊥ < Γ.C := Γ.hC.bot_lt
      have hC_le_q : Γ.C ≤ q := le_sup_right
      have hC_lt_q : ⊥ < q := lt_of_lt_of_le hC_pos hC_le_q

      have hU_lt_q : Γ.U < q := lt_of_le_of_ne le_sup_left
        (fun h => hUC_ne ((Γ.hU.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          Γ.hC.1).symm)
      exact h_bot_covBy.2 Γ.hU.bot_lt hU_lt_q
    exact line_height_two Γ.hU Γ.hC hUC_ne (bot_lt_iff_ne_bot.mpr h_ne_bot) h_meet.1.lt

  have hP'_le_q : P' ≤ q := inf_le_left
  have hP'_le_PE : P' ≤ P ⊔ Γ.E := inf_le_right
  have hP_ne_P' : P ≠ P' := fun h => hP_not_q (h ▸ hP'_le_q)
  have hP_lt_PP' : P < P ⊔ P' := lt_of_le_of_ne le_sup_left
    (fun h => hP_ne_P' ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
      hP'_atom.1).symm)
  have hPP'_le_PE : P ⊔ P' ≤ P ⊔ Γ.E := sup_le le_sup_left hP'_le_PE
  have hPP'_eq_PE : P ⊔ P' = P ⊔ Γ.E :=
    (hPE_covBy_P.eq_or_eq hP_lt_PP'.le hPP'_le_PE).resolve_left (ne_of_gt hP_lt_PP')
  have hP_inf_m : P ⊓ m = ⊥ :=
    (hP.le_iff.mp inf_le_left).resolve_right (fun h => hP_not_m (h ▸ inf_le_right))
  have hPE_inf_m : (P ⊔ Γ.E) ⊓ m = Γ.E := by
    rw [sup_comm P Γ.E, sup_inf_assoc_of_le P Γ.hE_on_m, hP_inf_m, sup_bot_eq]
  have hPP'_inf_m : (P ⊔ P') ⊓ m = Γ.E := hPP'_eq_PE ▸ hPE_inf_m

  set l := Γ.O ⊔ Γ.U with hl_def

  have hq_inf_l : q ⊓ l = Γ.U := by
    show (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.U
    rw [sup_comm Γ.U Γ.C]
    exact line_direction Γ.hC Γ.hC_not_l (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U)
  have hq_inf_m : q ⊓ m = Γ.U := by
    show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have hCm : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [hCm, sup_bot_eq]

  have hU_ne_P : Γ.U ≠ P := fun h => hP_not_l (h ▸ le_sup_right)
  have hP'_ne_U : P' ≠ Γ.U := by
    intro h_eq

    have hU_le_PE : Γ.U ≤ P ⊔ Γ.E := h_eq ▸ hP'_le_PE
    have hP_lt_PU : P < P ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h => hU_ne_P
        ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1))
    have hPU_le_PE : P ⊔ Γ.U ≤ P ⊔ Γ.E := sup_le le_sup_left hU_le_PE
    have hPU_eq_PE : P ⊔ Γ.U = P ⊔ Γ.E :=
      (hPE_covBy_P.eq_or_eq hP_lt_PU.le hPU_le_PE).resolve_left (ne_of_gt hP_lt_PU)
    have hPU_inf_m : (P ⊔ Γ.U) ⊓ m = Γ.U :=
      line_direction hP hP_not_m (le_sup_left : Γ.U ≤ m)
    have hE_le_PU : Γ.E ≤ P ⊔ Γ.U := hPU_eq_PE.symm ▸ le_sup_right
    have hE_le_U : Γ.E ≤ Γ.U := hPU_inf_m ▸ le_inf hE_le_PU Γ.hE_on_m
    exact hU_ne_E ((Γ.hU.le_iff.mp hE_le_U).resolve_left Γ.hE_atom.1).symm

  have hP'_plane : P' ≤ π := hP'_le_q.trans hq_covBy_π.le

  have hP'_not_m : ¬ P' ≤ m := by
    intro h; apply hP'_ne_U
    exact (Γ.hU.le_iff.mp (hq_inf_m ▸ le_inf hP'_le_q h)).resolve_left hP'_atom.1
  have hP'_not_l : ¬ P' ≤ l := by
    intro h; apply hP'_ne_U
    exact (Γ.hU.le_iff.mp (hq_inf_l ▸ le_inf hP'_le_q h)).resolve_left hP'_atom.1

  have hP'_ne_O : P' ≠ Γ.O :=
    fun h => hP'_not_l (h ▸ (le_sup_left : Γ.O ≤ l))
  have hP'_ne_I : P' ≠ Γ.I :=
    fun h => hP'_not_l (h ▸ Γ.hI_on)

  have hP'_not_OP : ¬ P' ≤ Γ.O ⊔ P := by
    intro h

    have hPE_OP_eq_P : (P ⊔ Γ.E) ⊓ (P ⊔ Γ.O) = P :=
      modular_intersection hP Γ.hE_atom Γ.hO hP_ne_E hP_ne_O
        (fun heq => Γ.hO_not_m (heq ▸ Γ.hE_on_m)) hO_not_PE
    have hP'_le_P : P' ≤ P := by
      have := le_inf hP'_le_PE (sup_comm Γ.O P ▸ h : P' ≤ P ⊔ Γ.O)
      rwa [hPE_OP_eq_P] at this
    exact hP_ne_P' ((hP.le_iff.mp hP'_le_P).resolve_left hP'_atom.1).symm

  have hσP_le_OP : σP ≤ Γ.O ⊔ P :=
    show (Γ.O ⊔ P) ⊓ (c ⊔ (Γ.I ⊔ P) ⊓ m) ≤ Γ.O ⊔ P from inf_le_left
  have hσP'_le_OP' : σP' ≤ Γ.O ⊔ P' :=
    show (Γ.O ⊔ P') ⊓ (c ⊔ (Γ.I ⊔ P') ⊓ m) ≤ Γ.O ⊔ P' from inf_le_left

  have hσP_atom : IsAtom σP := dilation_ext_atom Γ hP hc hc_on hc_ne_O hc_ne_U
    hP_plane hP_not_l hP_ne_O hP_ne_I hP_not_m
  have hσP'_atom : IsAtom σP' := dilation_ext_atom Γ hP'_atom hc hc_on hc_ne_O hc_ne_U
    hP'_plane hP'_not_l hP'_ne_O hP'_ne_I hP'_not_m

  have hd_P_atom : IsAtom ((Γ.I ⊔ P) ⊓ m) :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  have hd_P_ne_U : (Γ.I ⊔ P) ⊓ m ≠ Γ.U := by
    intro h

    have hU_le_IP : Γ.U ≤ Γ.I ⊔ P := h ▸ inf_le_left
    have hI_lt : Γ.I < Γ.I ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h' => Γ.hUI ((Γ.hI.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
        Γ.hU.1).symm.symm)
    have hI_covBy_IP : Γ.I ⋖ Γ.I ⊔ P := atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)
    have hIU_le_IP : Γ.I ⊔ Γ.U ≤ Γ.I ⊔ P := sup_le le_sup_left hU_le_IP
    have hIU_eq_IP : Γ.I ⊔ Γ.U = Γ.I ⊔ P :=
      (hI_covBy_IP.eq_or_eq hI_lt.le hIU_le_IP).resolve_left (ne_of_gt hI_lt)
    have hP_le_l : P ≤ l :=
      le_sup_right.trans (hIU_eq_IP.symm.le.trans (sup_le Γ.hI_on le_sup_right))
    exact hP_not_l hP_le_l
  have hd_P_not_l : ¬ (Γ.I ⊔ P) ⊓ m ≤ l := by
    intro h
    apply hd_P_ne_U
    have h_meet : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := Γ.l_inf_m_eq_U
    exact (Γ.hU.le_iff.mp (h_meet ▸ le_inf h inf_le_right)).resolve_left hd_P_atom.1
  have hσP_not_l : ¬ σP ≤ l := by
    intro h

    have hOP_inf_l : (Γ.O ⊔ P) ⊓ l = Γ.O := by
      rw [sup_comm Γ.O P]
      exact line_direction hP hP_not_l (le_sup_left : Γ.O ≤ l)
    have hσP_le_O : σP ≤ Γ.O := hOP_inf_l ▸ le_inf hσP_le_OP h
    have hσP_eq_O : σP = Γ.O := (Γ.hO.le_iff.mp hσP_le_O).resolve_left hσP_atom.1

    have hσP_le_cd : σP ≤ c ⊔ (Γ.I ⊔ P) ⊓ m :=
      show (Γ.O ⊔ P) ⊓ (c ⊔ (Γ.I ⊔ P) ⊓ m) ≤ c ⊔ (Γ.I ⊔ P) ⊓ m from inf_le_right
    have hO_le_cd : Γ.O ≤ c ⊔ (Γ.I ⊔ P) ⊓ m := hσP_eq_O ▸ hσP_le_cd

    have hcd_inf_l : (c ⊔ (Γ.I ⊔ P) ⊓ m) ⊓ l = c := by
      rw [sup_comm c]
      exact line_direction hd_P_atom hd_P_not_l hc_on
    have hO_le_c : Γ.O ≤ c := hcd_inf_l ▸ le_inf hO_le_cd (le_sup_left : Γ.O ≤ l)
    exact hc_ne_O.symm ((hc.le_iff.mp hO_le_c).resolve_left Γ.hO.1)

  have hσP_ne_σP' : σP ≠ σP' := by
    intro h_eq
    have hσP_le_OP' : σP ≤ Γ.O ⊔ P' := h_eq ▸ hσP'_le_OP'
    have hOP_OP'_eq : (Γ.O ⊔ P) ⊓ (Γ.O ⊔ P') = Γ.O :=
      modular_intersection Γ.hO hP hP'_atom (Ne.symm hP_ne_O) (Ne.symm hP'_ne_O)
        hP_ne_P' (fun h => hP'_not_OP h)
    have hσP_le_O : σP ≤ Γ.O := hOP_OP'_eq ▸ le_inf hσP_le_OP hσP_le_OP'
    have hσP_eq_O : σP = Γ.O := (Γ.hO.le_iff.mp hσP_le_O).resolve_left hσP_atom.1
    exact hσP_not_l (hσP_eq_O ▸ (le_sup_left : Γ.O ≤ l))

  have hDPD : (P ⊔ P') ⊓ m = (σP ⊔ σP') ⊓ m :=
    dilation_preserves_direction Γ hP hP'_atom c hc hc_on hc_ne_O hc_ne_U
      hP_plane hP'_plane hP_not_m hP'_not_m hP_not_l hP'_not_l
      hP_ne_O hP'_ne_O hP_ne_P' hP_ne_I hP'_ne_I hσP_ne_σP'
      R hR hR_not h_irred

  have hσσ'_inf_m : (σP ⊔ σP') ⊓ m = Γ.E := hDPD ▸ hPP'_inf_m
  have hE_le_σσ' : Γ.E ≤ σP ⊔ σP' := hσσ'_inf_m ▸ inf_le_left
  have hσP'_not_m : ¬ σP' ≤ m := dilation_ext_not_m Γ hP'_atom hc hc_on hc_ne_O hc_ne_U
    hP'_plane hP'_not_m hP'_not_l hP'_ne_O hP'_ne_I hc_ne_I
  have hσP'_ne_E : σP' ≠ Γ.E := fun h => hσP'_not_m (h ▸ Γ.hE_on_m)

  have hσP'_covBy_σP'E : σP' ⋖ σP' ⊔ Γ.E :=
    atom_covBy_join hσP'_atom Γ.hE_atom hσP'_ne_E

  have hσP'_covBy_σP'σP : σP' ⋖ σP' ⊔ σP :=
    atom_covBy_join hσP'_atom hσP_atom (Ne.symm hσP_ne_σP')

  have hσP'E_le_σP'σP : σP' ⊔ Γ.E ≤ σP' ⊔ σP := by
    refine sup_le le_sup_left ?_
    exact hE_le_σσ'.trans (sup_comm σP σP' ▸ le_rfl)

  have hσP'_lt_σP'E : σP' < σP' ⊔ Γ.E := lt_of_le_of_ne le_sup_left
    (fun h => hσP'_ne_E
      ((hσP'_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_atom.1).symm)

  have hσP'E_eq : σP' ⊔ Γ.E = σP' ⊔ σP :=
    (hσP'_covBy_σP'σP.eq_or_eq hσP'_lt_σP'E.le hσP'E_le_σP'σP).resolve_left
      (ne_of_gt hσP'_lt_σP'E)

  have hσP_le_σP'E : σP ≤ σP' ⊔ Γ.E := hσP'E_eq.symm ▸ (le_sup_right : σP ≤ σP' ⊔ σP)

  have hσP_le_meet : σP ≤ (σP' ⊔ Γ.E) ⊓ (Γ.O ⊔ P) := le_inf hσP_le_σP'E hσP_le_OP

  have hRHS_atom : IsAtom ((σP' ⊔ Γ.E) ⊓ (Γ.O ⊔ P)) :=
    meet_of_lines_is_atom hσP'_atom Γ.hE_atom Γ.hO hP hσP'_ne_E (Ne.symm hP_ne_O)
      (fun h => hE_not_OP (le_sup_right.trans h))
      (fun h => hσP_atom.1 (le_bot_iff.mp (h ▸ hσP_le_meet)))

  exact (hRHS_atom.le_iff.mp hσP_le_meet).resolve_left hσP_atom.1

theorem dilation_witness_preservation (Γ : CoordSystem L)
    (x : L) (hx : IsAtom x) (hx_on : x ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hx_ne_U : x ≠ Γ.U) (hx_ne_I : x ≠ Γ.I)
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_ne_I : P ≠ Γ.I)
    (hP_ne_O : P ≠ Γ.O) :
    IsAtom (dilation_ext Γ x P) ∧
    dilation_ext Γ x P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ∧
    ¬ dilation_ext Γ x P ≤ Γ.O ⊔ Γ.U ∧
    ¬ dilation_ext Γ x P ≤ Γ.U ⊔ Γ.V ∧
    ¬ dilation_ext Γ x P ≤ Γ.O ⊔ Γ.C ∧
    dilation_ext Γ x P ≠ Γ.I := by
  set m := Γ.U ⊔ Γ.V
  set l := Γ.O ⊔ Γ.U
  set σ := dilation_ext Γ x P
  set d_P := (Γ.I ⊔ P) ⊓ m

  have hσ_atom : IsAtom σ :=
    dilation_ext_atom Γ hP hx hx_on hx_ne_O hx_ne_U hP_plane hP_not_l hP_ne_O hP_ne_I hP_not_m

  have hσ_plane : σ ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := dilation_ext_plane Γ hP hx hx_on hP_plane

  have hσ_not_m : ¬ σ ≤ m :=
    dilation_ext_not_m Γ hP hx hx_on hx_ne_O hx_ne_U hP_plane hP_not_m hP_not_l hP_ne_O
      hP_ne_I hx_ne_I

  have hx_not_m : ¬ x ≤ m := fun h => hx_ne_U (Γ.atom_on_both_eq_U hx hx_on h)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hOx_eq_l : Γ.O ⊔ x = l := by
    show Γ.O ⊔ x = Γ.O ⊔ Γ.U
    have hO_lt : Γ.O < Γ.O ⊔ x := by
      apply lt_of_le_of_ne le_sup_left; intro h
      exact hx_ne_O ((Γ.hO.le_iff.mp (h ▸ le_sup_right)).resolve_left hx.1)
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hx_on)).resolve_left (ne_of_gt hO_lt)
  have hd_P_atom : IsAtom d_P :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  have hσ_le_OP : σ ≤ Γ.O ⊔ P := inf_le_left

  have hσ_ne_O : σ ≠ Γ.O := by
    intro h_eq
    have hO_le_xdP : Γ.O ≤ x ⊔ d_P := h_eq ▸ (inf_le_right : σ ≤ x ⊔ d_P)
    have hl_le_xdP : l ≤ x ⊔ d_P :=
      hOx_eq_l.symm.le.trans (sup_le hO_le_xdP le_sup_left)
    have hxdP_inf_m : (x ⊔ d_P) ⊓ m = d_P :=
      line_direction hx hx_not_m (inf_le_right : d_P ≤ m)
    have hU_le_dP : Γ.U ≤ d_P := by
      have h1 : Γ.U ≤ (x ⊔ d_P) ⊓ m :=
        le_inf ((le_sup_right : Γ.U ≤ l).trans hl_le_xdP) (le_sup_left : Γ.U ≤ m)
      exact hxdP_inf_m ▸ h1
    have hU_eq_dP : Γ.U = d_P := IsAtom.eq_of_le Γ.hU hd_P_atom hU_le_dP

    have hU_le_IP : Γ.U ≤ Γ.I ⊔ P := hU_eq_dP ▸ (inf_le_left : d_P ≤ Γ.I ⊔ P)

    have hIU_covBy : Γ.I ⋖ Γ.I ⊔ Γ.U := atom_covBy_join Γ.hI Γ.hU Γ.hUI.symm

    have hIU_le_IP : Γ.I ⊔ Γ.U ≤ Γ.I ⊔ P := sup_le le_sup_left hU_le_IP

    have hI_lt_IU : Γ.I < Γ.I ⊔ Γ.U := hIU_covBy.lt

    have hI_covBy_IP : Γ.I ⋖ Γ.I ⊔ P := atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)

    have hIU_eq_IP : Γ.I ⊔ Γ.U = Γ.I ⊔ P :=
      (hI_covBy_IP.eq_or_eq hI_lt_IU.le hIU_le_IP).resolve_left (ne_of_gt hI_lt_IU)

    have hIU_eq_l : Γ.I ⊔ Γ.U = l := by
      show Γ.I ⊔ Γ.U = Γ.O ⊔ Γ.U
      have hI_le_l : Γ.I ≤ Γ.O ⊔ Γ.U := Γ.hI_on
      have hIU_le_l : Γ.I ⊔ Γ.U ≤ Γ.O ⊔ Γ.U := sup_le hI_le_l le_sup_right
      have hU_lt : Γ.U < Γ.I ⊔ Γ.U := lt_of_le_of_ne le_sup_right
        (fun h => Γ.hUI ((Γ.hU.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left Γ.hI.1).symm)
      have hU_covBy_l : Γ.U ⋖ Γ.O ⊔ Γ.U := by
        rw [sup_comm]; exact atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm
      exact (hU_covBy_l.eq_or_eq hU_lt.le hIU_le_l).resolve_left (ne_of_gt hU_lt)

    exact hP_not_l (le_sup_right.trans (hIU_eq_IP.symm.trans hIU_eq_l).le)

  have hOP_l_eq_O : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ P) = Γ.O :=
    modular_intersection Γ.hO Γ.hU hP Γ.hOU (Ne.symm hP_ne_O)
      (fun h' => hP_not_l (h' ▸ le_sup_right)) hP_not_l
  have hσ_not_l : ¬ σ ≤ l := by
    intro h
    have hσ_le_O : σ ≤ Γ.O := hOP_l_eq_O ▸ le_inf h hσ_le_OP
    exact hσ_ne_O ((Γ.hO.le_iff.mp hσ_le_O).resolve_left hσ_atom.1)

  have hC_not_OP : ¬ Γ.C ≤ Γ.O ⊔ P := by
    intro h
    have hOC_le : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ P := sup_le le_sup_left h
    have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
    have hO_lt_OC : Γ.O < Γ.O ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h' => hOC ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hC.1).symm)
    have hOC_eq_OP : Γ.O ⊔ Γ.C = Γ.O ⊔ P :=
      (hO_covBy_OP.eq_or_eq hO_lt_OC.le hOC_le).resolve_left (ne_of_gt hO_lt_OC)
    exact hP_not_OC (le_sup_right.trans hOC_eq_OP.symm.le)
  have hP_ne_C : P ≠ Γ.C := fun h => hP_not_OC (h ▸ le_sup_right)
  have hOP_OC_eq_O : (Γ.O ⊔ P) ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
    modular_intersection Γ.hO hP Γ.hC (Ne.symm hP_ne_O) hOC hP_ne_C hC_not_OP
  have hσ_not_OC : ¬ σ ≤ Γ.O ⊔ Γ.C := by
    intro h
    have hσ_le_O : σ ≤ Γ.O := hOP_OC_eq_O ▸ le_inf hσ_le_OP h
    exact hσ_ne_O ((Γ.hO.le_iff.mp hσ_le_O).resolve_left hσ_atom.1)

  have hσ_ne_I : σ ≠ Γ.I := by
    intro h_eq
    have hI_le_OP : Γ.I ≤ Γ.O ⊔ P := h_eq ▸ hσ_le_OP
    have hOI_le_OP : Γ.O ⊔ Γ.I ≤ Γ.O ⊔ P := sup_le le_sup_left hI_le_OP
    have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
    have hO_lt_OI : Γ.O < Γ.O ⊔ Γ.I := lt_of_le_of_ne le_sup_left
      (fun h => Γ.hOI ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hI.1).symm)
    have hOI_eq_OP : Γ.O ⊔ Γ.I = Γ.O ⊔ P :=
      (hO_covBy_OP.eq_or_eq hO_lt_OI.le hOI_le_OP).resolve_left (ne_of_gt hO_lt_OI)

    have hOI_eq_l : Γ.O ⊔ Γ.I = l := by
      show Γ.O ⊔ Γ.I = Γ.O ⊔ Γ.U
      have hO_covBy_l : Γ.O ⋖ Γ.O ⊔ Γ.U := atom_covBy_join Γ.hO Γ.hU Γ.hOU
      exact (hO_covBy_l.eq_or_eq hO_lt_OI.le (sup_le le_sup_left Γ.hI_on)).resolve_left
        (ne_of_gt hO_lt_OI)

    exact hP_not_l (le_sup_right.trans (hOI_eq_OP.symm.trans hOI_eq_l).le)
  exact ⟨hσ_atom, hσ_plane, hσ_not_l, hσ_not_m, hσ_not_OC, hσ_ne_I⟩

theorem dil_ne_O (Γ : CoordSystem L) {c P : L} (hc : IsAtom c) (hP : IsAtom P)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U)
    (_hP_ne_O : P ≠ Γ.O) (hP_ne_I : P ≠ Γ.I) :
    dilation_ext Γ c P ≠ Γ.O := by
  set m := Γ.U ⊔ Γ.V with hm
  set d := (Γ.I ⊔ P) ⊓ m with hd
  have hd_atom : IsAtom d :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  intro h
  have hσ_le_cd : dilation_ext Γ c P ≤ c ⊔ d := inf_le_right
  have hO_le_cd : Γ.O ≤ c ⊔ d := h ▸ hσ_le_cd
  have hO_lt_Oc : Γ.O < Γ.O ⊔ c := lt_of_le_of_ne le_sup_left
    (fun h' => hc_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left hc.1))
  have hOc_eq_l : Γ.O ⊔ c = Γ.O ⊔ Γ.U :=
    ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt_Oc.le
      (sup_le le_sup_left hc_on)).resolve_left (ne_of_gt hO_lt_Oc)
  have hl_le_cd : Γ.O ⊔ Γ.U ≤ c ⊔ d := hOc_eq_l ▸ sup_le hO_le_cd le_sup_left
  have hc_not_m : ¬ c ≤ m := fun h' => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on h')
  have hc_ne_d : c ≠ d := fun h' => hc_not_m (h' ▸ inf_le_right)
  have hc_lt_l : c < Γ.O ⊔ Γ.U :=
    (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hc hc_on).lt
  have hl_eq_cd : Γ.O ⊔ Γ.U = c ⊔ d :=
    ((atom_covBy_join hc hd_atom hc_ne_d).eq_or_eq hc_on hl_le_cd).resolve_left
      (ne_of_gt hc_lt_l)
  have hd_le_l : d ≤ Γ.O ⊔ Γ.U := hl_eq_cd ▸ le_sup_right
  have hd_le_U : d ≤ Γ.U := by
    have := le_inf hd_le_l (inf_le_right : d ≤ m)
    rwa [Γ.l_inf_m_eq_U] at this
  have hd_eq_U : d = Γ.U := (Γ.hU.le_iff.mp hd_le_U).resolve_left hd_atom.1
  have hU_le_IP : Γ.U ≤ Γ.I ⊔ P := hd_eq_U ▸ (inf_le_left : d ≤ Γ.I ⊔ P)
  have hI_covBy_IP : Γ.I ⋖ Γ.I ⊔ P := atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)
  have hIU_le_IP : Γ.I ⊔ Γ.U ≤ Γ.I ⊔ P := sup_le le_sup_left hU_le_IP
  have hIU_eq_l : Γ.I ⊔ Γ.U = Γ.O ⊔ Γ.U := by
    have hU_lt : Γ.U < Γ.I ⊔ Γ.U := lt_of_le_of_ne le_sup_right
      (fun h' => Γ.hUI ((Γ.hU.le_iff.mp (le_sup_left.trans h'.symm.le)).resolve_left Γ.hI.1).symm)
    have hU_covBy_l : Γ.U ⋖ Γ.O ⊔ Γ.U := by
      rw [sup_comm]; exact atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm
    exact (hU_covBy_l.eq_or_eq hU_lt.le (sup_le Γ.hI_on le_sup_right)).resolve_left
      (ne_of_gt hU_lt)
  have hl_le_IP : Γ.O ⊔ Γ.U ≤ Γ.I ⊔ P := hIU_eq_l ▸ hIU_le_IP
  have hI_lt_l : Γ.I < Γ.O ⊔ Γ.U := lt_of_le_of_ne Γ.hI_on
    (fun h' => Γ.hOI ((Γ.hI.le_iff.mp (le_sup_left.trans h'.symm.le)).resolve_left Γ.hO.1))
  have hl_eq_IP : Γ.O ⊔ Γ.U = Γ.I ⊔ P :=
    (hI_covBy_IP.eq_or_eq hI_lt_l.le hl_le_IP).resolve_left (ne_of_gt hI_lt_l)
  exact hP_not_l (le_sup_right.trans hl_eq_IP.symm.le)

theorem dilC_not_m (Γ : CoordSystem L) {c : L} (hc : IsAtom c)
    (hc_on : c ≤ Γ.O ⊔ Γ.U) (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U) :
    ¬ dilation_ext Γ c Γ.C ≤ Γ.U ⊔ Γ.V := by
  have hC_ne_O : Γ.C ≠ Γ.O := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hC_ne_I : Γ.C ≠ Γ.I := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  by_cases hcI : c = Γ.I
  · subst hcI
    rw [dilation_ext_identity Γ Γ.hC Γ.hC_plane Γ.hC_not_l]
    exact Γ.hC_not_m
  · exact dilation_ext_not_m Γ Γ.hC hc hc_on hc_ne_O hc_ne_U Γ.hC_plane Γ.hC_not_m Γ.hC_not_l
      hC_ne_O hC_ne_I hcI

theorem point_from_ref (Γ : CoordSystem L) {βa W_C W_βa : L}
    (hβa_atom : IsAtom βa) (hβa_not_OC : ¬ βa ≤ Γ.O ⊔ Γ.C)
    (hWC_atom : IsAtom W_C) (hWC_le : W_C ≤ Γ.O ⊔ Γ.C) (hWC_ne_O : W_C ≠ Γ.O)
    (hWC_not_m : ¬ W_C ≤ Γ.U ⊔ Γ.V)
    (hWβa_atom : IsAtom W_βa) (hWβa_le : W_βa ≤ Γ.O ⊔ βa)
    (hWne : W_C ≠ W_βa)
    (hd_atom : IsAtom ((Γ.C ⊔ βa) ⊓ (Γ.U ⊔ Γ.V)))
    (h_dir : (W_C ⊔ W_βa) ⊓ (Γ.U ⊔ Γ.V) = (Γ.C ⊔ βa) ⊓ (Γ.U ⊔ Γ.V)) :
    W_βa = (Γ.O ⊔ βa) ⊓ (W_C ⊔ (Γ.C ⊔ βa) ⊓ (Γ.U ⊔ Γ.V)) := by
  set m := Γ.U ⊔ Γ.V with hm
  set d := (Γ.C ⊔ βa) ⊓ m with hd
  have hCO : Γ.C ≠ Γ.O := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hOC : Γ.O ≠ Γ.C := hCO.symm
  have hβaO : βa ≠ Γ.O := fun h => hβa_not_OC (h ▸ le_sup_left)
  have hOβa : Γ.O ≠ βa := hβaO.symm
  have hCβa : Γ.C ≠ βa := fun h => hβa_not_OC (h ▸ le_sup_right)
  have hd_le_m : d ≤ m := inf_le_right
  have hWC_ne_d : W_C ≠ d := fun h => hWC_not_m (h ▸ hd_le_m)
  have hd_le : d ≤ W_C ⊔ W_βa := h_dir ▸ inf_le_left
  have hd_not_WC : ¬ d ≤ W_C :=
    fun h => hWC_ne_d ((hWC_atom.le_iff.mp h).resolve_left hd_atom.1).symm
  have hWC_lt : W_C < W_C ⊔ d := lt_of_le_of_ne le_sup_left
    (fun h => hd_not_WC (le_sup_right.trans h.symm.le))
  have hWC_cov : W_C ⋖ W_C ⊔ W_βa := atom_covBy_join hWC_atom hWβa_atom hWne
  have hWCd_eq : W_C ⊔ d = W_C ⊔ W_βa :=
    (hWC_cov.eq_or_eq hWC_lt.le (sup_le le_sup_left hd_le)).resolve_left (ne_of_gt hWC_lt)
  have hWβa_le_WCd : W_βa ≤ W_C ⊔ d := hWCd_eq ▸ le_sup_right
  have hWC_not_Oβa : ¬ W_C ≤ Γ.O ⊔ βa := by
    intro h
    have hle : W_C ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ βa) := le_inf hWC_le h
    rw [modular_intersection Γ.hO Γ.hC hβa_atom hOC hOβa hCβa hβa_not_OC] at hle
    exact hWC_ne_O ((Γ.hO.le_iff.mp hle).resolve_left hWC_atom.1)
  have hRHS_atom : IsAtom ((W_C ⊔ d) ⊓ (Γ.O ⊔ βa)) :=
    meet_of_lines_is_atom hWC_atom hd_atom Γ.hO hβa_atom hWC_ne_d hOβa
      (fun h => hWC_not_Oβa (le_sup_left.trans h))
      (fun h => hWβa_atom.1 (le_bot_iff.mp (h ▸ le_inf hWβa_le_WCd hWβa_le)))
  have hmeet := (hRHS_atom.le_iff.mp (le_inf hWβa_le_WCd hWβa_le)).resolve_left hWβa_atom.1
  rw [inf_comm] at hmeet
  exact hmeet

theorem OC_point_facts (Γ : CoordSystem L) {W : L} (hW : IsAtom W)
    (hW_le : W ≤ Γ.O ⊔ Γ.C) (hW_ne_O : W ≠ Γ.O) :
    ¬ W ≤ Γ.O ⊔ Γ.U ∧ W ≠ Γ.I := by
  have hCO : Γ.C ≠ Γ.O := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hm : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
    modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU hCO.symm hUC Γ.hC_not_l
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hW_ne_O ((Γ.hO.le_iff.mp (hm ▸ le_inf h hW_le)).resolve_left hW.1)
  · have hI_le : Γ.I ≤ Γ.O ⊔ Γ.C := h ▸ hW_le
    exact Γ.hOI ((Γ.hO.le_iff.mp (hm ▸ le_inf Γ.hI_on hI_le)).resolve_left Γ.hI.1).symm

theorem OC_Oβa_ne (Γ : CoordSystem L) {βa W1 W2 : L} (hβa_atom : IsAtom βa)
    (hβa_not_OC : ¬ βa ≤ Γ.O ⊔ Γ.C)
    (hW1 : IsAtom W1) (hW1_le : W1 ≤ Γ.O ⊔ Γ.C) (hW1_ne_O : W1 ≠ Γ.O)
    (hW2_le : W2 ≤ Γ.O ⊔ βa) : W1 ≠ W2 := by
  have hCO : Γ.C ≠ Γ.O := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hβaO : βa ≠ Γ.O := fun h => hβa_not_OC (h ▸ le_sup_left)
  have hCβa : Γ.C ≠ βa := fun h => hβa_not_OC (h ▸ le_sup_right)
  have hmeet : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ βa) = Γ.O :=
    modular_intersection Γ.hO Γ.hC hβa_atom hCO.symm hβaO.symm hCβa hβa_not_OC
  intro h
  have : W1 ≤ Γ.O := hmeet ▸ le_inf hW1_le (h ▸ hW2_le)
  exact hW1_ne_O ((Γ.hO.le_iff.mp this).resolve_left hW1.1)

theorem three_par_O (Γ : CoordSystem L)
    {a₁ a₂ a₃ b₁ b₂ b₃ : L}
    (ha₁ : IsAtom a₁) (ha₂ : IsAtom a₂) (ha₃ : IsAtom a₃)
    (hb₁ : IsAtom b₁) (hb₂ : IsAtom b₂) (hb₃ : IsAtom b₃)
    (ha₁_le : a₁ ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (ha₂_le : a₂ ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (ha₃_le : a₃ ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hb₁_le : b₁ ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hb₂_le : b₂ ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hb₃_le : b₃ ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hb₁_on : b₁ ≤ Γ.O ⊔ a₁) (hb₂_on : b₂ ≤ Γ.O ⊔ a₂) (hb₃_on : b₃ ≤ Γ.O ⊔ a₃)
    (ha₁₂ : a₁ ≠ a₂) (ha₁₃ : a₁ ≠ a₃) (ha₂₃ : a₂ ≠ a₃)
    (hb₁₂ : b₁ ≠ b₂) (hb₁₃ : b₁ ≠ b₃) (hb₂₃ : b₂ ≠ b₃)
    (h_sides₁₂ : a₁ ⊔ a₂ ≠ b₁ ⊔ b₂) (h_sides₁₃ : a₁ ⊔ a₃ ≠ b₁ ⊔ b₃)
    (h_sides₂₃ : a₂ ⊔ a₃ ≠ b₂ ⊔ b₃)
    (hπA : a₁ ⊔ a₂ ⊔ a₃ = Γ.O ⊔ Γ.U ⊔ Γ.V) (hπB : b₁ ⊔ b₂ ⊔ b₃ = Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hoa₁ : Γ.O ≠ a₁) (hoa₂ : Γ.O ≠ a₂) (hoa₃ : Γ.O ≠ a₃)
    (hob₁ : Γ.O ≠ b₁) (hob₂ : Γ.O ≠ b₂) (hob₃ : Γ.O ≠ b₃)
    (ha₁b₁ : a₁ ≠ b₁) (ha₂b₂ : a₂ ≠ b₂) (ha₃b₃ : a₃ ≠ b₃)
    (ha₁_not_m : ¬ a₁ ≤ Γ.U ⊔ Γ.V) (ha₂_not_m : ¬ a₂ ≤ Γ.U ⊔ Γ.V)
    (hb₂_not_m : ¬ b₂ ≤ Γ.U ⊔ Γ.V)
    (h_cov₁₂ : a₁ ⊔ a₂ ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V) (h_cov₁₃ : a₁ ⊔ a₃ ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_cov₂₃ : a₂ ⊔ a₃ ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hdir_ne : (a₁ ⊔ a₂) ⊓ (Γ.U ⊔ Γ.V) ≠ (a₁ ⊔ a₃) ⊓ (Γ.U ⊔ Γ.V))
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q)
    (par12 : (a₁ ⊔ a₂) ⊓ (Γ.U ⊔ Γ.V) = (b₁ ⊔ b₂) ⊓ (Γ.U ⊔ Γ.V))
    (par13 : (a₁ ⊔ a₃) ⊓ (Γ.U ⊔ Γ.V) = (b₁ ⊔ b₃) ⊓ (Γ.U ⊔ Γ.V)) :
    (a₂ ⊔ a₃) ⊓ (Γ.U ⊔ Γ.V) = (b₂ ⊔ b₃) ⊓ (Γ.U ⊔ Γ.V) := by
  set m := Γ.U ⊔ Γ.V with hm_def
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hO_le_π : Γ.O ≤ π := le_sup_left.trans le_sup_left
  obtain ⟨axis, haxis_le, haxis_ne, h12, h13, h23⟩ :=
    desargues_planar Γ.hO ha₁ ha₂ ha₃ hb₁ hb₂ hb₃
      hO_le_π ha₁_le ha₂_le ha₃_le hb₁_le hb₂_le hb₃_le
      hb₁_on hb₂_on hb₃_on
      ha₁₂ ha₁₃ ha₂₃ hb₁₂ hb₁₃ hb₂₃
      h_sides₁₂ h_sides₁₃ h_sides₂₃
      hπA hπB
      hoa₁ hoa₂ hoa₃ hob₁ hob₂ hob₃
      ha₁b₁ ha₂b₂ ha₃b₃
      R hR hR_not h_irred
      h_cov₁₂ h_cov₁₃ h_cov₂₃
  set s12 := (a₁ ⊔ a₂) ⊓ m with hs12_def
  set s13 := (a₁ ⊔ a₃) ⊓ m with hs13_def
  have hs12_atom : IsAtom s12 :=
    line_meets_m_at_atom ha₁ ha₂ ha₁₂ (sup_le ha₁_le ha₂_le) Γ.m_covBy_π.le Γ.m_covBy_π ha₁_not_m
  have hs13_atom : IsAtom s13 :=
    line_meets_m_at_atom ha₁ ha₃ ha₁₃ (sup_le ha₁_le ha₃_le) Γ.m_covBy_π.le Γ.m_covBy_π ha₁_not_m
  have hs12_axis : s12 ≤ axis :=
    (le_inf inf_le_left (par12.le.trans inf_le_left)).trans h12
  have hs13_axis : s13 ≤ axis :=
    (le_inf inf_le_left (par13.le.trans inf_le_left)).trans h13
  have hs12_le_m : s12 ≤ m := inf_le_right
  have hs13_le_m : s13 ≤ m := inf_le_right
  have hs12_cov_m : s12 ⋖ m := line_covers_its_atoms Γ.hU Γ.hV hUV hs12_atom hs12_le_m
  have hs12_lt : s12 < s12 ⊔ s13 := lt_of_le_of_ne le_sup_left
    (fun h => hdir_ne ((hs12_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
      hs13_atom.1).symm)
  have hs_span : s12 ⊔ s13 = m :=
    (hs12_cov_m.eq_or_eq hs12_lt.le (sup_le hs12_le_m hs13_le_m)).resolve_left (ne_of_gt hs12_lt)
  have hm_le_axis : m ≤ axis := hs_span ▸ sup_le hs12_axis hs13_axis
  have haxis_eq_m : axis = m :=
    (Γ.m_covBy_π.eq_or_eq hm_le_axis haxis_le).resolve_right haxis_ne
  have h23_m : (a₂ ⊔ a₃) ⊓ (b₂ ⊔ b₃) ≤ m := haxis_eq_m ▸ h23
  have hs23a_atom : IsAtom ((a₂ ⊔ a₃) ⊓ m) :=
    line_meets_m_at_atom ha₂ ha₃ ha₂₃ (sup_le ha₂_le ha₃_le) Γ.m_covBy_π.le Γ.m_covBy_π ha₂_not_m
  have hs23b_atom : IsAtom ((b₂ ⊔ b₃) ⊓ m) :=
    line_meets_m_at_atom hb₂ hb₃ hb₂₃ (sup_le hb₂_le hb₃_le) Γ.m_covBy_π.le Γ.m_covBy_π hb₂_not_m
  have hb_not_le : ¬ (b₂ ⊔ b₃) ≤ a₂ ⊔ a₃ := by
    intro hle
    rcases eq_or_lt_of_le hle with he | hlt
    · exact h_sides₂₃ he.symm
    · have hX := line_height_two ha₂ ha₃ ha₂₃ (lt_of_lt_of_le hb₂.bot_lt le_sup_left) hlt
      exact hb₂₃ (((hX.le_iff.mp le_sup_left).resolve_left hb₂.1).trans
        ((hX.le_iff.mp le_sup_right).resolve_left hb₃.1).symm)
  have h_meet_ne : (a₂ ⊔ a₃) ⊓ (b₂ ⊔ b₃) ≠ ⊥ :=
    lines_meet_if_coplanar h_cov₂₃ (sup_le hb₂_le hb₃_le) hb_not_le hb₂
      (lt_of_le_of_ne le_sup_left (fun h =>
        hb₂₃ ((hb₂.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hb₃.1).symm))
  have h_int_lt : (a₂ ⊔ a₃) ⊓ (b₂ ⊔ b₃) < a₂ ⊔ a₃ := lt_of_le_of_ne inf_le_left (by
    intro h'
    have hle : a₂ ⊔ a₃ ≤ b₂ ⊔ b₃ := h' ▸ inf_le_right
    rcases eq_or_lt_of_le hle with he | hlt
    · exact h_sides₂₃ he
    · have hX := line_height_two hb₂ hb₃ hb₂₃ (lt_of_lt_of_le ha₂.bot_lt le_sup_left) hlt
      exact ha₂₃ (((hX.le_iff.mp le_sup_left).resolve_left ha₂.1).trans
        ((hX.le_iff.mp le_sup_right).resolve_left ha₃.1).symm))
  have h_int_atom : IsAtom ((a₂ ⊔ a₃) ⊓ (b₂ ⊔ b₃)) :=
    line_height_two ha₂ ha₃ ha₂₃ (bot_lt_iff_ne_bot.mpr h_meet_ne) h_int_lt
  have h1 := (hs23a_atom.le_iff.mp (le_inf inf_le_left h23_m)).resolve_left h_int_atom.1
  have h2 := (hs23b_atom.le_iff.mp (le_inf inf_le_right h23_m)).resolve_left h_int_atom.1
  exact h1.symm.trans h2

theorem crux_dir1 (Γ : CoordSystem L) (x : L) (hx : IsAtom x)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hx_ne_O : x ≠ Γ.O) (hx_ne_U : x ≠ Γ.U)
    (hx_ne_I : x ≠ Γ.I) :
    (x ⊔ dilation_ext Γ x Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I := by
  have hC_ne_O : Γ.C ≠ Γ.O := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hC_ne_I : Γ.C ≠ Γ.I := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hCx_atom : IsAtom (dilation_ext Γ x Γ.C) :=
    dilation_ext_atom Γ Γ.hC hx hx_on hx_ne_O hx_ne_U Γ.hC_plane Γ.hC_not_l
      hC_ne_O hC_ne_I Γ.hC_not_m
  have hCx_ne_x : dilation_ext Γ x Γ.C ≠ x :=
    dilation_ext_ne_c Γ Γ.hC hx hx_on hx_ne_O Γ.hC_not_l hC_ne_O hCx_atom
  have h := dilation_ext_parallelism Γ Γ.hC hx hx_on hx_ne_O hx_ne_U
    Γ.hC_plane Γ.hC_not_m Γ.hC_not_l hC_ne_O hC_ne_I hCx_atom hCx_ne_x
  calc (x ⊔ dilation_ext Γ x Γ.C) ⊓ (Γ.U ⊔ Γ.V)
      = (dilation_ext Γ x Γ.C ⊔ x) ⊓ (Γ.U ⊔ Γ.V) := by rw [sup_comm]
    _ = (Γ.C ⊔ Γ.I) ⊓ (Γ.U ⊔ Γ.V) := h.symm
    _ = (Γ.I ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by rw [sup_comm]
    _ = Γ.E_I := rfl

theorem crux_at_C_of_gap (Γ : CoordSystem L) (x y : L) (hx : IsAtom x) (hy : IsAtom y)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U)
    (hxy_ne_O : coord_mul Γ x y ≠ Γ.O) (hxy_ne_U : coord_mul Γ x y ≠ Γ.U)
    (h_gap : (coord_mul Γ x y ⊔ dilation_ext Γ y (dilation_ext Γ x Γ.C))
                ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I) :
    dilation_ext Γ y (dilation_ext Γ x Γ.C) = dilation_ext Γ (coord_mul Γ x y) Γ.C := by
  set m := Γ.U ⊔ Γ.V with hm_def
  have hC_ne_O : Γ.C ≠ Γ.O := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hC_ne_I : Γ.C ≠ Γ.I := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hxy_atom : IsAtom (coord_mul Γ x y) :=
    coord_mul_atom Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U
  have hxy_le_l : coord_mul Γ x y ≤ Γ.O ⊔ Γ.U := inf_le_right
  have hCx_atom : IsAtom (dilation_ext Γ x Γ.C) :=
    dilation_ext_atom Γ Γ.hC hx hx_on hx_ne_O hx_ne_U Γ.hC_plane Γ.hC_not_l
      hC_ne_O hC_ne_I Γ.hC_not_m
  have hCx_le_OC : dilation_ext Γ x Γ.C ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hCx_plane : dilation_ext Γ x Γ.C ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    dilation_ext_plane Γ Γ.hC hx hx_on Γ.hC_plane
  have hCx_ne_O : dilation_ext Γ x Γ.C ≠ Γ.O :=
    dil_ne_O Γ hx Γ.hC hx_on hx_ne_O hx_ne_U Γ.hC_plane Γ.hC_not_l hC_ne_O hC_ne_I
  have hCx_not_m : ¬ dilation_ext Γ x Γ.C ≤ Γ.U ⊔ Γ.V :=
    dilC_not_m Γ hx hx_on hx_ne_O hx_ne_U
  obtain ⟨hCx_not_l, hCx_ne_I⟩ := OC_point_facts Γ hCx_atom hCx_le_OC hCx_ne_O
  have hW_atom : IsAtom (dilation_ext Γ y (dilation_ext Γ x Γ.C)) :=
    dilation_ext_atom Γ hCx_atom hy hy_on hy_ne_O hy_ne_U hCx_plane hCx_not_l hCx_ne_O
      hCx_ne_I hCx_not_m
  have hW_le_OC : dilation_ext Γ y (dilation_ext Γ x Γ.C) ≤ Γ.O ⊔ Γ.C :=
    (inf_le_left).trans (sup_le le_sup_left hCx_le_OC)
  have hW_ne_O : dilation_ext Γ y (dilation_ext Γ x Γ.C) ≠ Γ.O :=
    dil_ne_O Γ hy hCx_atom hy_on hy_ne_O hy_ne_U hCx_plane hCx_not_l hCx_ne_O hCx_ne_I
  have hRHS_eq : dilation_ext Γ (coord_mul Γ x y) Γ.C
      = (Γ.O ⊔ Γ.C) ⊓ (coord_mul Γ x y ⊔ Γ.E_I) :=
    dilation_ext_C Γ (coord_mul Γ x y) hxy_atom hxy_le_l hxy_ne_O hxy_ne_U
  have hRHS_atom : IsAtom ((Γ.O ⊔ Γ.C) ⊓ (coord_mul Γ x y ⊔ Γ.E_I)) := by
    rw [← hRHS_eq]
    exact dilation_ext_atom Γ Γ.hC hxy_atom hxy_le_l hxy_ne_O hxy_ne_U Γ.hC_plane
      Γ.hC_not_l hC_ne_O hC_ne_I Γ.hC_not_m
  have hxy_ne_W : coord_mul Γ x y ≠ dilation_ext Γ y (dilation_ext Γ x Γ.C) := by
    intro h
    have hW_le_meet : dilation_ext Γ y (dilation_ext Γ x Γ.C)
        ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) := le_inf (h ▸ hxy_le_l) hW_le_OC
    rw [modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU hC_ne_O.symm hUC Γ.hC_not_l] at hW_le_meet
    exact hW_ne_O ((Γ.hO.le_iff.mp hW_le_meet).resolve_left hW_atom.1)
  have hEI_le : Γ.E_I ≤ coord_mul Γ x y ⊔ dilation_ext Γ y (dilation_ext Γ x Γ.C) :=
    h_gap ▸ (inf_le_left :
      (coord_mul Γ x y ⊔ dilation_ext Γ y (dilation_ext Γ x Γ.C)) ⊓ m
        ≤ coord_mul Γ x y ⊔ dilation_ext Γ y (dilation_ext Γ x Γ.C))
  have hEI_not_le_xy : ¬ Γ.E_I ≤ coord_mul Γ x y :=
    fun h => Γ.hE_I_not_l (h.trans hxy_le_l)
  have hxy_lt : coord_mul Γ x y < coord_mul Γ x y ⊔ Γ.E_I :=
    lt_of_le_of_ne le_sup_left (fun h => hEI_not_le_xy (h ▸ le_sup_right))
  have hxy_cov_W : coord_mul Γ x y ⋖ coord_mul Γ x y
      ⊔ dilation_ext Γ y (dilation_ext Γ x Γ.C) :=
    atom_covBy_join hxy_atom hW_atom hxy_ne_W
  have hxyEI_le_xyW : coord_mul Γ x y ⊔ Γ.E_I
      ≤ coord_mul Γ x y ⊔ dilation_ext Γ y (dilation_ext Γ x Γ.C) :=
    sup_le le_sup_left hEI_le
  have hxyEI_eq : coord_mul Γ x y ⊔ Γ.E_I
      = coord_mul Γ x y ⊔ dilation_ext Γ y (dilation_ext Γ x Γ.C) :=
    (hxy_cov_W.eq_or_eq hxy_lt.le hxyEI_le_xyW).resolve_left (ne_of_gt hxy_lt)
  have hW_le_xyEI : dilation_ext Γ y (dilation_ext Γ x Γ.C)
      ≤ coord_mul Γ x y ⊔ Γ.E_I := hxyEI_eq ▸ le_sup_right
  have hW_le_meet : dilation_ext Γ y (dilation_ext Γ x Γ.C)
      ≤ (Γ.O ⊔ Γ.C) ⊓ (coord_mul Γ x y ⊔ Γ.E_I) := le_inf hW_le_OC hW_le_xyEI
  rw [hRHS_eq]
  exact (hRHS_atom.le_iff.mp hW_le_meet).resolve_left hW_atom.1

theorem gap_direction (Γ : CoordSystem L)
    (x y : L) (hx : IsAtom x) (hy : IsAtom y)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U)
    (hx_ne_I : x ≠ Γ.I) (hy_ne_I : y ≠ Γ.I)
    (hxy_ne_O : coord_mul Γ x y ≠ Γ.O) (hxy_ne_U : coord_mul Γ x y ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    (coord_mul Γ x y ⊔ dilation_ext Γ y (dilation_ext Γ x Γ.C)) ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I := by
  set m := Γ.U ⊔ Γ.V with hm_def
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def
  set l := Γ.O ⊔ Γ.U with hl_def
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hIC : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hl_le_π : l ≤ π := le_sup_left
  have hm_le_π : m ≤ π := Γ.m_covBy_π.le
  have hx_not_m : ¬ x ≤ m := fun h => hx_ne_U (Γ.atom_on_both_eq_U hx hx_on h)
  have hx_ne_E : x ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hx_on)
  have hx_ne_EI : x ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hx_on)
  have hx_le_π : x ≤ π := hx_on.trans hl_le_π
  have hxO_l : Γ.O ⊔ x = l := by
    have hcov : Γ.O ⋖ l := atom_covBy_join Γ.hO Γ.hU Γ.hOU
    have hlt : Γ.O < Γ.O ⊔ x := lt_of_le_of_ne le_sup_left (fun h => hx_ne_O
      ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hx.1))
    exact (hcov.eq_or_eq le_sup_left (sup_le le_sup_left hx_on)).resolve_left (ne_of_gt hlt)
  have hE_atom := Γ.hE_atom
  have hEI_atom := Γ.hE_I_atom
  have hE_ne_EI : Γ.E ≠ Γ.E_I := (Γ.hE_I_ne_E).symm
  have hE_ne_C : Γ.E ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
  have hE_ne_U : Γ.E ≠ Γ.U := Γ.hEU
  have hE_lt : Γ.E < Γ.E ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
    (fun h => hE_ne_EI ((hE_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hEI_atom.1).symm)
  have hE_cov_m : Γ.E ⋖ m := line_covers_its_atoms Γ.hU Γ.hV hUV hE_atom Γ.hE_on_m
  have hEEI_m : Γ.E ⊔ Γ.E_I = m :=
    (hE_cov_m.eq_or_eq hE_lt.le (sup_le Γ.hE_on_m Γ.hE_I_on_m)).resolve_left (ne_of_gt hE_lt)
  have line_ne_π : ∀ {a b : L}, IsAtom a → IsAtom b → a ≠ b → a ⊔ b ≠ π := by
    intro a b ha hb hab h
    have hm_lt : m < π := Γ.m_covBy_π.lt
    rw [← h] at hm_lt
    have hm_pos : (⊥ : L) < m := lt_of_lt_of_le Γ.hU.bot_lt le_sup_left
    have hatom := line_height_two ha hb hab hm_pos hm_lt
    have hU_eq : Γ.U = m := (hatom.le_iff.mp (le_sup_left : Γ.U ≤ m)).resolve_left Γ.hU.1
    have : Γ.V ≤ Γ.U := hU_eq ▸ (le_sup_right : Γ.V ≤ m)
    exact hUV ((Γ.hU.le_iff.mp this).resolve_left Γ.hV.1).symm
  have hxC_ne : x ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hx_on)
  have hU_le_m : Γ.U ≤ m := le_sup_left
  have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ m = Γ.U := by
    rw [sup_inf_assoc_of_le Γ.C hU_le_m]
    have hCm : Γ.C ⊓ m = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [hCm, sup_bot_eq]
  have hU_not_xE : ¬ Γ.U ≤ x ⊔ Γ.E := by
    intro h
    have hx_lt : x < x ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h' => hx_ne_U ((hx.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
    have hxU_eq : x ⊔ Γ.U = x ⊔ Γ.E :=
      ((atom_covBy_join hx Γ.hE_atom hx_ne_E).eq_or_eq hx_lt.le
        (sup_le le_sup_left h)).resolve_left (ne_of_gt hx_lt)
    exact Γ.hE_not_l (le_sup_right.trans (hxU_eq.symm.le.trans (sup_le hx_on le_sup_right)))
  have hO_not_Cx : ¬ Γ.O ≤ Γ.C ⊔ x := by
    intro h
    have hO_le : Γ.O ≤ (Γ.C ⊔ x) ⊓ l := le_inf h le_sup_left
    rw [line_direction Γ.hC Γ.hC_not_l hx_on] at hO_le
    exact hx_ne_O ((hx.le_iff.mp hO_le).resolve_left Γ.hO.1).symm
  have hxCOC : (x ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
    rw [sup_comm x Γ.C, sup_comm Γ.O Γ.C]
    exact modular_intersection Γ.hC hx Γ.hO hxC_ne.symm hOC.symm hx_ne_O hO_not_Cx
  have hC_not_xE : ¬ Γ.C ≤ x ⊔ Γ.E := by
    intro hC_le
    have hx_lt : x < x ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h => hxC_ne ((hx.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm)
    have hxC_eq : x ⊔ Γ.C = x ⊔ Γ.E :=
      ((atom_covBy_join hx Γ.hE_atom hx_ne_E).eq_or_eq hx_lt.le
        (sup_le le_sup_left hC_le)).resolve_left (ne_of_gt hx_lt)
    have hmeet : Γ.E ≤ (x ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) := le_inf (hxC_eq ▸ le_sup_right) Γ.hE_le_OC
    rw [hxCOC] at hmeet
    exact hE_ne_C ((Γ.hC.le_iff.mp hmeet).resolve_left Γ.hE_atom.1)
  set σxC := dilation_ext Γ x Γ.C with hσxC_def
  have hσxC_eq : σxC = (Γ.O ⊔ Γ.C) ⊓ (x ⊔ Γ.E_I) := dilation_ext_C Γ x hx hx_on hx_ne_O hx_ne_U
  have hσxC_atom : IsAtom σxC :=
    dilation_ext_atom Γ Γ.hC hx hx_on hx_ne_O hx_ne_U Γ.hC_plane Γ.hC_not_l hOC.symm hIC.symm Γ.hC_not_m
  have hσxC_le_OC : σxC ≤ Γ.O ⊔ Γ.C := hσxC_eq ▸ inf_le_left
  have hσxC_le_xEI : σxC ≤ x ⊔ Γ.E_I := hσxC_eq ▸ inf_le_right
  have hσxC_plane : σxC ≤ π := dilation_ext_plane Γ Γ.hC hx hx_on Γ.hC_plane
  have hσxC_not_m : ¬ σxC ≤ m :=
    dilation_ext_not_m Γ Γ.hC hx hx_on hx_ne_O hx_ne_U Γ.hC_plane Γ.hC_not_m Γ.hC_not_l
      hOC.symm hIC.symm hx_ne_I
  have hσxC_ne_O : σxC ≠ Γ.O :=
    dil_ne_O Γ hx Γ.hC hx_on hx_ne_O hx_ne_U Γ.hC_plane Γ.hC_not_l hOC.symm hIC.symm
  obtain ⟨hσxC_not_l, hσxC_ne_I⟩ := OC_point_facts Γ hσxC_atom hσxC_le_OC hσxC_ne_O
  have hσxC_ne_x : σxC ≠ x :=
    dilation_ext_ne_c Γ Γ.hC hx hx_on hx_ne_O Γ.hC_not_l hOC.symm hσxC_atom
  set βx := (Γ.U ⊔ Γ.C) ⊓ (x ⊔ Γ.E) with hβx_def
  have hβx_atom : IsAtom βx := beta_atom Γ hx hx_on hx_ne_O hx_ne_U
  have hβx_not_l : ¬ βx ≤ l := beta_not_l Γ hx hx_on hx_ne_O hx_ne_U
  have hβx_plane : βx ≤ π := beta_plane Γ hx_on
  have hβx_le_xE : βx ≤ x ⊔ Γ.E := inf_le_right
  have hβx_le_UC : βx ≤ Γ.U ⊔ Γ.C := inf_le_left
  have hβx_ne_O : βx ≠ Γ.O := fun h => hβx_not_l (h ▸ le_sup_left)
  have hβx_ne_I : βx ≠ Γ.I := fun h => hβx_not_l (h ▸ Γ.hI_on)
  have hβx_ne_x : βx ≠ x := fun h => hβx_not_l (h ▸ hx_on)
  have hβx_not_m : ¬ βx ≤ m := by
    intro h
    have hle : βx ≤ Γ.U := hUC_inf_m ▸ le_inf hβx_le_UC h
    exact hU_not_xE (((Γ.hU.le_iff.mp hle).resolve_left hβx_atom.1) ▸ hβx_le_xE)
  have hβx_ne_C : βx ≠ Γ.C := fun h => hC_not_xE (h ▸ hβx_le_xE)
  have hβx_not_OC : ¬ βx ≤ Γ.O ⊔ Γ.C := by
    intro h
    have hle : βx ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C) := le_inf h hβx_le_UC
    rw [Γ.OC_inf_UC] at hle
    exact hβx_ne_C ((Γ.hC.le_iff.mp hle).resolve_left hβx_atom.1)
  have hEI_not_xE : ¬ Γ.E_I ≤ x ⊔ Γ.E := by
    intro h
    have : Γ.E_I ≤ (x ⊔ Γ.E) ⊓ m := le_inf h Γ.hE_I_on_m
    rw [line_direction hx hx_not_m Γ.hE_on_m] at this
    exact Γ.hE_I_ne_E ((Γ.hE_atom.le_iff.mp this).resolve_left Γ.hE_I_atom.1)
  have hβx_ne_σxC : βx ≠ σxC := by
    intro h
    have hle : βx ≤ (x ⊔ Γ.E) ⊓ (x ⊔ Γ.E_I) := le_inf hβx_le_xE (h ▸ hσxC_le_xEI)
    rw [modular_intersection hx Γ.hE_atom Γ.hE_I_atom hx_ne_E hx_ne_EI hE_ne_EI hEI_not_xE] at hle
    exact hβx_ne_x ((hx.le_iff.mp hle).resolve_left hβx_atom.1)
  set σyC := dilation_ext Γ y Γ.C with hσyC_def
  have hσyC_eq : σyC = (Γ.O ⊔ Γ.C) ⊓ (y ⊔ Γ.E_I) := dilation_ext_C Γ y hy hy_on hy_ne_O hy_ne_U
  have hσyC_atom : IsAtom σyC :=
    dilation_ext_atom Γ Γ.hC hy hy_on hy_ne_O hy_ne_U Γ.hC_plane Γ.hC_not_l hOC.symm hIC.symm Γ.hC_not_m
  have hσyC_le_OC : σyC ≤ Γ.O ⊔ Γ.C := hσyC_eq ▸ inf_le_left
  have hσyC_not_m : ¬ σyC ≤ m :=
    dilation_ext_not_m Γ Γ.hC hy hy_on hy_ne_O hy_ne_U Γ.hC_plane Γ.hC_not_m Γ.hC_not_l
      hOC.symm hIC.symm hy_ne_I
  have hEI_ne_C : Γ.E_I ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ Γ.hE_I_on_m)
  have hy_ne_EI : y ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hy_on)
  have hyC_ne : y ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hy_on)
  have hO_I_not_Cy : ¬ Γ.I ≤ Γ.C ⊔ y := by
    intro h
    have hI_le : Γ.I ≤ (Γ.C ⊔ y) ⊓ l := le_inf h (Γ.hI_on)
    rw [line_direction Γ.hC Γ.hC_not_l hy_on] at hI_le
    exact hy_ne_I ((hy.le_iff.mp hI_le).resolve_left Γ.hI.1).symm
  have hyCIC : (y ⊔ Γ.C) ⊓ (Γ.I ⊔ Γ.C) = Γ.C := by
    rw [sup_comm y Γ.C, sup_comm Γ.I Γ.C]
    exact modular_intersection Γ.hC hy Γ.hI hyC_ne.symm hIC.symm hy_ne_I hO_I_not_Cy
  have hσyC_ne_C : σyC ≠ Γ.C := by
    intro h
    have hC_le : Γ.C ≤ y ⊔ Γ.E_I := by
      have := hσyC_eq.symm.trans h
      exact le_of_eq this.symm |>.trans inf_le_right
    have hy_lt : y < y ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun hh => hyC_ne ((hy.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left Γ.hC.1).symm)
    have hyC_eq : y ⊔ Γ.C = y ⊔ Γ.E_I :=
      ((atom_covBy_join hy Γ.hE_I_atom hy_ne_EI).eq_or_eq hy_lt.le
        (sup_le le_sup_left hC_le)).resolve_left (ne_of_gt hy_lt)
    have hmeet : Γ.E_I ≤ (y ⊔ Γ.C) ⊓ (Γ.I ⊔ Γ.C) := le_inf (hyC_eq ▸ le_sup_right) Γ.hE_I_le_IC
    rw [hyCIC] at hmeet
    exact hEI_ne_C ((Γ.hC.le_iff.mp hmeet).resolve_left Γ.hE_I_atom.1)
  set d_x := (x ⊔ Γ.C) ⊓ m with hdx_def
  have hd_x_atom : IsAtom d_x :=
    line_meets_m_at_atom hx Γ.hC hxC_ne (sup_le hx_le_π Γ.hC_plane) hm_le_π Γ.m_covBy_π hx_not_m
  have hd_x_le_m : d_x ≤ m := inf_le_right
  have hd_x_le_xC : d_x ≤ x ⊔ Γ.C := inf_le_left
  have hd_x_ne_x : d_x ≠ x := fun h => hx_not_m (h ▸ hd_x_le_m)
  have hx_lt_xdx : x < x ⊔ d_x := lt_of_le_of_ne le_sup_left
    (fun h => hd_x_ne_x ((hx.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hd_x_atom.1))
  have hxdx_eq : x ⊔ d_x = x ⊔ Γ.C :=
    ((atom_covBy_join hx Γ.hC hxC_ne).eq_or_eq hx_lt_xdx.le
      (sup_le le_sup_left hd_x_le_xC)).resolve_left (ne_of_gt hx_lt_xdx)
  have hx_ne_xy : x ≠ coord_mul Γ x y := by
    intro hxe
    have hx_le_join : x ≤ σyC ⊔ d_x := by
      have hcm : coord_mul Γ x y = (σyC ⊔ d_x) ⊓ l := by
        rw [hσyC_def, hdx_def, hm_def, hl_def]; rfl
      rw [hxe, hcm]; exact inf_le_left
    have hσyC_ne_dx : σyC ≠ d_x := fun h => hσyC_not_m (h ▸ hd_x_le_m)
    have hdx_cov : d_x ⋖ σyC ⊔ d_x :=
      sup_comm d_x σyC ▸ atom_covBy_join hd_x_atom hσyC_atom (Ne.symm hσyC_ne_dx)
    have hxdx_ne_dx : x ⊔ d_x ≠ d_x := fun h =>
      hd_x_ne_x ((hd_x_atom.le_iff.mp (le_sup_left.trans h.le)).resolve_left hx.1).symm
    have hline_eq : x ⊔ d_x = σyC ⊔ d_x :=
      (hdx_cov.eq_or_eq le_sup_right (sup_le hx_le_join le_sup_right)).resolve_left hxdx_ne_dx
    have hσyC_le_xC : σyC ≤ x ⊔ Γ.C := by
      have : σyC ≤ x ⊔ d_x := hline_eq ▸ le_sup_left
      exact hxdx_eq ▸ this
    have : σyC ≤ (x ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) := le_inf hσyC_le_xC hσyC_le_OC
    rw [hxCOC] at this
    exact hσyC_ne_C ((Γ.hC.le_iff.mp this).resolve_left hσyC_atom.1)
  set W := dilation_ext Γ y σxC with hW_def
  have hW_atom : IsAtom W :=
    dilation_ext_atom Γ hσxC_atom hy hy_on hy_ne_O hy_ne_U hσxC_plane hσxC_not_l hσxC_ne_O hσxC_ne_I hσxC_not_m
  have hW_le_OC : W ≤ Γ.O ⊔ Γ.C := inf_le_left.trans (sup_le le_sup_left hσxC_le_OC)
  have hW_plane : W ≤ π := dilation_ext_plane Γ hσxC_atom hy hy_on hσxC_plane
  have hW_ne_O : W ≠ Γ.O :=
    dil_ne_O Γ hy hσxC_atom hy_on hy_ne_O hy_ne_U hσxC_plane hσxC_not_l hσxC_ne_O hσxC_ne_I
  have hW_not_m : ¬ W ≤ m :=
    dilation_ext_not_m Γ hσxC_atom hy hy_on hy_ne_O hy_ne_U hσxC_plane hσxC_not_m hσxC_not_l
      hσxC_ne_O hσxC_ne_I hy_ne_I
  have hW_ne_E : W ≠ Γ.E := fun h => hW_not_m (h ▸ Γ.hE_on_m)
  have hW_ne_σxC : W ≠ σxC :=
    dilation_ext_ne_P Γ hσxC_atom hy hy_on hy_ne_O hy_ne_U hσxC_plane hσxC_not_m hσxC_not_l
      hσxC_ne_O hσxC_ne_I hy_ne_I
  obtain ⟨hW_not_l, hW_ne_I⟩ := OC_point_facts Γ hW_atom hW_le_OC hW_ne_O
  set Wβ := dilation_ext Γ y βx with hWβ_def
  have hWβ_atom : IsAtom Wβ :=
    dilation_ext_atom Γ hβx_atom hy hy_on hy_ne_O hy_ne_U hβx_plane hβx_not_l hβx_ne_O hβx_ne_I hβx_not_m
  have hWβ_le_Oβx : Wβ ≤ Γ.O ⊔ βx := inf_le_left
  have hWβ_plane : Wβ ≤ π := dilation_ext_plane Γ hβx_atom hy hy_on hβx_plane
  have hWβ_ne_O : Wβ ≠ Γ.O :=
    dil_ne_O Γ hy hβx_atom hy_on hy_ne_O hy_ne_U hβx_plane hβx_not_l hβx_ne_O hβx_ne_I
  have hWβ_ne_βx : Wβ ≠ βx :=
    dilation_ext_ne_P Γ hβx_atom hy hy_on hy_ne_O hy_ne_U hβx_plane hβx_not_m hβx_not_l
      hβx_ne_O hβx_ne_I hy_ne_I
  have hUβx_ne : Γ.U ≠ βx := fun h => hβx_not_l (h ▸ (le_sup_right : Γ.U ≤ l))
  have hWβ_not_l : ¬ Wβ ≤ l := by
    intro h
    have hle : Wβ ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ βx) := le_inf h hWβ_le_Oβx
    rw [modular_intersection Γ.hO Γ.hU hβx_atom Γ.hOU (Ne.symm hβx_ne_O) hUβx_ne hβx_not_l] at hle
    exact hWβ_ne_O ((Γ.hO.le_iff.mp hle).resolve_left hWβ_atom.1)
  have hWβ_le_xyE : Wβ ≤ coord_mul Γ x y ⊔ Γ.E := by
    have hkey := dilation_mul_key_identity Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U
      R hR hR_not h_irred
    simp only at hkey
    rw [← hβx_def, ← hWβ_def] at hkey
    rw [hkey]; exact inf_le_right
  have hC_not_Oβx : ¬ Γ.C ≤ Γ.O ⊔ βx := by
    intro h
    have hle : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ βx := sup_le le_sup_left h
    rcases eq_or_lt_of_le hle with he | hlt
    · exact hβx_not_OC (le_sup_right.trans he.ge)
    · have hat := line_height_two Γ.hO hβx_atom (Ne.symm hβx_ne_O)
        (lt_of_lt_of_le Γ.hO.bot_lt le_sup_left) hlt
      exact hOC (((hat.le_iff.mp le_sup_left).resolve_left Γ.hO.1).trans
        ((hat.le_iff.mp le_sup_right).resolve_left Γ.hC.1).symm)
  have hWβ_ne_W : Wβ ≠ W := by
    intro h
    have hle : Wβ ≤ (Γ.O ⊔ βx) ⊓ (Γ.O ⊔ Γ.C) := le_inf hWβ_le_Oβx (h ▸ hW_le_OC)
    rw [modular_intersection Γ.hO hβx_atom Γ.hC (Ne.symm hβx_ne_O) hOC hβx_ne_C hC_not_Oβx] at hle
    exact hWβ_ne_O ((Γ.hO.le_iff.mp hle).resolve_left hWβ_atom.1)
  have hxy_on : coord_mul Γ x y ≤ l := inf_le_right
  have hxy_atom : IsAtom (coord_mul Γ x y) :=
    coord_mul_atom Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U
  have hxy_not_m : ¬ coord_mul Γ x y ≤ m := fun h => hxy_ne_U (Γ.atom_on_both_eq_U hxy_atom hxy_on h)
  have hxy_ne_E : coord_mul Γ x y ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hxy_on)
  have hxy_le_π : coord_mul Γ x y ≤ π := hxy_on.trans hl_le_π
  have hx_lt_xσ : x < x ⊔ σxC := lt_of_le_of_ne le_sup_left
    (fun h => hσxC_ne_x ((hx.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hσxC_atom.1))
  have hxσxC_eq : x ⊔ σxC = x ⊔ Γ.E_I :=
    ((atom_covBy_join hx Γ.hE_I_atom hx_ne_EI).eq_or_eq hx_lt_xσ.le
      (sup_le le_sup_left hσxC_le_xEI)).resolve_left (ne_of_gt hx_lt_xσ)
  have hx_lt_xβ : x < x ⊔ βx := lt_of_le_of_ne le_sup_left
    (fun h => hβx_ne_x ((hx.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hβx_atom.1))
  have hβxx_eq : x ⊔ βx = x ⊔ Γ.E :=
    ((atom_covBy_join hx Γ.hE_atom hx_ne_E).eq_or_eq hx_lt_xβ.le
      (sup_le le_sup_left hβx_le_xE)).resolve_left (ne_of_gt hx_lt_xβ)
  have hWβ_ne_xy : Wβ ≠ coord_mul Γ x y := fun h => hWβ_not_l (h ▸ hxy_on)
  have hxy_lt_Wβ : coord_mul Γ x y < coord_mul Γ x y ⊔ Wβ := lt_of_le_of_ne le_sup_left
    (fun h => hWβ_ne_xy ((hxy_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hWβ_atom.1))
  have hWβxy_eq : coord_mul Γ x y ⊔ Wβ = coord_mul Γ x y ⊔ Γ.E :=
    ((atom_covBy_join hxy_atom Γ.hE_atom hxy_ne_E).eq_or_eq hxy_lt_Wβ.le
      (sup_le le_sup_left hWβ_le_xyE)).resolve_left (ne_of_gt hxy_lt_Wβ)
  have hEI_xE_meet : (x ⊔ Γ.E) ⊓ (x ⊔ Γ.E_I) = x :=
    modular_intersection hx Γ.hE_atom Γ.hE_I_atom hx_ne_E hx_ne_EI hE_ne_EI hEI_not_xE
  have hσxC_not_xE : ¬ σxC ≤ x ⊔ Γ.E := by
    intro h
    have hle : σxC ≤ (x ⊔ Γ.E) ⊓ (x ⊔ Γ.E_I) := le_inf h hσxC_le_xEI
    rw [hEI_xE_meet] at hle
    exact hσxC_ne_x ((hx.le_iff.mp hle).resolve_left hσxC_atom.1)
  have hβx_not_xσxC : ¬ βx ≤ x ⊔ σxC := by
    rw [hxσxC_eq]; intro h
    have hle : βx ≤ (x ⊔ Γ.E) ⊓ (x ⊔ Γ.E_I) := le_inf hβx_le_xE h
    rw [hEI_xE_meet] at hle
    exact hβx_ne_x ((hx.le_iff.mp hle).resolve_left hβx_atom.1)
  have hxm_eq : x ⊔ m = π := by
    have hlt : m < x ⊔ m := lt_of_le_of_ne le_sup_right (fun h => hx_not_m (le_sup_left.trans h.symm.le))
    exact (Γ.m_covBy_π.eq_or_eq hlt.le (sup_le hx_le_π hm_le_π)).resolve_left (ne_of_gt hlt)
  have hx_not_βxσxC : ¬ x ≤ βx ⊔ σxC := by
    intro h
    have hE_le : Γ.E ≤ βx ⊔ σxC := (le_sup_right.trans hβxx_eq.ge).trans (sup_le h le_sup_left)
    have hEI_le : Γ.E_I ≤ βx ⊔ σxC := (le_sup_right.trans hxσxC_eq.ge).trans (sup_le h le_sup_right)
    have hm_le' : m ≤ βx ⊔ σxC := hEEI_m ▸ sup_le hE_le hEI_le
    have hπ_le : π ≤ βx ⊔ σxC := hxm_eq ▸ sup_le h hm_le'
    exact line_ne_π hβx_atom hσxC_atom hβx_ne_σxC
      (le_antisymm (sup_le hβx_plane hσxC_plane) hπ_le)
  have hπA : βx ⊔ x ⊔ σxC = π := by
    refine le_antisymm (sup_le (sup_le hβx_plane hx_le_π) hσxC_plane) ?_
    rw [← hxm_eq]
    refine sup_le ((le_sup_right : x ≤ βx ⊔ x).trans le_sup_left) ?_
    rw [← hEEI_m]
    refine sup_le ?_ ?_
    · exact (le_sup_right.trans hβxx_eq.ge).trans ((sup_comm x βx).le.trans le_sup_left)
    · exact (le_sup_right.trans hxσxC_eq.ge).trans
        (sup_le ((le_sup_right : x ≤ βx ⊔ x).trans le_sup_left) le_sup_right)
  have hOxy_l : Γ.O ⊔ coord_mul Γ x y = l := by
    have hcov : Γ.O ⋖ l := atom_covBy_join Γ.hO Γ.hU Γ.hOU
    have hlt : Γ.O < Γ.O ⊔ coord_mul Γ x y := lt_of_le_of_ne le_sup_left (fun h => hxy_ne_O
      ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hxy_atom.1))
    exact (hcov.eq_or_eq le_sup_left (sup_le le_sup_left hxy_on)).resolve_left (ne_of_gt hlt)
  have hl_cov_π : l ⋖ π := by
    have hV_disj : Γ.V ⊓ l = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have h := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    have hπv : Γ.V ⊔ l = π := by rw [hl_def, hπ_def, sup_comm Γ.V (Γ.O ⊔ Γ.U)]
    have hπv' : l ⊔ Γ.V = π := by rw [hl_def, hπ_def]
    first
      | rwa [hπv] at h
      | rwa [hπv'] at h
  have hlC_π : l ⊔ Γ.C = π := by
    have hlt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
    exact (hl_cov_π.eq_or_eq hlt.le (sup_le hl_le_π Γ.hC_plane)).resolve_left (ne_of_gt hlt)
  have hEW_OC : Γ.E ⊔ W = Γ.O ⊔ Γ.C := by
    have hE_cov : Γ.E ⋖ Γ.O ⊔ Γ.C := line_covers_its_atoms Γ.hO Γ.hC hOC Γ.hE_atom Γ.hE_le_OC
    have hlt : Γ.E < Γ.E ⊔ W := lt_of_le_of_ne le_sup_left (fun h =>
      hW_ne_E ((Γ.hE_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hW_atom.1))
    exact (hE_cov.eq_or_eq hlt.le (sup_le Γ.hE_le_OC hW_le_OC)).resolve_left (ne_of_gt hlt)
  have hπB : Wβ ⊔ coord_mul Γ x y ⊔ W = π := by
    refine le_antisymm (sup_le (sup_le hWβ_plane hxy_le_π) hW_plane) ?_
    have hE_le : Γ.E ≤ Wβ ⊔ coord_mul Γ x y ⊔ W :=
      (le_sup_right.trans hWβxy_eq.ge).trans
        (sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left))
    have hW_le' : W ≤ Wβ ⊔ coord_mul Γ x y ⊔ W := le_sup_right
    have hxy_le' : coord_mul Γ x y ≤ Wβ ⊔ coord_mul Γ x y ⊔ W :=
      le_sup_right.trans le_sup_left
    have hOC_le : Γ.O ⊔ Γ.C ≤ Wβ ⊔ coord_mul Γ x y ⊔ W := hEW_OC ▸ sup_le hE_le hW_le'
    have hπ_eq : Γ.O ⊔ Γ.C ⊔ coord_mul Γ x y = π := by
      rw [show Γ.O ⊔ Γ.C ⊔ coord_mul Γ x y = (Γ.O ⊔ coord_mul Γ x y) ⊔ Γ.C from by ac_rfl, hOxy_l, hlC_π]
    rw [← hπ_eq]; exact sup_le hOC_le hxy_le'
  have h_cov₁₂ : βx ⊔ x ⋖ π :=
    hπA ▸ line_covBy_plane hβx_atom hx hσxC_atom hβx_ne_x hβx_ne_σxC (Ne.symm hσxC_ne_x)
      (fun h => hσxC_not_xE (((sup_comm βx x) ▸ h).trans hβxx_eq.le))
  have h_cov₁₃ : βx ⊔ σxC ⋖ π :=
    (show βx ⊔ σxC ⊔ x = π from by rw [← hπA]; ac_rfl) ▸
      line_covBy_plane hβx_atom hσxC_atom hx hβx_ne_σxC hβx_ne_x hσxC_ne_x hx_not_βxσxC
  have h_cov₂₃ : x ⊔ σxC ⋖ π :=
    (show x ⊔ σxC ⊔ βx = π from by rw [← hπA]; ac_rfl) ▸
      line_covBy_plane hx hσxC_atom hβx_atom (Ne.symm hσxC_ne_x) (Ne.symm hβx_ne_x)
        (Ne.symm hβx_ne_σxC) hβx_not_xσxC
  have par12 : (βx ⊔ x) ⊓ m = (Wβ ⊔ coord_mul Γ x y) ⊓ m := by
    have hl : (βx ⊔ x) ⊓ m = Γ.E := by
      rw [sup_comm βx x, hβxx_eq]; exact line_direction hx hx_not_m Γ.hE_on_m
    have hr : (Wβ ⊔ coord_mul Γ x y) ⊓ m = Γ.E := by
      rw [sup_comm Wβ (coord_mul Γ x y), hWβxy_eq]; exact line_direction hxy_atom hxy_not_m Γ.hE_on_m
    rw [hl, hr]
  have par13 : (βx ⊔ σxC) ⊓ m = (Wβ ⊔ W) ⊓ m :=
    dilation_preserves_direction Γ hβx_atom hσxC_atom y hy hy_on hy_ne_O hy_ne_U hβx_plane hσxC_plane
      hβx_not_m hσxC_not_m hβx_not_l hσxC_not_l hβx_ne_O hσxC_ne_O hβx_ne_σxC hβx_ne_I hσxC_ne_I
      hWβ_ne_W R hR hR_not h_irred
  have hdir_ne : (βx ⊔ x) ⊓ m ≠ (βx ⊔ σxC) ⊓ m := by
    have hl : (βx ⊔ x) ⊓ m = Γ.E := by
      rw [sup_comm βx x, hβxx_eq]; exact line_direction hx hx_not_m Γ.hE_on_m
    rw [hl]; intro h
    have hE_le : Γ.E ≤ βx ⊔ σxC := h ▸ inf_le_left
    have hβx_ne_E : βx ≠ Γ.E := fun hh => hβx_not_m (hh ▸ Γ.hE_on_m)
    have hβxE_le : βx ⊔ Γ.E ≤ x ⊔ Γ.E := sup_le hβx_le_xE le_sup_right
    have hβxE_eq : βx ⊔ Γ.E = x ⊔ Γ.E := by
      rcases eq_or_lt_of_le hβxE_le with he | hlt
      · exact he
      · exact absurd (line_height_two hx Γ.hE_atom hx_ne_E
          (lt_of_lt_of_le hβx_atom.bot_lt le_sup_left) hlt) (fun hat =>
          hβx_ne_E (((hat.le_iff.mp le_sup_left).resolve_left hβx_atom.1).trans
            ((hat.le_iff.mp le_sup_right).resolve_left Γ.hE_atom.1).symm))
    exact hx_not_βxσxC ((le_sup_left.trans hβxE_eq.ge).trans (sup_le le_sup_left hE_le))
  have h_sides₁₂ : βx ⊔ x ≠ Wβ ⊔ coord_mul Γ x y := by
    intro h
    have hxe : x ⊔ Γ.E = coord_mul Γ x y ⊔ Γ.E := by
      rw [show x ⊔ Γ.E = βx ⊔ x from by rw [sup_comm βx x]; exact hβxx_eq.symm,
          show coord_mul Γ x y ⊔ Γ.E = Wβ ⊔ coord_mul Γ x y from by
            rw [sup_comm Wβ (coord_mul Γ x y)]; exact hWβxy_eq.symm, h]
    have h1 : (x ⊔ Γ.E) ⊓ l = x := by
      rw [sup_comm x Γ.E]; exact line_direction Γ.hE_atom Γ.hE_not_l hx_on
    have h2 : (coord_mul Γ x y ⊔ Γ.E) ⊓ l = coord_mul Γ x y := by
      rw [sup_comm _ Γ.E]; exact line_direction Γ.hE_atom Γ.hE_not_l hxy_on
    exact hx_ne_xy (h1.symm.trans ((congrArg (· ⊓ l) hxe).trans h2))
  have h_sides₁₃ : βx ⊔ σxC ≠ Wβ ⊔ W := by
    intro h
    have hW_le' : W ≤ βx ⊔ σxC := h ▸ le_sup_right
    have hσxCW_OC : σxC ⊔ W = Γ.O ⊔ Γ.C := by
      have hσxC_cov : σxC ⋖ Γ.O ⊔ Γ.C := line_covers_its_atoms Γ.hO Γ.hC hOC hσxC_atom hσxC_le_OC
      have hlt : σxC < σxC ⊔ W := lt_of_le_of_ne le_sup_left (fun hh =>
        hW_ne_σxC ((hσxC_atom.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left hW_atom.1))
      exact (hσxC_cov.eq_or_eq hlt.le (sup_le hσxC_le_OC hW_le_OC)).resolve_left (ne_of_gt hlt)
    have hOC_le : Γ.O ⊔ Γ.C ≤ βx ⊔ σxC := hσxCW_OC ▸ sup_le le_sup_right hW_le'
    have hOCβx_π : Γ.O ⊔ Γ.C ⊔ βx = π := by
      have hlt : Γ.O ⊔ Γ.C < Γ.O ⊔ Γ.C ⊔ βx := lt_of_le_of_ne le_sup_left
        (fun hh => hβx_not_OC (le_sup_right.trans hh.symm.le))
      exact ((CoordSystem.OC_covBy_π Γ).eq_or_eq hlt.le
        (sup_le (sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane) hβx_plane)).resolve_left
        (ne_of_gt hlt)
    exact line_ne_π hβx_atom hσxC_atom hβx_ne_σxC
      (le_antisymm (sup_le hβx_plane hσxC_plane) (hOCβx_π ▸ sup_le hOC_le le_sup_left))
  have h_sides₂₃ : x ⊔ σxC ≠ coord_mul Γ x y ⊔ W := by
    intro h
    have h1 : (x ⊔ σxC) ⊓ l = x := by
      rw [hxσxC_eq, sup_comm x Γ.E_I]; exact line_direction Γ.hE_I_atom Γ.hE_I_not_l hx_on
    have h2 : (coord_mul Γ x y ⊔ W) ⊓ l = coord_mul Γ x y := by
      rw [sup_comm _ W]; exact line_direction hW_atom hW_not_l hxy_on
    exact hx_ne_xy (h1.symm.trans ((congrArg (· ⊓ l) h).trans h2))
  have key := three_par_O Γ hβx_atom hx hσxC_atom hWβ_atom hxy_atom hW_atom
    hβx_plane hx_le_π hσxC_plane hWβ_plane hxy_le_π hW_plane
    hWβ_le_Oβx (hxy_on.trans hxO_l.ge) inf_le_left
    hβx_ne_x hβx_ne_σxC (Ne.symm hσxC_ne_x) hWβ_ne_xy hWβ_ne_W
    (fun h => hW_not_l (h ▸ hxy_on))
    h_sides₁₂ h_sides₁₃ h_sides₂₃ hπA hπB
    (Ne.symm hβx_ne_O) (Ne.symm hx_ne_O) (Ne.symm hσxC_ne_O)
    (Ne.symm hWβ_ne_O) (Ne.symm hxy_ne_O) (Ne.symm hW_ne_O)
    (Ne.symm hWβ_ne_βx) hx_ne_xy (Ne.symm hW_ne_σxC)
    hβx_not_m hx_not_m hxy_not_m
    h_cov₁₂ h_cov₁₃ h_cov₂₃ hdir_ne
    R hR hR_not h_irred par12 par13
  have hcrux : (x ⊔ σxC) ⊓ m = Γ.E_I := crux_dir1 Γ x hx hx_on hx_ne_O hx_ne_U hx_ne_I
  exact key.symm.trans hcrux

theorem crux_at_C (Γ : CoordSystem L) (x y : L) (hx : IsAtom x) (hy : IsAtom y)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U)
    (hx_ne_I : x ≠ Γ.I) (hy_ne_I : y ≠ Γ.I)
    (hxy_ne_O : coord_mul Γ x y ≠ Γ.O) (hxy_ne_U : coord_mul Γ x y ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ y (dilation_ext Γ x Γ.C) = dilation_ext Γ (coord_mul Γ x y) Γ.C :=
  crux_at_C_of_gap Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U hxy_ne_O hxy_ne_U
    (gap_direction Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U hx_ne_I hy_ne_I
      hxy_ne_O hxy_ne_U R hR hR_not h_irred)

theorem dilation_compose_at_beta (Γ : CoordSystem L)
    (x y a : L) (hx : IsAtom x) (hy : IsAtom y) (ha : IsAtom a)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O) (ha_ne_O : a ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U) (ha_ne_U : a ≠ Γ.U)
    (hx_ne_I : x ≠ Γ.I) (hy_ne_I : y ≠ Γ.I)

    (hxy_ne_O : coord_mul Γ x y ≠ Γ.O) (hxy_ne_U : coord_mul Γ x y ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ y (dilation_ext Γ x ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E))) =
      dilation_ext Γ (coord_mul Γ x y) ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) := by
  have hxy_atom : IsAtom (coord_mul Γ x y) :=
    coord_mul_atom Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U
  have hxy_on : coord_mul Γ x y ≤ Γ.O ⊔ Γ.U := inf_le_right
  set m := Γ.U ⊔ Γ.V with hm_def
  set βa := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) with hβa_def
  have hβa_atom : IsAtom βa := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hβa_plane : βa ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := beta_plane Γ ha_on
  have hβa_not_l : ¬ βa ≤ Γ.O ⊔ Γ.U := beta_not_l Γ ha ha_on ha_ne_O ha_ne_U
  have hβa_ne_O : βa ≠ Γ.O := fun h => hβa_not_l (h ▸ le_sup_left)
  have hβa_ne_I : βa ≠ Γ.I := fun h => hβa_not_l (h ▸ Γ.hI_on)
  have hβa_le_q : βa ≤ Γ.U ⊔ Γ.C := inf_le_left
  have hβa_le_aE : βa ≤ a ⊔ Γ.E := inf_le_right
  have ha_not_m : ¬ a ≤ Γ.U ⊔ Γ.V := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have ha_ne_E : a ≠ Γ.E := fun h => ha_not_m (h ▸ Γ.hE_on_m)
  have hqm_eq_U : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have hCm : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [hCm, sup_bot_eq]
  have hβa_ne_E : βa ≠ Γ.E := by
    intro h
    have hE_le_q : Γ.E ≤ Γ.U ⊔ Γ.C := h ▸ hβa_le_q
    exact Γ.hEU ((Γ.hU.le_iff.mp (le_inf hE_le_q Γ.hE_on_m |>.trans hqm_eq_U.le))
      |>.resolve_left Γ.hE_atom.1)
  have hβa_not_m : ¬ βa ≤ Γ.U ⊔ Γ.V := by
    intro h
    apply hβa_ne_E
    exact (Γ.hE_atom.le_iff.mp (le_inf hβa_le_aE h |>.trans
      (line_direction ha ha_not_m Γ.hE_on_m).le)).resolve_left hβa_atom.1
  have hO_ne_E : Γ.O ≠ Γ.E := fun h => Γ.hO_not_m (h ▸ Γ.hE_on_m)
  have hOC_ne : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hO_not_aE : ¬ Γ.O ≤ a ⊔ Γ.E := by
    intro hO_le
    have hO_lt_Oa : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
    have hOa_eq_l : Γ.O ⊔ a = Γ.O ⊔ Γ.U :=
      ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt_Oa.le
        (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt hO_lt_Oa)
    have hl_le : Γ.O ⊔ Γ.U ≤ a ⊔ Γ.E := hOa_eq_l ▸ sup_le hO_le le_sup_left
    have ha_lt_l : a < Γ.O ⊔ Γ.U :=
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt
    exact Γ.hE_not_l (le_sup_right.trans
      (((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_on hl_le).resolve_left
        (ne_of_gt ha_lt_l)).symm.le)
  have hβa_not_OC : ¬ βa ≤ Γ.O ⊔ Γ.C := by
    intro h
    have hO_lt_OE : Γ.O < Γ.O ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h' => hO_ne_E ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have hOE_le_OC : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left CoordSystem.hE_le_OC
    have hO_covBy_OC : Γ.O ⋖ Γ.O ⊔ Γ.C := atom_covBy_join Γ.hO Γ.hC hOC_ne
    have hOE_eq_OC : Γ.O ⊔ Γ.E = Γ.O ⊔ Γ.C :=
      (hO_covBy_OC.eq_or_eq hO_lt_OE.le hOE_le_OC).resolve_left (ne_of_gt hO_lt_OE)
    have hmod : (Γ.E ⊔ a) ⊓ (Γ.E ⊔ Γ.O) = Γ.E :=
      modular_intersection Γ.hE_atom ha Γ.hO ha_ne_E.symm hO_ne_E.symm ha_ne_O
        (show ¬ Γ.O ≤ Γ.E ⊔ a from sup_comm a Γ.E ▸ hO_not_aE)
    have hβa_le_meet : βa ≤ (Γ.E ⊔ a) ⊓ (Γ.E ⊔ Γ.O) := by
      refine le_inf ?_ ?_
      · exact sup_comm a Γ.E ▸ hβa_le_aE
      · have hβa_le_OE : βa ≤ Γ.O ⊔ Γ.E := h.trans hOE_eq_OC.symm.le
        exact sup_comm Γ.O Γ.E ▸ hβa_le_OE
    apply hβa_ne_E
    exact (Γ.hE_atom.le_iff.mp (hβa_le_meet.trans hmod.le)).resolve_left hβa_atom.1
  have hC_ne_O : Γ.C ≠ Γ.O := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hC_ne_I : Γ.C ≠ Γ.I := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hCβa : Γ.C ≠ βa := fun h => hβa_not_OC (h ▸ le_sup_right)
  have hd_atom : IsAtom ((Γ.C ⊔ βa) ⊓ (Γ.U ⊔ Γ.V)) :=
    line_meets_m_at_atom Γ.hC hβa_atom hCβa
      (sup_le Γ.hC_plane hβa_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hC_not_m
  have hP1_atom : IsAtom (dilation_ext Γ x Γ.C) :=
    dilation_ext_atom Γ Γ.hC hx hx_on hx_ne_O hx_ne_U Γ.hC_plane Γ.hC_not_l
      hC_ne_O hC_ne_I Γ.hC_not_m
  have hP1_le_OC : dilation_ext Γ x Γ.C ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hP1_plane : dilation_ext Γ x Γ.C ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    dilation_ext_plane Γ Γ.hC hx hx_on Γ.hC_plane
  have hP1_ne_O : dilation_ext Γ x Γ.C ≠ Γ.O :=
    dil_ne_O Γ hx Γ.hC hx_on hx_ne_O hx_ne_U Γ.hC_plane Γ.hC_not_l hC_ne_O hC_ne_I
  have hP1_not_m : ¬ dilation_ext Γ x Γ.C ≤ Γ.U ⊔ Γ.V :=
    dilC_not_m Γ hx hx_on hx_ne_O hx_ne_U
  obtain ⟨hP1_not_l, hP1_ne_I⟩ := OC_point_facts Γ hP1_atom hP1_le_OC hP1_ne_O
  have hP2_atom : IsAtom (dilation_ext Γ (coord_mul Γ x y) Γ.C) :=
    dilation_ext_atom Γ Γ.hC hxy_atom hxy_on hxy_ne_O hxy_ne_U Γ.hC_plane Γ.hC_not_l
      hC_ne_O hC_ne_I Γ.hC_not_m
  have hP2_le_OC : dilation_ext Γ (coord_mul Γ x y) Γ.C ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hP2_ne_O : dilation_ext Γ (coord_mul Γ x y) Γ.C ≠ Γ.O :=
    dil_ne_O Γ hxy_atom Γ.hC hxy_on hxy_ne_O hxy_ne_U Γ.hC_plane Γ.hC_not_l hC_ne_O hC_ne_I
  have hP2_not_m : ¬ dilation_ext Γ (coord_mul Γ x y) Γ.C ≤ Γ.U ⊔ Γ.V :=
    dilC_not_m Γ hxy_atom hxy_on hxy_ne_O hxy_ne_U
  obtain ⟨hQ1_atom, hQ1_plane, hQ1_not_l, hQ1_not_m, hQ1_not_OC, hQ1_ne_I⟩ :=
    dilation_witness_preservation Γ x hx hx_on hx_ne_O hx_ne_U hx_ne_I
      hβa_atom hβa_plane hβa_not_l hβa_not_m hβa_not_OC hβa_ne_I hβa_ne_O
  have hQ1_ne_O : dilation_ext Γ x βa ≠ Γ.O := fun h => hQ1_not_l (h ▸ le_sup_left)
  have hQ1_le_Oβa : dilation_ext Γ x βa ≤ Γ.O ⊔ βa := inf_le_left
  have hQ2_atom : IsAtom (dilation_ext Γ (coord_mul Γ x y) βa) :=
    dilation_ext_atom Γ hβa_atom hxy_atom hxy_on hxy_ne_O hxy_ne_U hβa_plane hβa_not_l
      hβa_ne_O hβa_ne_I hβa_not_m
  have hQ2_le_Oβa : dilation_ext Γ (coord_mul Γ x y) βa ≤ Γ.O ⊔ βa := inf_le_left
  have hW_atom : IsAtom (dilation_ext Γ y (dilation_ext Γ x Γ.C)) :=
    dilation_ext_atom Γ hP1_atom hy hy_on hy_ne_O hy_ne_U hP1_plane hP1_not_l hP1_ne_O
      hP1_ne_I hP1_not_m
  have hW_le_OC : dilation_ext Γ y (dilation_ext Γ x Γ.C) ≤ Γ.O ⊔ Γ.C :=
    (inf_le_left).trans (sup_le le_sup_left hP1_le_OC)
  have hW_ne_O : dilation_ext Γ y (dilation_ext Γ x Γ.C) ≠ Γ.O :=
    dil_ne_O Γ hy hP1_atom hy_on hy_ne_O hy_ne_U hP1_plane hP1_not_l hP1_ne_O hP1_ne_I
  have hW_not_m : ¬ dilation_ext Γ y (dilation_ext Γ x Γ.C) ≤ Γ.U ⊔ Γ.V :=
    dilation_ext_not_m Γ hP1_atom hy hy_on hy_ne_O hy_ne_U hP1_plane hP1_not_m hP1_not_l
      hP1_ne_O hP1_ne_I hy_ne_I
  have hL_atom : IsAtom (dilation_ext Γ y (dilation_ext Γ x βa)) :=
    dilation_ext_atom Γ hQ1_atom hy hy_on hy_ne_O hy_ne_U hQ1_plane hQ1_not_l hQ1_ne_O
      hQ1_ne_I hQ1_not_m
  have hL_le_Oβa : dilation_ext Γ y (dilation_ext Γ x βa) ≤ Γ.O ⊔ βa :=
    (inf_le_left).trans (sup_le le_sup_left hQ1_le_Oβa)
  have hP1_ne_Q1 : dilation_ext Γ x Γ.C ≠ dilation_ext Γ x βa :=
    OC_Oβa_ne Γ hβa_atom hβa_not_OC hP1_atom hP1_le_OC hP1_ne_O hQ1_le_Oβa
  have hP2_ne_Q2 : dilation_ext Γ (coord_mul Γ x y) Γ.C ≠ dilation_ext Γ (coord_mul Γ x y) βa :=
    OC_Oβa_ne Γ hβa_atom hβa_not_OC hP2_atom hP2_le_OC hP2_ne_O hQ2_le_Oβa
  have hW_ne_L : dilation_ext Γ y (dilation_ext Γ x Γ.C) ≠ dilation_ext Γ y (dilation_ext Γ x βa) :=
    OC_Oβa_ne Γ hβa_atom hβa_not_OC hW_atom hW_le_OC hW_ne_O hL_le_Oβa
  have dpd_x : (Γ.C ⊔ βa) ⊓ (Γ.U ⊔ Γ.V) =
      (dilation_ext Γ x Γ.C ⊔ dilation_ext Γ x βa) ⊓ (Γ.U ⊔ Γ.V) :=
    dilation_preserves_direction Γ Γ.hC hβa_atom x hx hx_on hx_ne_O hx_ne_U
      Γ.hC_plane hβa_plane Γ.hC_not_m hβa_not_m Γ.hC_not_l hβa_not_l hC_ne_O hβa_ne_O
      hCβa hC_ne_I hβa_ne_I hP1_ne_Q1 R hR hR_not h_irred
  have dpd_y : (dilation_ext Γ x Γ.C ⊔ dilation_ext Γ x βa) ⊓ (Γ.U ⊔ Γ.V) =
      (dilation_ext Γ y (dilation_ext Γ x Γ.C) ⊔ dilation_ext Γ y (dilation_ext Γ x βa))
        ⊓ (Γ.U ⊔ Γ.V) :=
    dilation_preserves_direction Γ hP1_atom hQ1_atom y hy hy_on hy_ne_O hy_ne_U
      hP1_plane hQ1_plane hP1_not_m hQ1_not_m hP1_not_l hQ1_not_l hP1_ne_O hQ1_ne_O
      hP1_ne_Q1 hP1_ne_I hQ1_ne_I hW_ne_L R hR hR_not h_irred
  have dpd_xy : (Γ.C ⊔ βa) ⊓ (Γ.U ⊔ Γ.V) =
      (dilation_ext Γ (coord_mul Γ x y) Γ.C ⊔ dilation_ext Γ (coord_mul Γ x y) βa)
        ⊓ (Γ.U ⊔ Γ.V) :=
    dilation_preserves_direction Γ Γ.hC hβa_atom (coord_mul Γ x y) hxy_atom hxy_on
      hxy_ne_O hxy_ne_U Γ.hC_plane hβa_plane Γ.hC_not_m hβa_not_m Γ.hC_not_l hβa_not_l
      hC_ne_O hβa_ne_O hCβa hC_ne_I hβa_ne_I hP2_ne_Q2 R hR hR_not h_irred
  have hLHS : dilation_ext Γ y (dilation_ext Γ x βa) =
      (Γ.O ⊔ βa) ⊓ (dilation_ext Γ y (dilation_ext Γ x Γ.C) ⊔ (Γ.C ⊔ βa) ⊓ (Γ.U ⊔ Γ.V)) :=
    point_from_ref Γ hβa_atom hβa_not_OC hW_atom hW_le_OC hW_ne_O hW_not_m
      hL_atom hL_le_Oβa hW_ne_L hd_atom (dpd_y.symm.trans dpd_x.symm)
  have hRHS : dilation_ext Γ (coord_mul Γ x y) βa =
      (Γ.O ⊔ βa) ⊓ (dilation_ext Γ (coord_mul Γ x y) Γ.C ⊔ (Γ.C ⊔ βa) ⊓ (Γ.U ⊔ Γ.V)) :=
    point_from_ref Γ hβa_atom hβa_not_OC hP2_atom hP2_le_OC hP2_ne_O hP2_not_m
      hQ2_atom hQ2_le_Oβa hP2_ne_Q2 hd_atom dpd_xy.symm
  rw [hLHS, hRHS, crux_at_C Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U
    hx_ne_I hy_ne_I hxy_ne_O hxy_ne_U R hR hR_not h_irred]

/-- The pure-lattice core of the E-recovery: if `σP` and `σP'` are atoms whose
    join meets `m` exactly at `E`, with `σP` on the line `O⊔P` and `σP'` off `m`,
    then `σP` is recovered as the meet of line `σP'⊔E` with line `O⊔P`. -/
theorem recovery_core (Γ : CoordSystem L) {σP σP' P : L}
    (hσP_atom : IsAtom σP) (hσP'_atom : IsAtom σP')
    (hP : IsAtom P) (hP_ne_O : P ≠ Γ.O)
    (hσP'_not_m : ¬ σP' ≤ Γ.U ⊔ Γ.V)
    (hσP_ne_σP' : σP ≠ σP')
    (h_inf : (σP ⊔ σP') ⊓ (Γ.U ⊔ Γ.V) = Γ.E)
    (hσP_le_OP : σP ≤ Γ.O ⊔ P)
    (hE_not_OP : ¬ Γ.E ≤ Γ.O ⊔ P) :
    σP = (σP' ⊔ Γ.E) ⊓ (Γ.O ⊔ P) := by
  set m := Γ.U ⊔ Γ.V
  have hE_le_σσ' : Γ.E ≤ σP ⊔ σP' := h_inf ▸ inf_le_left
  have hσP'_ne_E : σP' ≠ Γ.E := fun h => hσP'_not_m (h ▸ Γ.hE_on_m)
  have hσP'_covBy_σP'σP : σP' ⋖ σP' ⊔ σP :=
    atom_covBy_join hσP'_atom hσP_atom (Ne.symm hσP_ne_σP')
  have hσP'E_le_σP'σP : σP' ⊔ Γ.E ≤ σP' ⊔ σP := by
    refine sup_le le_sup_left ?_
    exact hE_le_σσ'.trans (sup_comm σP σP' ▸ le_rfl)
  have hσP'_lt_σP'E : σP' < σP' ⊔ Γ.E := lt_of_le_of_ne le_sup_left
    (fun h => hσP'_ne_E
      ((hσP'_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_atom.1).symm)
  have hσP'E_eq : σP' ⊔ Γ.E = σP' ⊔ σP :=
    (hσP'_covBy_σP'σP.eq_or_eq hσP'_lt_σP'E.le hσP'E_le_σP'σP).resolve_left
      (ne_of_gt hσP'_lt_σP'E)
  have hσP_le_σP'E : σP ≤ σP' ⊔ Γ.E := hσP'E_eq.symm ▸ (le_sup_right : σP ≤ σP' ⊔ σP)
  have hσP_le_meet : σP ≤ (σP' ⊔ Γ.E) ⊓ (Γ.O ⊔ P) := le_inf hσP_le_σP'E hσP_le_OP
  have hRHS_atom : IsAtom ((σP' ⊔ Γ.E) ⊓ (Γ.O ⊔ P)) :=
    meet_of_lines_is_atom hσP'_atom Γ.hE_atom Γ.hO hP hσP'_ne_E (Ne.symm hP_ne_O)
      (fun h => hE_not_OP (le_sup_right.trans h))
      (fun h => hσP_atom.1 (le_bot_iff.mp (h ▸ hσP_le_meet)))
  exact (hRHS_atom.le_iff.mp hσP_le_meet).resolve_left hσP_atom.1

/-- All witness facts for the β-image `βa = (U⊔C) ⊓ (a⊔E)` of an l-atom `a`. -/
theorem beta_witness (Γ : CoordSystem L) {a : L} (ha : IsAtom a)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    IsAtom ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ∧
    (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ∧
    ¬ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.O ⊔ Γ.U ∧
    ¬ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.U ⊔ Γ.V ∧
    ¬ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.O ⊔ Γ.C ∧
    (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≠ Γ.I ∧
    (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≠ Γ.O := by
  set βa := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) with hβa_def
  have hβa_atom : IsAtom βa := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hβa_plane : βa ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := beta_plane Γ ha_on
  have hβa_not_l : ¬ βa ≤ Γ.O ⊔ Γ.U := beta_not_l Γ ha ha_on ha_ne_O ha_ne_U
  have hβa_ne_O : βa ≠ Γ.O := fun h => hβa_not_l (h ▸ le_sup_left)
  have hβa_ne_I : βa ≠ Γ.I := fun h => hβa_not_l (h ▸ Γ.hI_on)
  have hβa_le_q : βa ≤ Γ.U ⊔ Γ.C := inf_le_left
  have hβa_le_aE : βa ≤ a ⊔ Γ.E := inf_le_right
  have ha_not_m : ¬ a ≤ Γ.U ⊔ Γ.V := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have ha_ne_E : a ≠ Γ.E := fun h => ha_not_m (h ▸ Γ.hE_on_m)
  have hqm_eq_U : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have hCm : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [hCm, sup_bot_eq]
  have hβa_ne_E : βa ≠ Γ.E := by
    intro h
    have hE_le_q : Γ.E ≤ Γ.U ⊔ Γ.C := h ▸ hβa_le_q
    exact Γ.hEU ((Γ.hU.le_iff.mp (le_inf hE_le_q Γ.hE_on_m |>.trans hqm_eq_U.le))
      |>.resolve_left Γ.hE_atom.1)
  have hβa_not_m : ¬ βa ≤ Γ.U ⊔ Γ.V := by
    intro h
    apply hβa_ne_E
    exact (Γ.hE_atom.le_iff.mp (le_inf hβa_le_aE h |>.trans
      (line_direction ha ha_not_m Γ.hE_on_m).le)).resolve_left hβa_atom.1
  have hO_ne_E : Γ.O ≠ Γ.E := fun h => Γ.hO_not_m (h ▸ Γ.hE_on_m)
  have hOC_ne : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hO_not_aE : ¬ Γ.O ≤ a ⊔ Γ.E := by
    intro hO_le
    have hO_lt_Oa : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
    have hOa_eq_l : Γ.O ⊔ a = Γ.O ⊔ Γ.U :=
      ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt_Oa.le
        (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt hO_lt_Oa)
    have hl_le : Γ.O ⊔ Γ.U ≤ a ⊔ Γ.E := hOa_eq_l ▸ sup_le hO_le le_sup_left
    have ha_lt_l : a < Γ.O ⊔ Γ.U :=
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt
    exact Γ.hE_not_l (le_sup_right.trans
      (((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_on hl_le).resolve_left
        (ne_of_gt ha_lt_l)).symm.le)
  have hβa_not_OC : ¬ βa ≤ Γ.O ⊔ Γ.C := by
    intro h
    have hO_lt_OE : Γ.O < Γ.O ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h' => hO_ne_E ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have hOE_le_OC : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left CoordSystem.hE_le_OC
    have hO_covBy_OC : Γ.O ⋖ Γ.O ⊔ Γ.C := atom_covBy_join Γ.hO Γ.hC hOC_ne
    have hOE_eq_OC : Γ.O ⊔ Γ.E = Γ.O ⊔ Γ.C :=
      (hO_covBy_OC.eq_or_eq hO_lt_OE.le hOE_le_OC).resolve_left (ne_of_gt hO_lt_OE)
    have hmod : (Γ.E ⊔ a) ⊓ (Γ.E ⊔ Γ.O) = Γ.E :=
      modular_intersection Γ.hE_atom ha Γ.hO ha_ne_E.symm hO_ne_E.symm ha_ne_O
        (show ¬ Γ.O ≤ Γ.E ⊔ a from sup_comm a Γ.E ▸ hO_not_aE)
    have hβa_le_meet : βa ≤ (Γ.E ⊔ a) ⊓ (Γ.E ⊔ Γ.O) := by
      refine le_inf ?_ ?_
      · exact sup_comm a Γ.E ▸ hβa_le_aE
      · have hβa_le_OE : βa ≤ Γ.O ⊔ Γ.E := h.trans hOE_eq_OC.symm.le
        exact sup_comm Γ.O Γ.E ▸ hβa_le_OE
    apply hβa_ne_E
    exact (Γ.hE_atom.le_iff.mp (hβa_le_meet.trans hmod.le)).resolve_left hβa_atom.1
  exact ⟨hβa_atom, hβa_plane, hβa_not_l, hβa_not_m, hβa_not_OC, hβa_ne_I, hβa_ne_O⟩

/-- The β-cast of a witness `P` is realized as the β-image of the l-atom
    `a = (O⊔U) ⊓ (P⊔E)`. -/
theorem beta_cast_realize (Γ : CoordSystem L) {P : L} (hP : IsAtom P)
    (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U)
    (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V) (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) :
    IsAtom ((Γ.O ⊔ Γ.U) ⊓ (P ⊔ Γ.E)) ∧
    (Γ.O ⊔ Γ.U) ⊓ (P ⊔ Γ.E) ≤ Γ.O ⊔ Γ.U ∧
    (Γ.O ⊔ Γ.U) ⊓ (P ⊔ Γ.E) ≠ Γ.O ∧
    (Γ.O ⊔ Γ.U) ⊓ (P ⊔ Γ.E) ≠ Γ.U ∧
    beta_cast Γ P = (Γ.U ⊔ Γ.C) ⊓ ((Γ.O ⊔ Γ.U) ⊓ (P ⊔ Γ.E) ⊔ Γ.E) := by
  set l := Γ.O ⊔ Γ.U with hl_def
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def
  set a := l ⊓ (P ⊔ Γ.E) with ha_def
  have hP_ne_O : P ≠ Γ.O := fun h => hP_not_l (h ▸ le_sup_left)
  have hP_ne_E : P ≠ Γ.E := fun h => hP_not_m (h ▸ Γ.hE_on_m)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hPE_le_π : P ⊔ Γ.E ≤ π :=
    sup_le hP_plane (Γ.hE_on_m.trans Γ.m_covBy_π.le)
  have hl_covBy_π : l ⋖ π :=
    line_covBy_plane Γ.hO Γ.hU Γ.hV Γ.hOU (fun h => Γ.hV_off (h ▸ le_sup_left))
      hUV Γ.hV_off
  have ha_atom : IsAtom a := by
    rw [ha_def, inf_comm]
    exact line_meets_m_at_atom hP Γ.hE_atom hP_ne_E hPE_le_π hl_covBy_π.le hl_covBy_π hP_not_l
  have ha_le_l : a ≤ l := inf_le_left
  have ha_le_PE : a ≤ P ⊔ Γ.E := inf_le_right
  have ha_ne_E : a ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ ha_le_l)
  -- a ⊔ E = P ⊔ E
  have hPE_covBy_P : P ⋖ P ⊔ Γ.E := atom_covBy_join hP Γ.hE_atom hP_ne_E
  have haE_le_PE : a ⊔ Γ.E ≤ P ⊔ Γ.E := sup_le ha_le_PE le_sup_right
  have hE_covBy_PE : Γ.E ⋖ P ⊔ Γ.E := by
    rw [sup_comm]; exact atom_covBy_join Γ.hE_atom hP hP_ne_E.symm
  have haE_ne_E : a ⊔ Γ.E ≠ Γ.E := fun h =>
    ha_ne_E ((Γ.hE_atom.le_iff.mp (le_sup_left.trans h.le)).resolve_left ha_atom.1)
  have hE_lt_aE : Γ.E < a ⊔ Γ.E := lt_of_le_of_ne le_sup_right (Ne.symm haE_ne_E)
  have haE_eq_PE : a ⊔ Γ.E = P ⊔ Γ.E :=
    (hE_covBy_PE.eq_or_eq (le_sup_right : Γ.E ≤ a ⊔ Γ.E) haE_le_PE).resolve_left
      (ne_of_gt hE_lt_aE)
  -- a ≠ O (else P ≤ O⊔E ≤ O⊔C)
  have ha_ne_O : a ≠ Γ.O := by
    intro h
    have hO_le_PE : Γ.O ≤ P ⊔ Γ.E := h ▸ ha_le_PE
    have hO_ne_E : Γ.O ≠ Γ.E := fun h' => Γ.hO_not_m (h' ▸ Γ.hE_on_m)
    have hOE_le_PE : Γ.O ⊔ Γ.E ≤ P ⊔ Γ.E := sup_le hO_le_PE le_sup_right
    have hOE_ne_E : Γ.O ⊔ Γ.E ≠ Γ.E := fun h' =>
      hO_ne_E ((Γ.hE_atom.le_iff.mp (le_sup_left.trans h'.le)).resolve_left Γ.hO.1)
    have hOE_eq_PE : Γ.O ⊔ Γ.E = P ⊔ Γ.E :=
      (hE_covBy_PE.eq_or_eq (le_sup_right : Γ.E ≤ Γ.O ⊔ Γ.E) hOE_le_PE).resolve_left hOE_ne_E
    have hP_le_OE : P ≤ Γ.O ⊔ Γ.E := hOE_eq_PE ▸ le_sup_left
    have hOE_le_OC : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left CoordSystem.hE_le_OC
    exact hP_not_OC (hP_le_OE.trans hOE_le_OC)
  -- a ≠ U (else E ≤ P⊔U ∩ m = U)
  have ha_ne_U : a ≠ Γ.U := by
    intro h
    have hU_le_PE : Γ.U ≤ P ⊔ Γ.E := h ▸ ha_le_PE
    have hPU_le_PE : P ⊔ Γ.U ≤ P ⊔ Γ.E := sup_le le_sup_left hU_le_PE
    have hU_ne_P : Γ.U ≠ P := fun h' => hP_not_l (h' ▸ le_sup_right)
    have hP_lt_PU : P < P ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h' => hU_ne_P ((hP.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1))
    have hPU_eq_PE : P ⊔ Γ.U = P ⊔ Γ.E :=
      (hPE_covBy_P.eq_or_eq hP_lt_PU.le hPU_le_PE).resolve_left (ne_of_gt hP_lt_PU)
    have hPU_inf_m : (P ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U :=
      line_direction hP hP_not_m (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)
    have hE_le_PU : Γ.E ≤ P ⊔ Γ.U := hPU_eq_PE.symm ▸ le_sup_right
    have hE_le_U : Γ.E ≤ Γ.U := hPU_inf_m ▸ le_inf hE_le_PU Γ.hE_on_m
    exact Γ.hEU ((Γ.hU.le_iff.mp hE_le_U).resolve_left Γ.hE_atom.1)
  refine ⟨ha_atom, ha_le_l, ha_ne_O, ha_ne_U, ?_⟩
  show (Γ.U ⊔ Γ.C) ⊓ (P ⊔ Γ.E) = (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)
  rw [haE_eq_PE]

/-- Composite E-recovery: the σ_y∘σ_x image of a witness `P` is recovered from
    its β-cast image, mirroring `recovery_via_E` but pushed through two dilations
    via direction-preservation (so the inner `σ_x P` need not be off `q`). -/
theorem composite_recovery (Γ : CoordSystem L)
    (x y : L) (hx : IsAtom x) (hy : IsAtom y)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U)
    (hx_ne_I : x ≠ Γ.I) (hy_ne_I : y ≠ Γ.I)
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_not_q : ¬ P ≤ Γ.U ⊔ Γ.C)
    (hP_ne_I : P ≠ Γ.I)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ y (dilation_ext Γ x P) =
      (dilation_ext Γ y (dilation_ext Γ x (beta_cast Γ P)) ⊔ Γ.E) ⊓ (Γ.O ⊔ P) := by
  set m := Γ.U ⊔ Γ.V with hm_def
  set B := beta_cast Γ P with hB_def
  have hP_ne_O : P ≠ Γ.O := fun h => hP_not_l (h ▸ le_sup_left)
  -- B's witness facts via realization as a β-image
  obtain ⟨ha_atom, ha_le_l, ha_ne_O, ha_ne_U, hB_eq⟩ :=
    beta_cast_realize Γ hP hP_plane hP_not_l hP_not_m hP_not_OC
  obtain ⟨hBw_atom, hBw_plane, hBw_not_l, hBw_not_m, hBw_not_OC, hBw_ne_I, hBw_ne_O⟩ :=
    beta_witness Γ ha_atom ha_le_l ha_ne_O ha_ne_U
  rw [← hB_eq] at hBw_atom hBw_plane hBw_not_l hBw_not_m hBw_not_OC hBw_ne_I hBw_ne_O
  -- E off O⊔P
  have hE_not_OP : ¬ Γ.E ≤ Γ.O ⊔ P := by
    intro hE_le
    have hO_ne_E : Γ.O ≠ Γ.E := fun h => Γ.hO_not_m (h ▸ Γ.hE_on_m)
    have hOE_le_OP : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ P := sup_le le_sup_left hE_le
    have hO_covBy_OE : Γ.O ⋖ Γ.O ⊔ Γ.E := atom_covBy_join Γ.hO Γ.hE_atom hO_ne_E
    have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
    have hOE_eq_OP : Γ.O ⊔ Γ.E = Γ.O ⊔ P :=
      (hO_covBy_OP.eq_or_eq le_sup_left hOE_le_OP).resolve_left
        (ne_of_gt hO_covBy_OE.lt)
    have hOE_le_OC : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left CoordSystem.hE_le_OC
    exact hP_not_OC (le_sup_right.trans (hOE_eq_OP ▸ hOE_le_OC))
  -- recovery for σ_x at P
  have hRecX : dilation_ext Γ x P =
      (dilation_ext Γ x B ⊔ Γ.E) ⊓ (Γ.O ⊔ P) :=
    recovery_via_E Γ x hx hx_on hx_ne_O hx_ne_U hx_ne_I hP hP_plane hP_not_l hP_not_m
      hP_not_OC hP_not_q hP_ne_I R hR hR_not h_irred
  set Q := dilation_ext Γ x P with hQ_def
  set B₁ := dilation_ext Γ x B with hB1_def
  have hQ_le_BE : Q ≤ B₁ ⊔ Γ.E := hRecX.le.trans inf_le_left
  -- Q is a witness
  obtain ⟨hQ_atom, hQ_plane, hQ_not_l, hQ_not_m, hQ_not_OC, hQ_ne_I⟩ :=
    dilation_witness_preservation Γ x hx hx_on hx_ne_O hx_ne_U hx_ne_I
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I hP_ne_O
  have hQ_ne_O : Q ≠ Γ.O := fun h => hQ_not_l (h ▸ le_sup_left)
  -- B₁ = σ_x B is a witness
  obtain ⟨hB1_atom, hB1_plane, hB1_not_l, hB1_not_m, hB1_not_OC, hB1_ne_I⟩ :=
    dilation_witness_preservation Γ x hx hx_on hx_ne_O hx_ne_U hx_ne_I
      hBw_atom hBw_plane hBw_not_l hBw_not_m hBw_not_OC hBw_ne_I hBw_ne_O
  have hB1_ne_O : B₁ ≠ Γ.O := fun h => hB1_not_l (h ▸ le_sup_left)
  -- B ≠ P and ¬ B ≤ O⊔P  (uses P off q)
  have hB_le_q : B ≤ Γ.U ⊔ Γ.C := by rw [hB_def, beta_cast]; exact inf_le_left
  have hB_le_PE : B ≤ P ⊔ Γ.E := by rw [hB_def, beta_cast]; exact inf_le_right
  have hB_ne_P : B ≠ P := fun h => hP_not_q (h ▸ hB_le_q)
  have hP_ne_E : P ≠ Γ.E := fun h => hP_not_m (h ▸ Γ.hE_on_m)
  have hO_ne_E : Γ.O ≠ Γ.E := fun h => Γ.hO_not_m (h ▸ Γ.hE_on_m)
  have hB_not_OP : ¬ B ≤ Γ.O ⊔ P := by
    intro hB_le
    have hOP_PE_eq : (P ⊔ Γ.O) ⊓ (P ⊔ Γ.E) = P :=
      modular_intersection hP Γ.hO Γ.hE_atom hP_ne_O hP_ne_E hO_ne_E
        (fun h => hE_not_OP (sup_comm Γ.O P ▸ h))
    have hB_le_P : B ≤ P :=
      le_inf (sup_comm Γ.O P ▸ hB_le) hB_le_PE |>.trans hOP_PE_eq.le
    exact hB_ne_P ((hP.le_iff.mp hB_le_P).resolve_left hBw_atom.1)
  -- ¬ σ_x B ≤ O⊔P, hence Q ≠ B₁
  have hB1_le_OB : B₁ ≤ Γ.O ⊔ B := inf_le_left
  have hB1_not_OP : ¬ B₁ ≤ Γ.O ⊔ P := by
    intro hB1_le
    have hmeet : (Γ.O ⊔ P) ⊓ (Γ.O ⊔ B) = Γ.O :=
      modular_intersection Γ.hO hP hBw_atom (Ne.symm hP_ne_O) (Ne.symm hBw_ne_O)
        (Ne.symm hB_ne_P) hB_not_OP
    exact hB1_ne_O ((Γ.hO.le_iff.mp (hmeet ▸ le_inf hB1_le hB1_le_OB)).resolve_left
      hB1_atom.1)
  have hQ_ne_B1 : Q ≠ B₁ := by
    intro h
    exact hB1_not_OP (h ▸ (hRecX.le.trans inf_le_right))
  -- O ⊔ Q = O ⊔ P
  have hQ_le_OP : Q ≤ Γ.O ⊔ P := hRecX.le.trans inf_le_right
  have hOQ_eq_OP : Γ.O ⊔ Q = Γ.O ⊔ P := by
    have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
    have hO_lt_OQ : Γ.O < Γ.O ⊔ Q := lt_of_le_of_ne le_sup_left
      (fun h => hQ_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hQ_atom.1))
    exact (hO_covBy_OP.eq_or_eq le_sup_left (sup_le le_sup_left hQ_le_OP)).resolve_left
      (ne_of_gt hO_lt_OQ)
  -- direction at the y-step
  -- first: (Q ⊔ B₁) ⊓ m = E
  have hB1_ne_E : B₁ ≠ Γ.E := fun h => hB1_not_m (le_of_eq h |>.trans Γ.hE_on_m)
  have hQB1_eq_B1E : Q ⊔ B₁ = B₁ ⊔ Γ.E := by
    have hB1_covBy_B1E : B₁ ⋖ B₁ ⊔ Γ.E := atom_covBy_join hB1_atom Γ.hE_atom hB1_ne_E
    have hQB1_le : Q ⊔ B₁ ≤ B₁ ⊔ Γ.E := sup_le hQ_le_BE le_sup_left
    have hB1_lt : B₁ < Q ⊔ B₁ := lt_of_le_of_ne le_sup_right
      (fun h => hQ_ne_B1 ((hB1_atom.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left
        hQ_atom.1))
    exact (hB1_covBy_B1E.eq_or_eq hB1_lt.le hQB1_le).resolve_left (ne_of_gt hB1_lt)
  have hQB1_inf_m : (Q ⊔ B₁) ⊓ m = Γ.E := by
    rw [hQB1_eq_B1E]
    exact line_direction hB1_atom hB1_not_m Γ.hE_on_m
  -- σ_y Q ≠ σ_y B₁
  set W := dilation_ext Γ y Q with hW_def
  set W' := dilation_ext Γ y B₁ with hW'_def
  obtain ⟨hW_atom, _hW_plane, hW_not_l, _hW_not_m, _hW_not_OC, _hW_ne_I⟩ :=
    dilation_witness_preservation Γ y hy hy_on hy_ne_O hy_ne_U hy_ne_I
      hQ_atom hQ_plane hQ_not_l hQ_not_m hQ_not_OC hQ_ne_I hQ_ne_O
  obtain ⟨hW'_atom, _hW'_plane, hW'_not_l, hW'_not_m, _hW'_not_OC, _hW'_ne_I⟩ :=
    dilation_witness_preservation Γ y hy hy_on hy_ne_O hy_ne_U hy_ne_I
      hB1_atom hB1_plane hB1_not_l hB1_not_m hB1_not_OC hB1_ne_I hB1_ne_O
  have hW_ne_O : W ≠ Γ.O := fun h => hW_not_l (h ▸ le_sup_left)
  have hW_le_OQ : W ≤ Γ.O ⊔ Q := inf_le_left
  have hW'_le_OB1 : W' ≤ Γ.O ⊔ B₁ := inf_le_left
  have hW_ne_W' : W ≠ W' := by
    intro h
    have hB1_not_OQ : ¬ B₁ ≤ Γ.O ⊔ Q := by rw [hOQ_eq_OP]; exact hB1_not_OP
    have hmeet : (Γ.O ⊔ Q) ⊓ (Γ.O ⊔ B₁) = Γ.O :=
      modular_intersection Γ.hO hQ_atom hB1_atom (Ne.symm hQ_ne_O) (Ne.symm hB1_ne_O)
        hQ_ne_B1 hB1_not_OQ
    exact hW_ne_O ((Γ.hO.le_iff.mp (hmeet ▸ le_inf hW_le_OQ (h ▸ hW'_le_OB1))).resolve_left
      hW_atom.1)
  -- direction preservation
  have hDPD : (Q ⊔ B₁) ⊓ m = (W ⊔ W') ⊓ m :=
    dilation_preserves_direction Γ hQ_atom hB1_atom y hy hy_on hy_ne_O hy_ne_U
      hQ_plane hB1_plane hQ_not_m hB1_not_m hQ_not_l hB1_not_l hQ_ne_O hB1_ne_O
      hQ_ne_B1 hQ_ne_I hB1_ne_I hW_ne_W' R hR hR_not h_irred
  have hWW'_inf_m : (W ⊔ W') ⊓ m = Γ.E := hDPD ▸ hQB1_inf_m
  -- apply recovery_core with base point Q
  have hE_not_OQ : ¬ Γ.E ≤ Γ.O ⊔ Q := by rw [hOQ_eq_OP]; exact hE_not_OP
  have hcore : W = (W' ⊔ Γ.E) ⊓ (Γ.O ⊔ Q) :=
    recovery_core Γ hW_atom hW'_atom hQ_atom hQ_ne_O hW'_not_m hW_ne_W'
      hWW'_inf_m hW_le_OQ hE_not_OQ
  rw [hcore, hOQ_eq_OP]

/-- E-recovery for ALL non-degenerate parameters `c` (including `c = I`), where
    `recovery_via_E` only handles `c ≠ I`. -/
theorem recovery_all (Γ : CoordSystem L)
    (c : L) (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U)
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_not_q : ¬ P ≤ Γ.U ⊔ Γ.C)
    (hP_ne_I : P ≠ Γ.I)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ c P =
      (dilation_ext Γ c (beta_cast Γ P) ⊔ Γ.E) ⊓ (Γ.O ⊔ P) := by
  by_cases hcI : c = Γ.I
  · subst hcI
    set B := beta_cast Γ P with hB_def
    have hP_ne_O : P ≠ Γ.O := fun h => hP_not_l (h ▸ le_sup_left)
    have hP_ne_E : P ≠ Γ.E := fun h => hP_not_m (h ▸ Γ.hE_on_m)
    -- B facts
    obtain ⟨ha_atom, ha_le_l, ha_ne_O, ha_ne_U, hB_eq⟩ :=
      beta_cast_realize Γ hP hP_plane hP_not_l hP_not_m hP_not_OC
    obtain ⟨hBw_atom, hBw_plane, hBw_not_l, hBw_not_m, _, _, _⟩ :=
      beta_witness Γ ha_atom ha_le_l ha_ne_O ha_ne_U
    rw [← hB_eq] at hBw_atom hBw_plane hBw_not_l hBw_not_m
    have hE_not_OP : ¬ Γ.E ≤ Γ.O ⊔ P := by
      intro hE_le
      have hO_ne_E : Γ.O ≠ Γ.E := fun h => Γ.hO_not_m (h ▸ Γ.hE_on_m)
      have hOE_le_OP : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ P := sup_le le_sup_left hE_le
      have hO_covBy_OE : Γ.O ⋖ Γ.O ⊔ Γ.E := atom_covBy_join Γ.hO Γ.hE_atom hO_ne_E
      have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
      have hOE_eq_OP : Γ.O ⊔ Γ.E = Γ.O ⊔ P :=
        (hO_covBy_OP.eq_or_eq le_sup_left hOE_le_OP).resolve_left (ne_of_gt hO_covBy_OE.lt)
      exact hP_not_OC (le_sup_right.trans (hOE_eq_OP ▸ sup_le le_sup_left CoordSystem.hE_le_OC))
    rw [dilation_ext_identity Γ hP hP_plane hP_not_l,
        dilation_ext_identity Γ hBw_atom hBw_plane hBw_not_l]
    -- goal: P = (B ⊔ E) ⊓ (O ⊔ P)
    have hB_le_PE : B ≤ P ⊔ Γ.E := by rw [hB_def, beta_cast]; exact inf_le_right
    have hB_ne_E : B ≠ Γ.E := fun h => hBw_not_m (le_of_eq h |>.trans Γ.hE_on_m)
    have hE_covBy_PE : Γ.E ⋖ P ⊔ Γ.E := by
      rw [sup_comm]; exact atom_covBy_join Γ.hE_atom hP hP_ne_E.symm
    have hBE_ne_E : B ⊔ Γ.E ≠ Γ.E := fun h =>
      hB_ne_E ((Γ.hE_atom.le_iff.mp (le_sup_left.trans h.le)).resolve_left hBw_atom.1)
    have hBE_eq_PE : B ⊔ Γ.E = P ⊔ Γ.E :=
      (hE_covBy_PE.eq_or_eq (le_sup_right : Γ.E ≤ B ⊔ Γ.E)
        (sup_le hB_le_PE le_sup_right)).resolve_left hBE_ne_E
    have hO_not_PE : ¬ Γ.O ≤ P ⊔ Γ.E := by
      intro hO_le
      have hOP_le : Γ.O ⊔ P ≤ P ⊔ Γ.E := sup_le hO_le le_sup_left
      have hP_lt : P < Γ.O ⊔ P := lt_of_le_of_ne le_sup_right
        (fun h => hP_ne_O ((hP.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left Γ.hO.1).symm)
      have hPE_eq : P ⊔ Γ.E = Γ.O ⊔ P :=
        ((atom_covBy_join hP Γ.hE_atom hP_ne_E).eq_or_eq hP_lt.le hOP_le).resolve_left
          (ne_of_gt hP_lt) |>.symm
      exact hE_not_OP (le_sup_right.trans hPE_eq.le)
    rw [hBE_eq_PE]
    have hE_ne_O : Γ.E ≠ Γ.O := fun h => Γ.hO_not_m (h ▸ Γ.hE_on_m)
    have hmeet : (P ⊔ Γ.E) ⊓ (P ⊔ Γ.O) = P :=
      modular_intersection hP Γ.hE_atom Γ.hO hP_ne_E hP_ne_O hE_ne_O hO_not_PE
    rw [show Γ.O ⊔ P = P ⊔ Γ.O from sup_comm _ _, hmeet]
  · exact recovery_via_E Γ c hc hc_on hc_ne_O hc_ne_U hcI hP hP_plane hP_not_l hP_not_m
      hP_not_OC hP_not_q hP_ne_I R hR hR_not h_irred

theorem dilation_compose_at_witness (Γ : CoordSystem L)
    (x y : L) (hx : IsAtom x) (hy : IsAtom y)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U)
    (hxy_ne_O : coord_mul Γ x y ≠ Γ.O) (hxy_ne_U : coord_mul Γ x y ≠ Γ.U)
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_ne_I : P ≠ Γ.I)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ (coord_mul Γ x y) P =
      dilation_ext Γ y (dilation_ext Γ x P) := by
  have hP_ne_O : P ≠ Γ.O := fun h => hP_not_l (h ▸ le_sup_left)
  by_cases hxI : x = Γ.I
  · subst hxI
    rw [dilation_ext_identity Γ hP hP_plane hP_not_l, coord_mul_left_one Γ y hy hy_on hy_ne_U]
  by_cases hyI : y = Γ.I
  · subst hyI
    obtain ⟨hQ_atom, hQ_plane, hQ_not_l, _, _, _⟩ :=
      dilation_witness_preservation Γ x hx hx_on hx_ne_O hx_ne_U hxI
        hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I hP_ne_O
    rw [coord_mul_right_one Γ x hx hx_on, dilation_ext_identity Γ hQ_atom hQ_plane hQ_not_l]
  -- main case: x ≠ I, y ≠ I
  obtain ⟨ha_atom, ha_le_l, ha_ne_O, ha_ne_U, hB_eq⟩ :=
    beta_cast_realize Γ hP hP_plane hP_not_l hP_not_m hP_not_OC
  have hcab : dilation_ext Γ y (dilation_ext Γ x (beta_cast Γ P)) =
      dilation_ext Γ (coord_mul Γ x y) (beta_cast Γ P) := by
    rw [hB_eq]
    exact dilation_compose_at_beta Γ x y ((Γ.O ⊔ Γ.U) ⊓ (P ⊔ Γ.E)) hx hy ha_atom
      hx_on hy_on ha_le_l hx_ne_O hy_ne_O ha_ne_O hx_ne_U hy_ne_U ha_ne_U hxI hyI
      hxy_ne_O hxy_ne_U R hR hR_not h_irred
  by_cases hPq : P ≤ Γ.U ⊔ Γ.C
  · -- P is itself a β-image: P = beta_cast Γ P
    have hbc_atom : IsAtom (beta_cast Γ P) :=
      hB_eq ▸ (beta_witness Γ ha_atom ha_le_l ha_ne_O ha_ne_U).1
    have hP_le_bc : P ≤ beta_cast Γ P := by
      rw [beta_cast]; exact le_inf hPq le_sup_left
    have hP_eq : P = beta_cast Γ P := (hbc_atom.le_iff.mp hP_le_bc).resolve_left hP.1
    rw [hP_eq]; exact hcab.symm
  · -- ¬ P ≤ q : recovery route
    have hLHS : dilation_ext Γ (coord_mul Γ x y) P =
        (dilation_ext Γ (coord_mul Γ x y) (beta_cast Γ P) ⊔ Γ.E) ⊓ (Γ.O ⊔ P) :=
      recovery_all Γ (coord_mul Γ x y)
        (coord_mul_atom Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U)
        inf_le_right hxy_ne_O hxy_ne_U hP hP_plane hP_not_l hP_not_m hP_not_OC hPq hP_ne_I
        R hR hR_not h_irred
    have hRHS : dilation_ext Γ y (dilation_ext Γ x P) =
        (dilation_ext Γ y (dilation_ext Γ x (beta_cast Γ P)) ⊔ Γ.E) ⊓ (Γ.O ⊔ P) :=
      composite_recovery Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U hxI hyI
        hP hP_plane hP_not_l hP_not_m hP_not_OC hPq hP_ne_I R hR hR_not h_irred
    rw [hLHS, hRHS, hcab]

theorem coord_mul_assoc (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (ha_ne_I : a ≠ Γ.I)

    (hs_ne_O : coord_mul Γ a b ≠ Γ.O) (hs_ne_U : coord_mul Γ a b ≠ Γ.U)
    (ht_ne_O : coord_mul Γ b c ≠ Γ.O) (ht_ne_U : coord_mul Γ b c ≠ Γ.U)
    (hsc_ne_O : coord_mul Γ (coord_mul Γ a b) c ≠ Γ.O)
    (hsc_ne_U : coord_mul Γ (coord_mul Γ a b) c ≠ Γ.U)
    (hat_ne_O : coord_mul Γ a (coord_mul Γ b c) ≠ Γ.O)
    (hat_ne_U : coord_mul Γ a (coord_mul Γ b c) ≠ Γ.U)

    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_ne_I : P ≠ Γ.I) (hP_ne_O : P ≠ Γ.O)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_mul Γ (coord_mul Γ a b) c = coord_mul Γ a (coord_mul Γ b c) := by
  set s := coord_mul Γ a b with hs_def
  set t := coord_mul Γ b c with ht_def

  have hs_atom : IsAtom s := coord_mul_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
  have ht_atom : IsAtom t := coord_mul_atom Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U
  have hs_on : s ≤ Γ.O ⊔ Γ.U := by show coord_mul Γ a b ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have ht_on : t ≤ Γ.O ⊔ Γ.U := by show coord_mul Γ b c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hsc_atom : IsAtom (coord_mul Γ s c) :=
    coord_mul_atom Γ s c hs_atom hc hs_on hc_on hs_ne_O hc_ne_O hs_ne_U hc_ne_U
  have hat_atom : IsAtom (coord_mul Γ a t) :=
    coord_mul_atom Γ a t ha ht_atom ha_on ht_on ha_ne_O ht_ne_O ha_ne_U ht_ne_U
  have hsc_on : coord_mul Γ s c ≤ Γ.O ⊔ Γ.U := by
    show coord_mul Γ (coord_mul Γ a b) c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hat_on : coord_mul Γ a t ≤ Γ.O ⊔ Γ.U := by
    show coord_mul Γ a (coord_mul Γ b c) ≤ Γ.O ⊔ Γ.U; exact inf_le_right

  obtain ⟨hσaP_atom, hσaP_plane, hσaP_not_l, hσaP_not_m, hσaP_not_OC, hσaP_ne_I⟩ :=
    dilation_witness_preservation Γ a ha ha_on ha_ne_O ha_ne_U ha_ne_I
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I hP_ne_O

  have h_LHS_step : dilation_ext Γ (coord_mul Γ s c) P =
      dilation_ext Γ c (dilation_ext Γ s P) :=
    dilation_compose_at_witness Γ s c hs_atom hc hs_on hc_on
      hs_ne_O hc_ne_O hs_ne_U hc_ne_U hsc_ne_O hsc_ne_U
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I R hR hR_not h_irred

  have h_s_decomp : dilation_ext Γ s P = dilation_ext Γ b (dilation_ext Γ a P) :=
    dilation_compose_at_witness Γ a b ha hb ha_on hb_on
      ha_ne_O hb_ne_O ha_ne_U hb_ne_U hs_ne_O hs_ne_U
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I R hR hR_not h_irred

  have h_RHS_step : dilation_ext Γ (coord_mul Γ a t) P =
      dilation_ext Γ t (dilation_ext Γ a P) :=
    dilation_compose_at_witness Γ a t ha ht_atom ha_on ht_on
      ha_ne_O ht_ne_O ha_ne_U ht_ne_U hat_ne_O hat_ne_U
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I R hR hR_not h_irred

  have h_t_decomp : dilation_ext Γ t (dilation_ext Γ a P) =
      dilation_ext Γ c (dilation_ext Γ b (dilation_ext Γ a P)) :=
    dilation_compose_at_witness Γ b c hb hc hb_on hc_on
      hb_ne_O hc_ne_O hb_ne_U hc_ne_U ht_ne_O ht_ne_U
      hσaP_atom hσaP_plane hσaP_not_l hσaP_not_m hσaP_not_OC hσaP_ne_I
      R hR hR_not h_irred

  have h_agree : dilation_ext Γ (coord_mul Γ s c) P =
      dilation_ext Γ (coord_mul Γ a t) P := by
    rw [h_LHS_step, h_s_decomp, h_RHS_step, h_t_decomp]

  exact dilation_determined_by_param Γ hsc_atom hat_atom hsc_on hat_on
    hsc_ne_O hat_ne_O hsc_ne_U hat_ne_U
    hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I h_agree

end Foam.Bridges
