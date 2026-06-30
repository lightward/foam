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

theorem crux_at_C (Γ : CoordSystem L) (x y : L) (hx : IsAtom x) (hy : IsAtom y)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U)
    (hx_ne_I : x ≠ Γ.I) (hy_ne_I : y ≠ Γ.I)
    (hxy_ne_O : coord_mul Γ x y ≠ Γ.O) (hxy_ne_U : coord_mul Γ x y ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ y (dilation_ext Γ x Γ.C) = dilation_ext Γ (coord_mul Γ x y) Γ.C := by
  sorry

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

theorem dilation_compose_at_witness (Γ : CoordSystem L)
    (x y : L) (hx : IsAtom x) (hy : IsAtom y)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U)
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_ne_I : P ≠ Γ.I)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ (coord_mul Γ x y) P =
      dilation_ext Γ y (dilation_ext Γ x P) := by
  sorry

theorem coord_mul_assoc (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (ha_ne_I : a ≠ Γ.I)
    (_hab : a ≠ b) (_hbc : b ≠ c) (_hac : a ≠ c)

    (hs_ne_O : coord_mul Γ a b ≠ Γ.O) (hs_ne_U : coord_mul Γ a b ≠ Γ.U)
    (ht_ne_O : coord_mul Γ b c ≠ Γ.O) (ht_ne_U : coord_mul Γ b c ≠ Γ.U)
    (_hsc : coord_mul Γ a b ≠ c) (_hat : a ≠ coord_mul Γ b c)
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
      hs_ne_O hc_ne_O hs_ne_U hc_ne_U
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I R hR hR_not h_irred

  have h_s_decomp : dilation_ext Γ s P = dilation_ext Γ b (dilation_ext Γ a P) :=
    dilation_compose_at_witness Γ a b ha hb ha_on hb_on
      ha_ne_O hb_ne_O ha_ne_U hb_ne_U
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I R hR hR_not h_irred

  have h_RHS_step : dilation_ext Γ (coord_mul Γ a t) P =
      dilation_ext Γ t (dilation_ext Γ a P) :=
    dilation_compose_at_witness Γ a t ha ht_atom ha_on ht_on
      ha_ne_O ht_ne_O ha_ne_U ht_ne_U
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I R hR hR_not h_irred

  have h_t_decomp : dilation_ext Γ t (dilation_ext Γ a P) =
      dilation_ext Γ c (dilation_ext Γ b (dilation_ext Γ a P)) :=
    dilation_compose_at_witness Γ b c hb hc hb_on hc_on
      hb_ne_O hc_ne_O hb_ne_U hc_ne_U
      hσaP_atom hσaP_plane hσaP_not_l hσaP_not_m hσaP_not_OC hσaP_ne_I
      R hR hR_not h_irred

  have h_agree : dilation_ext Γ (coord_mul Γ s c) P =
      dilation_ext Γ (coord_mul Γ a t) P := by
    rw [h_LHS_step, h_s_decomp, h_RHS_step, h_t_decomp]

  exact dilation_determined_by_param Γ hsc_atom hat_atom hsc_on hat_on
    hsc_ne_O hat_ne_O hsc_ne_U hat_ne_U
    hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I h_agree

end Foam.Bridges
