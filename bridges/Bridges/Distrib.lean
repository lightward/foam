import Bridges.MulKeyIdentity
import Bridges.Assoc
namespace Foam.Bridges
universe u
variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

theorem coord_mul_right_distrib (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hab : a ≠ b)
    (hs_ne_O : coord_add Γ a b ≠ Γ.O) (hs_ne_U : coord_add Γ a b ≠ Γ.U)
    (hac_ne_O : coord_mul Γ a c ≠ Γ.O) (hac_ne_U : coord_mul Γ a c ≠ Γ.U)
    (hbc_ne_O : coord_mul Γ b c ≠ Γ.O) (hbc_ne_U : coord_mul Γ b c ≠ Γ.U)
    (hac_ne_bc : coord_mul Γ a c ≠ coord_mul Γ b c)
    (hsc_ne_O : coord_mul Γ (coord_add Γ a b) c ≠ Γ.O)
    (hsc_ne_U : coord_mul Γ (coord_add Γ a b) c ≠ Γ.U)
    (hacbc_ne_O : coord_add Γ (coord_mul Γ a c) (coord_mul Γ b c) ≠ Γ.O)
    (hacbc_ne_U : coord_add Γ (coord_mul Γ a c) (coord_mul Γ b c) ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_mul Γ (coord_add Γ a b) c =
      coord_add Γ (coord_mul Γ a c) (coord_mul Γ b c) := by

  set l := Γ.O ⊔ Γ.U with hl_def
  set m := Γ.U ⊔ Γ.V with hm_def
  set q := Γ.U ⊔ Γ.C with hq_def
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def
  set s := coord_add Γ a b with hs_def
  set ac := coord_mul Γ a c with hac_def
  set bc := coord_mul Γ b c with hbc_def
  set sc := coord_mul Γ s c with hsc_def

  set C_b := (Γ.U ⊔ Γ.C) ⊓ (b ⊔ Γ.E) with hCb_def
  set C_s := (Γ.U ⊔ Γ.C) ⊓ (s ⊔ Γ.E) with hCs_def
  set σ := dilation_ext Γ c Γ.C with hσ_def
  set e_b := (Γ.O ⊔ C_b) ⊓ m with heb_def

  set C_bc := parallelogram_completion Γ.O bc Γ.C m with hCbc_def

  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hl_covBy : l ⋖ π := by
    rw [show l = Γ.O ⊔ Γ.U from rfl]; rw [show π = Γ.O ⊔ Γ.U ⊔ Γ.V from rfl]
    have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hIC : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)

  have hs_atom : IsAtom s := coord_add_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
  have hs_on : s ≤ l := by show coord_add Γ a b ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hac_atom : IsAtom ac := coord_mul_atom Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U
  have hac_on : ac ≤ l := by show coord_mul Γ a c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hbc_atom : IsAtom bc := coord_mul_atom Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U
  have hbc_on : bc ≤ l := by show coord_mul Γ b c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hsc_atom : IsAtom sc := coord_mul_atom Γ s c hs_atom hc hs_on hc_on hs_ne_O hc_ne_O hs_ne_U hc_ne_U
  have hsc_on : sc ≤ l := by show coord_mul Γ s c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hacbc_atom : IsAtom (coord_add Γ ac bc) := coord_add_atom Γ ac bc hac_atom hbc_atom hac_on hbc_on hac_ne_O hbc_ne_O hac_ne_U hbc_ne_U
  have hacbc_on : coord_add Γ ac bc ≤ l := by
    show coord_add Γ (coord_mul Γ a c) (coord_mul Γ b c) ≤ Γ.O ⊔ Γ.U; exact inf_le_right

  have hCb_atom : IsAtom C_b := beta_atom Γ hb hb_on hb_ne_O hb_ne_U
  have hCs_atom : IsAtom C_s := beta_atom Γ hs_atom hs_on hs_ne_O hs_ne_U
  have hCb_on_q : C_b ≤ q := inf_le_left
  have hCs_on_q : C_s ≤ q := inf_le_left
  have hCb_not_l : ¬ C_b ≤ l := beta_not_l Γ hb hb_on hb_ne_O hb_ne_U
  have hCs_not_l : ¬ C_s ≤ l := beta_not_l Γ hs_atom hs_on hs_ne_O hs_ne_U
  have hCb_plane : C_b ≤ π := beta_plane Γ hb_on
  have hCs_plane : C_s ≤ π := beta_plane Γ hs_on

  have hlm_eq_U : l ⊓ m = Γ.U := by
    show (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    rw [show Γ.O ⊔ Γ.U = Γ.U ⊔ Γ.O from sup_comm _ _,
        sup_inf_assoc_of_le Γ.O (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
    rw [this, sup_bot_eq]
  have hlq_eq_U : l ⊓ q = Γ.U := by
    rw [show l = Γ.O ⊔ Γ.U from rfl, show q = Γ.U ⊔ Γ.C from rfl]
    rw [show Γ.O ⊔ Γ.U = Γ.U ⊔ Γ.O from sup_comm _ _,
        sup_inf_assoc_of_le Γ.O (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.C)]
    have : Γ.O ⊓ (Γ.U ⊔ Γ.C) = ⊥ := by
      rcases Γ.hO.le_iff.mp inf_le_left with h | h
      · exact h
      ·
        exfalso
        have hO_le_UC : Γ.O ≤ Γ.U ⊔ Γ.C := h ▸ inf_le_right
        have hl_le_UC : Γ.O ⊔ Γ.U ≤ Γ.U ⊔ Γ.C := sup_le hO_le_UC le_sup_left

        have hUC_le_π : Γ.U ⊔ Γ.C ≤ π :=
          sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane
        rcases hl_covBy.eq_or_eq hl_le_UC hUC_le_π with h1 | h2
        · exact Γ.hC_not_l ((le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C).trans h1.le)
        ·

          have hC_inf_m : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
            (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun hh => Γ.hC_not_m (hh ▸ inf_le_right))
          have hUCm : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
            rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V), hC_inf_m, sup_bot_eq]

          have hV_le_UC : Γ.V ≤ Γ.U ⊔ Γ.C := (le_sup_right : Γ.V ≤ π).trans h2.symm.le

          have hV_le_U : Γ.V ≤ Γ.U := le_inf hV_le_UC (le_sup_right : Γ.V ≤ Γ.U ⊔ Γ.V)
            |>.trans hUCm.le
          exact hUV ((Γ.hU.le_iff.mp hV_le_U).resolve_left Γ.hV.1).symm
    rw [this, sup_bot_eq]
  have hqm_eq_U : q ⊓ m = Γ.U := by
    rw [show q = Γ.U ⊔ Γ.C from rfl, show m = Γ.U ⊔ Γ.V from rfl]
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [this, sup_bot_eq]

  have hE_inf_l : Γ.E ⊓ l = ⊥ :=
    (Γ.hE_atom.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hE_not_l (h ▸ inf_le_right))

  have hObc_eq_l : Γ.O ⊔ bc = l := by
    have hO_lt : Γ.O < Γ.O ⊔ bc := lt_of_le_of_ne le_sup_left
      (fun h => hbc_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hbc_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hbc_on)).resolve_left (ne_of_gt hO_lt)
  have hCbc_eq_beta : C_bc = q ⊓ (bc ⊔ Γ.E) := by
    show parallelogram_completion Γ.O bc Γ.C m = q ⊓ (bc ⊔ Γ.E)
    show (Γ.C ⊔ (Γ.O ⊔ bc) ⊓ m) ⊓ (bc ⊔ (Γ.O ⊔ Γ.C) ⊓ m) = q ⊓ (bc ⊔ Γ.E)
    rw [hObc_eq_l, hlm_eq_U, show Γ.C ⊔ Γ.U = q from by
      rw [show q = Γ.U ⊔ Γ.C from rfl]; exact sup_comm _ _]
    rfl
  have hCbc_atom : IsAtom C_bc := hCbc_eq_beta ▸ beta_atom Γ hbc_atom hbc_on hbc_ne_O hbc_ne_U
  have hCbc_on_q : C_bc ≤ q := hCbc_eq_beta ▸ inf_le_left

  have pc_eq_beta : ∀ (x : L), Γ.O ⊔ x = l →
      parallelogram_completion Γ.O x Γ.C m = q ⊓ (x ⊔ Γ.E) := by
    intro x hOx_eq_l
    show (Γ.C ⊔ (Γ.O ⊔ x) ⊓ m) ⊓ (x ⊔ (Γ.O ⊔ Γ.C) ⊓ m) = q ⊓ (x ⊔ Γ.E)
    rw [hOx_eq_l, hlm_eq_U]
    rw [show Γ.C ⊔ Γ.U = q from by rw [show q = Γ.U ⊔ Γ.C from rfl]; exact sup_comm _ _]
    rfl

  have hOb_eq_l : Γ.O ⊔ b = l := by
    have hO_lt : Γ.O < Γ.O ⊔ b := lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hb.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hb_on)).resolve_left (ne_of_gt hO_lt)
  have hOs_eq_l : Γ.O ⊔ s = l := by
    have hO_lt : Γ.O < Γ.O ⊔ s := lt_of_le_of_ne le_sup_left
      (fun h => hs_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hs_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hs_on)).resolve_left (ne_of_gt hO_lt)

  have hCb_eq_pc : C_b = parallelogram_completion Γ.O b Γ.C m := (pc_eq_beta b hOb_eq_l).symm
  have hCs_eq_pc : C_s = parallelogram_completion Γ.O s Γ.C m := (pc_eq_beta s hOs_eq_l).symm

  have h_ki : parallelogram_completion Γ.O a C_b m = C_s := by
    rw [hCb_eq_pc, hCs_eq_pc]
    exact key_identity Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U hab R hR hR_not h_irred

  have hCs_le_a_eb : C_s ≤ a ⊔ e_b := by
    rw [← h_ki]; unfold parallelogram_completion
    simp only [show (Γ.O ⊔ a) ⊓ m = Γ.U from by
      rw [show (Γ.O ⊔ a) = l from by
        have : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
          (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
        exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq this.le
          (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt this)
      ]; exact hlm_eq_U]
    exact inf_le_right

  set C'_bc := dilation_ext Γ c C_b with hC'bc_def
  set C'_sc := dilation_ext Γ c C_s with hC'sc_def

  have h_mki_b : C'_bc = (σ ⊔ Γ.U) ⊓ (bc ⊔ Γ.E) :=
    dilation_mul_key_identity Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U R hR hR_not h_irred

  have h_mki_s : C'_sc = (σ ⊔ Γ.U) ⊓ (sc ⊔ Γ.E) :=
    dilation_mul_key_identity Γ s c hs_atom hc hs_on hc_on hs_ne_O hc_ne_O hs_ne_U hc_ne_U R hR hR_not h_irred

  set C_sc := q ⊓ (sc ⊔ Γ.E) with hCsc_def
  set e_bc := (Γ.O ⊔ C_bc) ⊓ m with hebc_def

  have heb_atom : IsAtom e_b := by
    rw [show e_b = (Γ.O ⊔ C_b) ⊓ m from rfl]
    exact line_meets_m_at_atom Γ.hO hCb_atom (Ne.symm (fun h => hCb_not_l (h ▸ le_sup_left)))
      (sup_le (show Γ.O ≤ π from le_sup_left.trans le_sup_left) hCb_plane) hm_le_π Γ.m_covBy_π Γ.hO_not_m
  have hCbc_plane : C_bc ≤ π := hCbc_eq_beta ▸ beta_plane Γ hbc_on
  have hCbc_not_l : ¬ C_bc ≤ l := hCbc_eq_beta ▸ beta_not_l Γ hbc_atom hbc_on hbc_ne_O hbc_ne_U
  have hO_ne_Cbc : Γ.O ≠ C_bc := fun h => hCbc_not_l (h ▸ le_sup_left)
  have hebc_atom : IsAtom e_bc := by
    exact line_meets_m_at_atom Γ.hO hCbc_atom hO_ne_Cbc
      (sup_le (show Γ.O ≤ π from le_sup_left.trans le_sup_left) hCbc_plane) hm_le_π Γ.m_covBy_π Γ.hO_not_m

  have hOac_eq_l : Γ.O ⊔ ac = l := by
    have hO_lt : Γ.O < Γ.O ⊔ ac := lt_of_le_of_ne le_sup_left
      (fun h => hac_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hac_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hac_on)).resolve_left (ne_of_gt hO_lt)
  have hpc_eq : parallelogram_completion Γ.O ac C_bc m =
      (C_bc ⊔ Γ.U) ⊓ (ac ⊔ e_bc) := by
    show (C_bc ⊔ (Γ.O ⊔ ac) ⊓ m) ⊓ (ac ⊔ (Γ.O ⊔ C_bc) ⊓ m) = (C_bc ⊔ Γ.U) ⊓ (ac ⊔ e_bc)
    rw [hOac_eq_l, hlm_eq_U]

  have hCbc_ne_U : C_bc ≠ Γ.U := by
    intro h

    have hU_le_bcE : Γ.U ≤ bc ⊔ Γ.E := by
      rw [← h, hCbc_eq_beta]; exact inf_le_right
    have hbcEl : (bc ⊔ Γ.E) ⊓ l = bc := by
      change (bc ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = bc; rw [sup_comm bc Γ.E]
      exact line_direction Γ.hE_atom Γ.hE_not_l hbc_on
    have hU_le_bc : Γ.U ≤ bc := by
      have hU_le_inf : Γ.U ≤ (bc ⊔ Γ.E) ⊓ l :=
        le_inf hU_le_bcE (show Γ.U ≤ l from le_sup_right)
      exact hU_le_inf.trans hbcEl.le
    exact hbc_ne_U ((hbc_atom.le_iff.mp hU_le_bc).resolve_left Γ.hU.1).symm
  have hCbcU_eq_q : C_bc ⊔ Γ.U = q := by
    rw [sup_comm]
    have hCbc_le_q : C_bc ≤ q := hCbc_on_q

    have hCbc_lt : Γ.U < Γ.U ⊔ C_bc := by
      apply lt_of_le_of_ne le_sup_left
      intro h; apply hCbc_ne_U
      exact ((Γ.hU.le_iff.mp (le_sup_right.trans h.symm.le : C_bc ≤ Γ.U)).resolve_left
        hCbc_atom.1)
    rw [show q = Γ.U ⊔ Γ.C from rfl]
    exact ((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq hCbc_lt.le
      (sup_le le_sup_left hCbc_le_q)).resolve_left (ne_of_gt hCbc_lt)

  have hpc_eq' : parallelogram_completion Γ.O ac C_bc m = q ⊓ (ac ⊔ e_bc) := by
    rw [hpc_eq, hCbcU_eq_q]

  have h_core : C_sc = q ⊓ (ac ⊔ e_bc) := by

    have hσ_atom : IsAtom σ :=
      dilation_ext_atom Γ Γ.hC hc hc_on hc_ne_O hc_ne_U
        Γ.hC_plane Γ.hC_not_l (Ne.symm (fun h => Γ.hC_not_l (h ▸ le_sup_left)))
        (fun h => Γ.hC_not_l (h ▸ Γ.hI_on)) Γ.hC_not_m
    have hσ_on_OC : σ ≤ Γ.O ⊔ Γ.C := by
      show dilation_ext Γ c Γ.C ≤ Γ.O ⊔ Γ.C; unfold dilation_ext; exact inf_le_left
    have hσ_plane : σ ≤ π := dilation_ext_plane Γ Γ.hC hc hc_on Γ.hC_plane
    have hσ_not_m : ¬ σ ≤ m := by
      by_cases hcI : c = Γ.I
      ·
        subst hcI; rw [show σ = Γ.C from dilation_ext_identity Γ Γ.hC Γ.hC_plane Γ.hC_not_l]
        exact Γ.hC_not_m
      · exact dilation_ext_not_m Γ Γ.hC hc hc_on hc_ne_O hc_ne_U
          Γ.hC_plane Γ.hC_not_m Γ.hC_not_l (Ne.symm (fun h => Γ.hC_not_l (h ▸ le_sup_left)))
          (fun h => Γ.hC_not_l (h ▸ Γ.hI_on)) hcI
    have hσ_not_l : ¬ σ ≤ l := by
      intro hσl

      by_cases hcI : c = Γ.I
      ·
        subst hcI
        have hσ_eq_C : σ = Γ.C := dilation_ext_identity Γ Γ.hC Γ.hC_plane Γ.hC_not_l
        exact Γ.hC_not_l (hσ_eq_C ▸ hσl)
      ·
        have hOCl : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
          change (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.O
          rw [sup_comm Γ.O Γ.C]
          exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
            line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
        have hσ_eq_O : σ = Γ.O := (Γ.hO.le_iff.mp ((le_inf hσ_on_OC hσl).trans hOCl.le)).resolve_left hσ_atom.1
        have hσ_on_cEI : σ ≤ c ⊔ (Γ.I ⊔ Γ.C) ⊓ m := by
          show dilation_ext Γ c Γ.C ≤ c ⊔ (Γ.I ⊔ Γ.C) ⊓ m; unfold dilation_ext; exact inf_le_right
        have hO_le_cEI : Γ.O ≤ c ⊔ (Γ.I ⊔ Γ.C) ⊓ m := hσ_eq_O.symm ▸ hσ_on_cEI

        have hcEI_l : (c ⊔ Γ.E_I) ⊓ l = c := by
          change (c ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = c; rw [sup_comm c Γ.E_I]
          exact line_direction Γ.hE_I_atom Γ.hE_I_not_l hc_on
        exact hc_ne_O ((hc.le_iff.mp (le_inf hO_le_cEI (show Γ.O ≤ l from le_sup_left)
          |>.trans hcEI_l.le)).resolve_left Γ.hO.1).symm

    have h_core_σC : Γ.C = σ → C_sc = q ⊓ (ac ⊔ e_bc) := by
      intro hCσ_eq

      have coord_mul_id : ∀ (x : L), IsAtom x → x ≤ l → x ≠ Γ.U → coord_mul Γ x c = x := by
        intro x hx hx_on hx_ne_U
        show ((Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) ⊔ (x ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ Γ.U) = x
        have hσ_eq : (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) = σ := (dilation_ext_C Γ c hc hc_on hc_ne_O hc_ne_U).symm
        rw [hσ_eq, ← hCσ_eq]

        have hx_ne_C : x ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hx_on)
        have hx_not_m : ¬ x ≤ m := fun h => hx_ne_U (Γ.atom_on_both_eq_U hx hx_on h)
        have hxC_le_π : x ⊔ Γ.C ≤ π := sup_le (hx_on.trans le_sup_left) Γ.hC_plane
        have hd_atom : IsAtom ((x ⊔ Γ.C) ⊓ m) :=
          line_meets_m_at_atom hx Γ.hC hx_ne_C hxC_le_π hm_le_π Γ.m_covBy_π hx_not_m

        have hC_ne_d : Γ.C ≠ (x ⊔ Γ.C) ⊓ m :=
          fun h => Γ.hC_not_m (h ▸ inf_le_right)
        have hC_lt_Cd : Γ.C < Γ.C ⊔ (x ⊔ Γ.C) ⊓ m := lt_of_le_of_ne le_sup_left
          (fun h => hC_ne_d ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hd_atom.1).symm)
        have hCd_le : Γ.C ⊔ (x ⊔ Γ.C) ⊓ m ≤ Γ.C ⊔ x :=
          sup_le le_sup_left ((inf_le_left : (x ⊔ Γ.C) ⊓ m ≤ x ⊔ Γ.C).trans (sup_comm x Γ.C).le)
        have hCd_eq_Cx : Γ.C ⊔ (x ⊔ Γ.C) ⊓ m = Γ.C ⊔ x :=
          ((atom_covBy_join Γ.hC hx hx_ne_C.symm).eq_or_eq hC_lt_Cd.le hCd_le).resolve_left
            (ne_of_gt hC_lt_Cd)
        have hC_inf_l : Γ.C ⊓ l = ⊥ :=
          (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_l (h ▸ inf_le_right))

        calc (Γ.C ⊔ (x ⊔ Γ.C) ⊓ m) ⊓ (Γ.O ⊔ Γ.U)
            = (Γ.C ⊔ x) ⊓ (Γ.O ⊔ Γ.U) := by rw [hCd_eq_Cx]
          _ = (x ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) := by rw [sup_comm Γ.C x]
          _ = x ⊔ Γ.C ⊓ (Γ.O ⊔ Γ.U) := sup_inf_assoc_of_le Γ.C hx_on
          _ = x ⊔ ⊥ := by rw [hC_inf_l]
          _ = x := by simp

      have hsc_eq_s : sc = s := coord_mul_id s hs_atom hs_on hs_ne_U
      have hac_eq_a : ac = a := coord_mul_id a ha ha_on ha_ne_U
      have hbc_eq_b : bc = b := coord_mul_id b hb hb_on hb_ne_U
      have hCbc_eq_Cb : C_bc = C_b := by
        rw [show C_bc = q ⊓ (bc ⊔ Γ.E) from hCbc_eq_beta, hbc_eq_b]
      have hebc_eq_eb : e_bc = e_b := by
        show (Γ.O ⊔ C_bc) ⊓ m = e_b; rw [hCbc_eq_Cb]
      show C_sc = q ⊓ (ac ⊔ e_bc)
      rw [show C_sc = q ⊓ (sc ⊔ Γ.E) from rfl, hsc_eq_s, hac_eq_a, hebc_eq_eb]

      have hCb_ne_U' : C_b ≠ Γ.U := by
        intro h
        have hU_le_bE : Γ.U ≤ b ⊔ Γ.E := by rw [← h]; exact inf_le_right
        have hbEl : (b ⊔ Γ.E) ⊓ l = b := by
          change (b ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = b; rw [sup_comm b Γ.E]
          exact line_direction Γ.hE_atom Γ.hE_not_l hb_on
        exact hb_ne_U ((hb.le_iff.mp (le_inf hU_le_bE (show Γ.U ≤ l from le_sup_right) |>.trans hbEl.le)).resolve_left Γ.hU.1).symm
      have hCbU_eq_q : C_b ⊔ Γ.U = q := by
        rw [sup_comm]
        have hU_lt : Γ.U < Γ.U ⊔ C_b := lt_of_le_of_ne le_sup_left
          (fun h => hCb_ne_U' ((Γ.hU.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hCb_atom.1))
        exact ((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq hU_lt.le
          (sup_le le_sup_left hCb_on_q)).resolve_left (ne_of_gt hU_lt)
      have hpc_a_Cb : parallelogram_completion Γ.O a C_b m = q ⊓ (a ⊔ e_b) := by
        show (C_b ⊔ (Γ.O ⊔ a) ⊓ m) ⊓ (a ⊔ (Γ.O ⊔ C_b) ⊓ m) = q ⊓ (a ⊔ e_b)
        have hOa_eq_l : Γ.O ⊔ a = l := by
          have hO_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
            (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
          exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
            (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt hO_lt)
        rw [hOa_eq_l, hlm_eq_U, hCbU_eq_q]
      rw [show C_s = q ⊓ (s ⊔ Γ.E) from rfl] at h_ki
      rw [← hpc_a_Cb, ← h_ki]

    by_cases hCσ_case : Γ.C = σ
    · exact h_core_σC hCσ_case

    have hCσ : Γ.C ≠ σ := hCσ_case

    have hCs_ne_O : C_s ≠ Γ.O := fun h => hCs_not_l (h ▸ le_sup_left)
    have hCs_ne_I : C_s ≠ Γ.I := fun h => hCs_not_l (h ▸ Γ.hI_on)
    have hCs_ne_U : C_s ≠ Γ.U := fun h => hCs_not_l (h ▸ le_sup_right)
    have hCs_not_m : ¬ C_s ≤ m := by
      intro h
      have hs_not_m : ¬ s ≤ m := fun hm => hs_ne_U (Γ.atom_on_both_eq_U hs_atom hs_on hm)
      have hCs_le_sE : C_s ≤ s ⊔ Γ.E := inf_le_right
      have hsE_dir : (s ⊔ Γ.E) ⊓ m = Γ.E := line_direction hs_atom hs_not_m Γ.hE_on_m
      have hCs_eq_E : C_s = Γ.E :=
        (Γ.hE_atom.le_iff.mp (le_inf hCs_le_sE h |>.trans hsE_dir.le)).resolve_left hCs_atom.1
      have hE_le_q : Γ.E ≤ q := hCs_eq_E ▸ hCs_on_q
      exact Γ.hEU ((Γ.hU.le_iff.mp (le_inf hE_le_q Γ.hE_on_m |>.trans hqm_eq_U.le)).resolve_left Γ.hE_atom.1)

    have hC'sc_atom : IsAtom C'_sc :=
      dilation_ext_atom Γ hCs_atom hc hc_on hc_ne_O hc_ne_U hCs_plane hCs_not_l hCs_ne_O hCs_ne_I hCs_not_m
    have hC'sc_plane : C'_sc ≤ π := dilation_ext_plane Γ hCs_atom hc hc_on hCs_plane
    have hC'sc_not_m : ¬ C'_sc ≤ m := by
      by_cases hcI : c = Γ.I
      · subst hcI
        have hC'sc_eq_Cs : C'_sc = C_s := dilation_ext_identity Γ hCs_atom hCs_plane hCs_not_l
        rw [hC'sc_eq_Cs]; exact hCs_not_m
      · exact dilation_ext_not_m Γ hCs_atom hc hc_on hc_ne_O hc_ne_U
          hCs_plane hCs_not_m hCs_not_l hCs_ne_O hCs_ne_I hcI
    have hC'sc_not_l : ¬ C'_sc ≤ l := by
      intro h
      by_cases hcI : c = Γ.I
      · subst hcI
        have hC'sc_eq_Cs : C'_sc = C_s := dilation_ext_identity Γ hCs_atom hCs_plane hCs_not_l
        exact hCs_not_l (hC'sc_eq_Cs ▸ h)
      ·

        have hOCs_l : (Γ.O ⊔ C_s) ⊓ l = Γ.O := by
          change (Γ.O ⊔ C_s) ⊓ (Γ.O ⊔ Γ.U) = Γ.O
          rw [sup_comm Γ.O C_s]
          exact inf_comm (Γ.O ⊔ Γ.U) (C_s ⊔ Γ.O) ▸
            line_direction hCs_atom hCs_not_l (show Γ.O ≤ l from le_sup_left)
        have hC'sc_atom' : IsAtom C'_sc := by
          exact dilation_ext_atom Γ hCs_atom hc hc_on hc_ne_O hc_ne_U hCs_plane hCs_not_l hCs_ne_O hCs_ne_I hCs_not_m
        have hC'sc_le_OCs' : C'_sc ≤ Γ.O ⊔ C_s := by
          show dilation_ext Γ c C_s ≤ Γ.O ⊔ C_s; unfold dilation_ext; exact inf_le_left
        have hC'sc_eq_O : C'_sc = Γ.O :=
          (Γ.hO.le_iff.mp ((le_inf hC'sc_le_OCs' h).trans hOCs_l.le)).resolve_left hC'sc_atom'.1

        have hC'sc_on_cdir : C'_sc ≤ c ⊔ (Γ.I ⊔ C_s) ⊓ m := by
          show dilation_ext Γ c C_s ≤ c ⊔ (Γ.I ⊔ C_s) ⊓ m; unfold dilation_ext; exact inf_le_right
        have hO_le_cdir : Γ.O ≤ c ⊔ (Γ.I ⊔ C_s) ⊓ m := hC'sc_eq_O.symm ▸ hC'sc_on_cdir

        have hI_ne_Cs : Γ.I ≠ C_s := Ne.symm hCs_ne_I
        have hICs_dir_atom : IsAtom ((Γ.I ⊔ C_s) ⊓ m) :=
          line_meets_m_at_atom Γ.hI hCs_atom hI_ne_Cs
            (sup_le (Γ.hI_on.trans le_sup_left) hCs_plane) hm_le_π Γ.m_covBy_π Γ.hI_not_m
        have hICs_dir_not_l : ¬ (Γ.I ⊔ C_s) ⊓ m ≤ l := by
          intro hle

          have hICs_dir_eq_U : (Γ.I ⊔ C_s) ⊓ m = Γ.U :=
            (Γ.hU.le_iff.mp (le_inf hle inf_le_right |>.trans hlm_eq_U.le)).resolve_left hICs_dir_atom.1
          have hU_le_ICs : Γ.U ≤ Γ.I ⊔ C_s := hICs_dir_eq_U ▸ inf_le_left
          have hICs_l : (Γ.I ⊔ C_s) ⊓ l = Γ.I := by
            rw [sup_comm Γ.I C_s]; exact inf_comm l (C_s ⊔ Γ.I) ▸ line_direction hCs_atom hCs_not_l Γ.hI_on
          have hU_le_I : Γ.U ≤ Γ.I := le_inf hU_le_ICs (show Γ.U ≤ l from le_sup_right) |>.trans hICs_l.le
          exact Γ.hUI.symm ((Γ.hI.le_iff.mp hU_le_I).resolve_left Γ.hU.1).symm
        have hcdir_l : (c ⊔ (Γ.I ⊔ C_s) ⊓ m) ⊓ l = c := by
          rw [sup_comm c ((Γ.I ⊔ C_s) ⊓ m)]
          exact line_direction hICs_dir_atom hICs_dir_not_l hc_on
        exact hc_ne_O ((hc.le_iff.mp (le_inf hO_le_cdir (show Γ.O ≤ l from le_sup_left)
          |>.trans hcdir_l.le)).resolve_left Γ.hO.1).symm

    have hC'sc_le_OCs : C'_sc ≤ Γ.O ⊔ C_s := by
      show dilation_ext Γ c C_s ≤ Γ.O ⊔ C_s; unfold dilation_ext; exact inf_le_left

    have hC'sc_le_σU : C'_sc ≤ σ ⊔ Γ.U := h_mki_s ▸ inf_le_left

    have hC'sc_le_scE : C'_sc ≤ sc ⊔ Γ.E := h_mki_s ▸ inf_le_right

    have hCb_ne_O : C_b ≠ Γ.O := fun h => hCb_not_l (h ▸ le_sup_left)
    have hCb_ne_I : C_b ≠ Γ.I := fun h => hCb_not_l (h ▸ Γ.hI_on)
    have hCb_ne_U : C_b ≠ Γ.U := fun h => hCb_not_l (h ▸ le_sup_right)
    have hCb_not_m : ¬ C_b ≤ m := by
      intro h
      have hb_not_m : ¬ b ≤ m := fun hm => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on hm)
      have hCb_le_bE : C_b ≤ b ⊔ Γ.E := inf_le_right
      have hbE_dir : (b ⊔ Γ.E) ⊓ m = Γ.E := line_direction hb hb_not_m Γ.hE_on_m
      have hCb_eq_E : C_b = Γ.E :=
        (Γ.hE_atom.le_iff.mp (le_inf hCb_le_bE h |>.trans hbE_dir.le)).resolve_left hCb_atom.1
      have hE_le_q : Γ.E ≤ q := hCb_eq_E ▸ hCb_on_q
      exact Γ.hEU ((Γ.hU.le_iff.mp (le_inf hE_le_q Γ.hE_on_m |>.trans hqm_eq_U.le)).resolve_left Γ.hE_atom.1)

    have hC'bc_atom : IsAtom C'_bc :=
      dilation_ext_atom Γ hCb_atom hc hc_on hc_ne_O hc_ne_U hCb_plane hCb_not_l hCb_ne_O hCb_ne_I hCb_not_m

    have hC'bc_le_OCb : C'_bc ≤ Γ.O ⊔ C_b := by
      show dilation_ext Γ c C_b ≤ Γ.O ⊔ C_b; unfold dilation_ext; exact inf_le_left

    have hC'bc_le_σU : C'_bc ≤ σ ⊔ Γ.U := h_mki_b ▸ inf_le_left

    have hC'bc_le_bcE : C'_bc ≤ bc ⊔ Γ.E := h_mki_b ▸ inf_le_right

    have hd_a : (a ⊔ Γ.C) ⊓ m = (σ ⊔ ac) ⊓ m := by

      set d_a := (a ⊔ Γ.C) ⊓ m with hda_def

      have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
      have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
      have haC_le_π : a ⊔ Γ.C ≤ π := sup_le (ha_on.trans le_sup_left) Γ.hC_plane
      have hda_atom : IsAtom d_a :=
        line_meets_m_at_atom ha Γ.hC ha_ne_C haC_le_π hm_le_π (show m ⋖ π from Γ.m_covBy_π) ha_not_m

      have hac_le_σ_da : ac ≤ σ ⊔ d_a := by

        have hσ_eq : σ = (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) := dilation_ext_C Γ c hc hc_on hc_ne_O hc_ne_U
        show coord_mul Γ a c ≤ σ ⊔ d_a
        show ((Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ Γ.U) ≤ σ ⊔ d_a
        rw [hσ_eq]
        exact le_trans inf_le_left (le_refl _)

      have hσ_ne_da : σ ≠ d_a := fun h => hσ_not_m (h ▸ inf_le_right)
      have hσ_ne_ac : σ ≠ ac := fun h => hσ_not_l (h ▸ hac_on)
      have hσ_lt_σac : σ < σ ⊔ ac := lt_of_le_of_ne le_sup_left
        (fun h => hσ_ne_ac ((hσ_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hac_atom.1).symm)
      have hσac_le_σda : σ ⊔ ac ≤ σ ⊔ d_a := sup_le le_sup_left hac_le_σ_da
      have hσac_eq_σda : σ ⊔ ac = σ ⊔ d_a :=
        ((atom_covBy_join hσ_atom hda_atom hσ_ne_da).eq_or_eq hσ_lt_σac.le hσac_le_σda).resolve_left
          (ne_of_gt hσ_lt_σac)

      rw [hσac_eq_σda]

      exact (line_direction hσ_atom hσ_not_m (show d_a ≤ m from inf_le_right)).symm

    have haxis1_on_m : (Γ.C ⊔ a) ⊓ (σ ⊔ ac) ≤ m := by

      set d_a := (a ⊔ Γ.C) ⊓ m
      have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
      have ha_not_m' : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
      have haC_le_π' : a ⊔ Γ.C ≤ π := sup_le (ha_on.trans le_sup_left) Γ.hC_plane
      have hda_atom : IsAtom d_a :=
        line_meets_m_at_atom ha Γ.hC ha_ne_C haC_le_π' hm_le_π (show m ⋖ π from Γ.m_covBy_π) ha_not_m'
      have hda_le_Ca : d_a ≤ Γ.C ⊔ a := sup_comm a Γ.C ▸ inf_le_left
      have hda_le_σac : d_a ≤ σ ⊔ ac := hd_a.symm ▸ inf_le_left
      have hda_le_meet : d_a ≤ (Γ.C ⊔ a) ⊓ (σ ⊔ ac) := le_inf hda_le_Ca hda_le_σac

      have hmeet_pos : ⊥ < (Γ.C ⊔ a) ⊓ (σ ⊔ ac) := lt_of_lt_of_le hda_atom.bot_lt hda_le_meet
      have hmeet_lt : (Γ.C ⊔ a) ⊓ (σ ⊔ ac) < Γ.C ⊔ a := by
        apply lt_of_le_of_ne inf_le_left; intro h

        have hCa_le : Γ.C ⊔ a ≤ σ ⊔ ac := h ▸ inf_le_right

        have hac_not_OC : ¬ ac ≤ Γ.O ⊔ Γ.C := by
          intro hle

          have hOCl : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
            rw [sup_comm Γ.O Γ.C, show l = Γ.O ⊔ Γ.U from rfl]
            exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
              line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
          exact hac_ne_O ((Γ.hO.le_iff.mp ((le_inf hle hac_on).trans hOCl.le)).resolve_left hac_atom.1)

        have hσac_OC : (σ ⊔ ac) ⊓ (Γ.O ⊔ Γ.C) = σ := by
          rw [sup_inf_assoc_of_le ac hσ_on_OC]
          have : ac ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
            (hac_atom.le_iff.mp inf_le_left).resolve_right (fun hh => hac_not_OC (hh ▸ inf_le_right))
          rw [this, sup_bot_eq]
        have hC_le_both : Γ.C ≤ (σ ⊔ ac) ⊓ (Γ.O ⊔ Γ.C) :=
          le_inf (le_sup_left.trans hCa_le) le_sup_right
        have hC_le_σ : Γ.C ≤ σ := hσac_OC ▸ hC_le_both
        exact hCσ ((hσ_atom.le_iff.mp hC_le_σ).resolve_left Γ.hC.1)
      have hmeet_atom : IsAtom ((Γ.C ⊔ a) ⊓ (σ ⊔ ac)) :=
        line_height_two Γ.hC ha (Ne.symm ha_ne_C) hmeet_pos hmeet_lt
      exact (hmeet_atom.le_iff.mp hda_le_meet).resolve_left hda_atom.1 ▸ inf_le_right

    have haxis2_on_m : (Γ.C ⊔ C_s) ⊓ (σ ⊔ C'_sc) ≤ m := by

      have hCCs_eq_q : Γ.C ⊔ C_s = q := by
        rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C]
        have hCs_ne_C : C_s ≠ Γ.C := by
          intro hCsC

          have hs_not_m : ¬ s ≤ m := fun hm => hs_ne_U (Γ.atom_on_both_eq_U hs_atom hs_on hm)
          have hs_ne_C : s ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hs_on)
          have hs_ne_E : s ≠ Γ.E := fun h => hs_ne_U (Γ.atom_on_both_eq_U hs_atom hs_on (h ▸ Γ.hE_on_m))
          have hC_le_sE : Γ.C ≤ s ⊔ Γ.E := hCsC ▸ (inf_le_right : C_s ≤ s ⊔ Γ.E)
          have hs_lt_sC : s < s ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h' => hs_ne_C ((hs_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hC.1).symm)
          have hsC_eq_sE : s ⊔ Γ.C = s ⊔ Γ.E :=
            ((atom_covBy_join hs_atom Γ.hE_atom hs_ne_E).eq_or_eq hs_lt_sC.le
              (sup_le le_sup_left hC_le_sE)).resolve_left (ne_of_gt hs_lt_sC)
          have hE_le_sC : Γ.E ≤ s ⊔ Γ.C := le_sup_right.trans hsC_eq_sE.symm.le
          have hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C := inf_le_left
          have hO_not_sC : ¬ Γ.O ≤ s ⊔ Γ.C := by
            intro hle
            have hl_le : l ≤ s ⊔ Γ.C := hOs_eq_l ▸ (sup_le hle le_sup_left : Γ.O ⊔ s ≤ s ⊔ Γ.C)
            exact Γ.hC_not_l (le_sup_right.trans
              (((atom_covBy_join hs_atom Γ.hC hs_ne_C).eq_or_eq hs_on hl_le).resolve_left
                (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hs_atom hs_on).lt)).symm.le)
          have hmod := modular_intersection Γ.hC hs_atom Γ.hO hs_ne_C.symm (Ne.symm (fun h => Γ.hC_not_l (h ▸ le_sup_left))) hs_ne_O
            (show ¬ Γ.O ≤ Γ.C ⊔ s from sup_comm s Γ.C ▸ hO_not_sC)
          have hE_le_C : Γ.E ≤ Γ.C :=
            (le_inf (sup_comm s Γ.C ▸ hE_le_sC) (sup_comm Γ.O Γ.C ▸ hE_le_OC)).trans hmod.le
          exact (fun hEC : Γ.E ≠ Γ.C => hEC ((Γ.hC.le_iff.mp hE_le_C).resolve_left Γ.hE_atom.1))
            (fun h' => Γ.hC_not_m (h' ▸ Γ.hE_on_m))
        have hC_lt : Γ.C < Γ.C ⊔ C_s := lt_of_le_of_ne le_sup_left
          (fun h => hCs_ne_C (((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hCs_atom.1)))
        have hCs_on_q' : C_s ≤ Γ.C ⊔ Γ.U := by rw [sup_comm]; exact hCs_on_q
        exact ((atom_covBy_join Γ.hC Γ.hU (Ne.symm (fun h => Γ.hC_not_l (h ▸ le_sup_right)))).eq_or_eq
          hC_lt.le (sup_le le_sup_left hCs_on_q')).resolve_left (ne_of_gt hC_lt)

      have hCCs_le_q : Γ.C ⊔ C_s ≤ q := hCCs_eq_q.le
      have hσC'sc_le_σU : σ ⊔ C'_sc ≤ σ ⊔ Γ.U := sup_le le_sup_left hC'sc_le_σU

      have hU_le_q : Γ.U ≤ q := show Γ.U ≤ Γ.U ⊔ Γ.C from le_sup_left
      have hσ_ne_U : σ ≠ Γ.U := fun h => hσ_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
      have hU_le_σU : Γ.U ≤ σ ⊔ Γ.U := le_sup_right

      have hσ_not_q : ¬ σ ≤ q := by
        intro hσq

        have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
          intro hle
          have hOCl : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
            rw [sup_comm Γ.O Γ.C, show l = Γ.O ⊔ Γ.U from rfl]
            exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
              line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
          have hU_le_O : Γ.U ≤ Γ.O := (le_inf hle (show Γ.U ≤ l from le_sup_right)).trans hOCl.le
          exact Γ.hOU ((Γ.hO.le_iff.mp hU_le_O).resolve_left Γ.hU.1).symm
        have hq_OC : q ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
          rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C, sup_inf_assoc_of_le Γ.U (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)]
          have : Γ.U ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
            (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun hh => hU_not_OC (hh ▸ inf_le_right))
          rw [this, sup_bot_eq]
        have hσ_le_C : σ ≤ Γ.C := (le_inf hσq hσ_on_OC).trans hq_OC.le
        exact hCσ ((Γ.hC.le_iff.mp hσ_le_C).resolve_left hσ_atom.1).symm
      have hqσU_eq_U : q ⊓ (σ ⊔ Γ.U) = Γ.U := by
        rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm σ Γ.U]
        exact modular_intersection Γ.hU Γ.hC hσ_atom hUC hσ_ne_U.symm hCσ hσ_not_q
      calc (Γ.C ⊔ C_s) ⊓ (σ ⊔ C'_sc)
          ≤ q ⊓ (σ ⊔ Γ.U) := le_inf (hCCs_eq_q ▸ inf_le_left) (inf_le_right.trans hσC'sc_le_σU)
        _ = Γ.U := hqσU_eq_U
        _ ≤ m := le_sup_left

    have haxis3_on_m : (a ⊔ C_s) ⊓ (ac ⊔ C'_sc) ≤ m := by

      have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
      have ha_ne_Cs : a ≠ C_s := fun h => hCs_not_l (h ▸ ha_on)
      have hσ_ne_ac : σ ≠ ac := fun h => hσ_not_l (h ▸ hac_on)
      have hac_ne_C'sc : ac ≠ C'_sc := fun h => hC'sc_not_l (h ▸ hac_on)

      have hσ_ne_C'sc : σ ≠ C'_sc := by
        intro heq

        have hσ_le_OCs : σ ≤ Γ.O ⊔ C_s := heq ▸ hC'sc_le_OCs

        have hC_not_OCs : ¬ Γ.C ≤ Γ.O ⊔ C_s := by
          intro hCle

          have hO_ne_Cs : Γ.O ≠ C_s := fun h => hCs_not_l (h ▸ le_sup_left)
          have hO_ne_C' : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
          have hO_lt : Γ.O < Γ.O ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => hO_ne_C' ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm)
          have hOC_le : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ C_s := sup_le le_sup_left hCle
          have hOC_eq : Γ.O ⊔ Γ.C = Γ.O ⊔ C_s :=
            ((atom_covBy_join Γ.hO hCs_atom hO_ne_Cs).eq_or_eq hO_lt.le hOC_le).resolve_left (ne_of_gt hO_lt)

          have hCs_le_OC : C_s ≤ Γ.O ⊔ Γ.C := le_sup_right.trans hOC_eq.symm.le
          have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
            intro hle'
            have hOCl : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
              rw [sup_comm Γ.O Γ.C, show l = Γ.O ⊔ Γ.U from rfl]
              exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
                line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
            exact Γ.hOU ((Γ.hO.le_iff.mp (le_inf hle' (show Γ.U ≤ l from le_sup_right) |>.trans hOCl.le)).resolve_left Γ.hU.1).symm
          have hq_OC : q ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
            rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C, sup_inf_assoc_of_le Γ.U (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)]
            have : Γ.U ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
              (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun hh => hU_not_OC (hh ▸ inf_le_right))
            rw [this, sup_bot_eq]
          have hCs_eq_C : C_s = Γ.C :=
            (Γ.hC.le_iff.mp (le_inf hCs_on_q hCs_le_OC |>.trans hq_OC.le)).resolve_left hCs_atom.1

          have hs_not_m : ¬ s ≤ m := fun hm => hs_ne_U (Γ.atom_on_both_eq_U hs_atom hs_on hm)
          have hs_ne_C : s ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hs_on)
          have hs_ne_E : s ≠ Γ.E := fun h => hs_ne_U (Γ.atom_on_both_eq_U hs_atom hs_on (h ▸ Γ.hE_on_m))
          have hC_le_sE : Γ.C ≤ s ⊔ Γ.E := hCs_eq_C ▸ (inf_le_right : C_s ≤ s ⊔ Γ.E)
          have hs_lt_sC : s < s ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h' => hs_ne_C ((hs_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hC.1).symm)
          have hsC_eq_sE : s ⊔ Γ.C = s ⊔ Γ.E :=
            ((atom_covBy_join hs_atom Γ.hE_atom hs_ne_E).eq_or_eq hs_lt_sC.le
              (sup_le le_sup_left hC_le_sE)).resolve_left (ne_of_gt hs_lt_sC)
          have hE_le_sC : Γ.E ≤ s ⊔ Γ.C := le_sup_right.trans hsC_eq_sE.symm.le
          have hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C := inf_le_left
          have hO_not_sC : ¬ Γ.O ≤ s ⊔ Γ.C := by
            intro hle'
            have hl_le : l ≤ s ⊔ Γ.C := hOs_eq_l ▸ (sup_le hle' le_sup_left : Γ.O ⊔ s ≤ s ⊔ Γ.C)
            exact Γ.hC_not_l (le_sup_right.trans
              (((atom_covBy_join hs_atom Γ.hC hs_ne_C).eq_or_eq hs_on hl_le).resolve_left
                (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hs_atom hs_on).lt)).symm.le)
          have hmod := modular_intersection Γ.hC hs_atom Γ.hO hs_ne_C.symm (Ne.symm (fun h => Γ.hC_not_l (h ▸ le_sup_left))) hs_ne_O
            (show ¬ Γ.O ≤ Γ.C ⊔ s from sup_comm s Γ.C ▸ hO_not_sC)
          have hE_le_C : Γ.E ≤ Γ.C :=
            (le_inf (sup_comm s Γ.C ▸ hE_le_sC) (sup_comm Γ.O Γ.C ▸ hE_le_OC)).trans hmod.le
          exact (fun hEC : Γ.E ≠ Γ.C => hEC ((Γ.hC.le_iff.mp hE_le_C).resolve_left Γ.hE_atom.1))
            (fun h' => Γ.hC_not_m (h' ▸ Γ.hE_on_m))

        have hCs_not_OC : ¬ C_s ≤ Γ.O ⊔ Γ.C := by
          intro hle'
          have hO_ne_Cs'' : Γ.O ≠ C_s := fun h => hCs_not_l (h ▸ le_sup_left)
          have hO_lt' : Γ.O < Γ.O ⊔ C_s := lt_of_le_of_ne le_sup_left
            (fun h => hO_ne_Cs'' ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hCs_atom.1).symm)
          have hOCs_eq : Γ.O ⊔ C_s = Γ.O ⊔ Γ.C :=
            ((atom_covBy_join Γ.hO Γ.hC (fun h => Γ.hC_not_l (h ▸ le_sup_left))).eq_or_eq hO_lt'.le
              (sup_le le_sup_left hle')).resolve_left (ne_of_gt hO_lt')
          exact hC_not_OCs (le_sup_right.trans hOCs_eq.symm.le)

        have hC_ne_Cs' : Γ.C ≠ C_s := fun h => hCs_not_OC (h ▸ le_sup_right)

        have hO_ne_Cs' : Γ.O ≠ C_s := fun h => hCs_not_l (h ▸ le_sup_left)
        have hO_ne_C' : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
        have hOC_OCs : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ C_s) = Γ.O :=
          modular_intersection Γ.hO Γ.hC hCs_atom hO_ne_C' hO_ne_Cs' hC_ne_Cs' hCs_not_OC

        have hσ_eq_O : σ = Γ.O :=
          (Γ.hO.le_iff.mp (le_inf hσ_on_OC hσ_le_OCs |>.trans hOC_OCs.le)).resolve_left hσ_atom.1
        exact hσ_not_l (hσ_eq_O ▸ (show Γ.O ≤ l from le_sup_left))

      have hC_ne_Cs : Γ.C ≠ C_s := by
        intro heq
        have hC_le_sE : Γ.C ≤ s ⊔ Γ.E := heq ▸ (inf_le_right : C_s ≤ s ⊔ Γ.E)
        have hs_not_OC : ¬ s ≤ Γ.O ⊔ Γ.C := by
          intro hle
          have : (Γ.C ⊔ Γ.O) ⊓ l = Γ.O :=
            line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
          exact hs_ne_O ((Γ.hO.le_iff.mp
            (le_inf (sup_comm Γ.O Γ.C ▸ hle) hs_on |>.trans this.le)).resolve_left hs_atom.1)
        have hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C := by
          show (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.C; exact inf_le_left
        have : (Γ.E ⊔ s) ⊓ (Γ.O ⊔ Γ.C) = Γ.E ⊔ s ⊓ (Γ.O ⊔ Γ.C) :=
          sup_inf_assoc_of_le s hE_le_OC
        have hs_inf : s ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
          (hs_atom.le_iff.mp inf_le_left).resolve_right (fun hh => hs_not_OC (hh ▸ inf_le_right))
        rw [hs_inf, sup_bot_eq] at this
        have hC_le_E : Γ.C ≤ Γ.E :=
          (le_inf (sup_comm s Γ.E ▸ hC_le_sE) (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)).trans this.le
        have hCeqE := (Γ.hE_atom.le_iff.mp hC_le_E).resolve_left Γ.hC.1
        exact Γ.hC_not_m (hCeqE ▸ Γ.hE_on_m)
      have hCa_ne_σac : Γ.C ⊔ a ≠ σ ⊔ ac := by
        intro heq
        have ha_not_OC : ¬ a ≤ Γ.O ⊔ Γ.C := by
          intro hle
          have : (Γ.C ⊔ Γ.O) ⊓ l = Γ.O :=
            line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
          exact ha_ne_O ((Γ.hO.le_iff.mp (le_inf (sup_comm Γ.O Γ.C ▸ hle) ha_on |>.trans this.le)).resolve_left ha.1)
        have h1 : (Γ.C ⊔ a) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
          rw [sup_inf_assoc_of_le a (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)]
          have : a ⊓ (Γ.O ⊔ Γ.C) = ⊥ := (ha.le_iff.mp inf_le_left).resolve_right
            (fun hh => ha_not_OC (hh ▸ inf_le_right))
          rw [this, sup_bot_eq]
        have hac_not_OC : ¬ ac ≤ Γ.O ⊔ Γ.C := by
          intro hle
          have : (Γ.C ⊔ Γ.O) ⊓ l = Γ.O :=
            line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
          exact hac_ne_O ((Γ.hO.le_iff.mp (le_inf (sup_comm Γ.O Γ.C ▸ hle) hac_on |>.trans this.le)).resolve_left hac_atom.1)
        have h2 : (σ ⊔ ac) ⊓ (Γ.O ⊔ Γ.C) = σ := by
          rw [sup_inf_assoc_of_le ac hσ_on_OC]
          have : ac ⊓ (Γ.O ⊔ Γ.C) = ⊥ := (hac_atom.le_iff.mp inf_le_left).resolve_right
            (fun hh => hac_not_OC (hh ▸ inf_le_right))
          rw [this, sup_bot_eq]
        have : Γ.C = σ := by
          have := congr_arg (· ⊓ (Γ.O ⊔ Γ.C)) heq; simp only [h1, h2] at this; exact this
        exact hCσ this
      have hCCs_ne_σC'sc : Γ.C ⊔ C_s ≠ σ ⊔ C'_sc := by
        intro heq

        have hCCs_eq_q : Γ.C ⊔ C_s = q := by
          rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C]
          have hC_lt : Γ.C < Γ.C ⊔ C_s := lt_of_le_of_ne le_sup_left
            (fun h => hC_ne_Cs ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hCs_atom.1).symm)
          have hCs_on_q' : C_s ≤ Γ.C ⊔ Γ.U := by rw [sup_comm]; exact hCs_on_q
          exact ((atom_covBy_join Γ.hC Γ.hU (Ne.symm (fun h => Γ.hC_not_l (h ▸ le_sup_right)))).eq_or_eq
            hC_lt.le (sup_le le_sup_left hCs_on_q')).resolve_left (ne_of_gt hC_lt)

        have hσ_le_q : σ ≤ q := le_sup_left.trans (heq.symm.le.trans hCCs_eq_q.le)

        have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
          intro hle'
          have hOCl : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
            rw [sup_comm Γ.O Γ.C, show l = Γ.O ⊔ Γ.U from rfl]
            exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
              line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
          exact Γ.hOU ((Γ.hO.le_iff.mp (le_inf hle' (show Γ.U ≤ l from le_sup_right) |>.trans hOCl.le)).resolve_left Γ.hU.1).symm
        have hq_OC : q ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
          rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C, sup_inf_assoc_of_le Γ.U (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)]
          have : Γ.U ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
            (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun hh => hU_not_OC (hh ▸ inf_le_right))
          rw [this, sup_bot_eq]
        have hσ_le_C : σ ≤ Γ.C := (le_inf hσ_le_q hσ_on_OC).trans hq_OC.le
        exact hCσ ((Γ.hC.le_iff.mp hσ_le_C).resolve_left hσ_atom.1).symm

      have ha_not_q : ¬ a ≤ q := fun haq =>
        ha_ne_U ((Γ.hU.le_iff.mp (le_inf ha_on haq |>.trans hlq_eq_U.le)).resolve_left ha.1)
      have ha_ne_ac : a ≠ ac := by
        intro heq
        have hd_a' : (a ⊔ Γ.C) ⊓ m = (σ ⊔ a) ⊓ m := heq ▸ hd_a
        set d := (a ⊔ Γ.C) ⊓ m
        have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
        have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
        have hd_atom : IsAtom d :=
          line_meets_m_at_atom ha Γ.hC ha_ne_C (sup_le (ha_on.trans le_sup_left) Γ.hC_plane)
            hm_le_π Γ.m_covBy_π ha_not_m
        have ha_ne_d : a ≠ d := fun h => ha_not_m (h ▸ inf_le_right)
        have hd_le_σa : d ≤ σ ⊔ a := hd_a' ▸ inf_le_left
        have had_le_Ca : a ⊔ d ≤ Γ.C ⊔ a :=
          sup_le le_sup_right (sup_comm a Γ.C ▸ inf_le_left)
        have had_le_σa : a ⊔ d ≤ σ ⊔ a := sup_le le_sup_right hd_le_σa
        have ha_lt : a < a ⊔ d := lt_of_le_of_ne le_sup_left
          (fun h => ha_ne_d ((ha.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hd_atom.1).symm)
        have had_eq_Ca : a ⊔ d = Γ.C ⊔ a :=
          ((by rw [sup_comm]; exact atom_covBy_join ha Γ.hC ha_ne_C : a ⋖ Γ.C ⊔ a).eq_or_eq ha_lt.le had_le_Ca).resolve_left (ne_of_gt ha_lt)
        have hσ_ne_a : σ ≠ a := fun h => hσ_not_l (h ▸ ha_on)
        have had_eq_σa : a ⊔ d = σ ⊔ a :=
          ((by rw [sup_comm]; exact atom_covBy_join ha hσ_atom (Ne.symm hσ_ne_a) : a ⋖ σ ⊔ a).eq_or_eq ha_lt.le had_le_σa).resolve_left (ne_of_gt ha_lt)
        have hσ_le_Ca : σ ≤ Γ.C ⊔ a := le_sup_left.trans (had_eq_Ca.symm.trans had_eq_σa).symm.le
        have ha_not_OC : ¬ a ≤ Γ.O ⊔ Γ.C := by
          intro hle
          have : (Γ.C ⊔ Γ.O) ⊓ l = Γ.O :=
            line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
          exact ha_ne_O ((Γ.hO.le_iff.mp (le_inf (sup_comm Γ.O Γ.C ▸ hle) ha_on |>.trans this.le)).resolve_left ha.1)
        have : (Γ.C ⊔ a) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
          rw [sup_inf_assoc_of_le a (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)]
          have : a ⊓ (Γ.O ⊔ Γ.C) = ⊥ := (ha.le_iff.mp inf_le_left).resolve_right
            (fun hh => ha_not_OC (hh ▸ inf_le_right))
          rw [this, sup_bot_eq]
        have hσ_le_C : σ ≤ Γ.C := (le_inf hσ_le_Ca hσ_on_OC).trans this.le
        exact hCσ ((Γ.hC.le_iff.mp hσ_le_C).resolve_left hσ_atom.1).symm
      have haCs_ne_acC'sc : a ⊔ C_s ≠ ac ⊔ C'_sc := by
        intro heq
        have h1 : (C_s ⊔ a) ⊓ l = a := line_direction hCs_atom hCs_not_l ha_on
        have h2 : (C'_sc ⊔ ac) ⊓ l = ac := line_direction hC'sc_atom hC'sc_not_l hac_on
        have : a = ac := by
          have := congr_arg (· ⊓ l) (show C_s ⊔ a = C'_sc ⊔ ac from by rw [sup_comm, heq, sup_comm])
          simp only [h1, h2] at this; exact this
        exact ha_ne_ac this
      have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)

      have hV_not_l : ¬ Γ.V ≤ l := fun hle =>
        hUV ((Γ.hU.le_iff.mp (le_inf hle (show Γ.V ≤ m from le_sup_right) |>.trans hlm_eq_U.le)).resolve_left Γ.hV.1).symm

      have hl_cov_π : l ⋖ π := by
        rw [show l = Γ.O ⊔ Γ.U from rfl, show π = Γ.O ⊔ Γ.U ⊔ Γ.V from rfl]
        exact line_covBy_plane Γ.hO Γ.hU Γ.hV Γ.hOU
          (fun h => Γ.hV_off (h ▸ (show Γ.O ≤ l from le_sup_left))) hUV hV_not_l

      have hCs_not_Ca : ¬ C_s ≤ Γ.C ⊔ a := by
        intro hle
        have : (Γ.C ⊔ a) ⊓ q = Γ.C := by
          change (Γ.C ⊔ a) ⊓ (Γ.U ⊔ Γ.C) = Γ.C
          rw [sup_inf_assoc_of_le a (le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C)]
          have : a ⊓ (Γ.U ⊔ Γ.C) = ⊥ := (ha.le_iff.mp inf_le_left).resolve_right
            (fun hh => ha_not_q (hh ▸ inf_le_right))
          rw [this, sup_bot_eq]
        exact hC_ne_Cs ((Γ.hC.le_iff.mp (le_inf hle hCs_on_q |>.trans this.le)).resolve_left hCs_atom.1).symm

      have haU_eq_l : a ⊔ Γ.U = l := by
        have h_cov := line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on
        have ha_lt : a < a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
          (fun h => ha_ne_U ((ha.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1).symm)
        exact (h_cov.eq_or_eq ha_lt.le (sup_le ha_on (show Γ.U ≤ l from le_sup_right))).resolve_left
          (ne_of_gt ha_lt)

      have hCl_eq_π : Γ.C ⊔ l = π := by
        have hl_lt : l < Γ.C ⊔ l := lt_of_le_of_ne le_sup_right
          (fun h => Γ.hC_not_l (le_sup_left.trans h.symm.le))
        exact (hl_cov_π.eq_or_eq hl_lt.le (sup_le Γ.hC_plane hl_cov_π.le)).resolve_left (ne_of_gt hl_lt)
      have hπA : Γ.C ⊔ a ⊔ C_s = π := by

        have hCa_cov_π : Γ.C ⊔ a ⋖ π := by
          have hCaU : Γ.C ⊔ a ⊔ Γ.U = π := by rw [sup_assoc, haU_eq_l]; exact hCl_eq_π
          have hU_not_Ca : ¬ Γ.U ≤ Γ.C ⊔ a := by
            intro hle
            have : (Γ.C ⊔ a) ⊓ l = a := line_direction Γ.hC Γ.hC_not_l ha_on
            exact ha_ne_U ((ha.le_iff.mp (le_inf hle (show Γ.U ≤ l from le_sup_right) |>.trans this.le)).resolve_left Γ.hU.1).symm
          rw [← hCaU]; exact line_covBy_plane Γ.hC ha Γ.hU (Ne.symm ha_ne_C) (Ne.symm hUC) ha_ne_U hU_not_Ca
        exact (hCa_cov_π.eq_or_eq (lt_of_le_of_ne le_sup_left
          (fun h => hCs_not_Ca (le_sup_right.trans h.symm.le))).le
          (sup_le (sup_le Γ.hC_plane (ha_on.trans le_sup_left)) hCs_plane)).resolve_left
          (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => hCs_not_Ca (le_sup_right.trans h.symm.le))))
      have hπB : σ ⊔ ac ⊔ C'_sc = π := by

        have hC'sc_not_σac : ¬ C'_sc ≤ σ ⊔ ac := by
          intro hle
          have hac_not_σU : ¬ ac ≤ σ ⊔ Γ.U := by
            intro hle'
            have : (σ ⊔ Γ.U) ⊓ l = Γ.U := line_direction hσ_atom hσ_not_l (show Γ.U ≤ l from le_sup_right)
            exact hac_ne_U ((Γ.hU.le_iff.mp (le_inf hle' hac_on |>.trans this.le)).resolve_left hac_atom.1)
          have : (σ ⊔ ac) ⊓ (σ ⊔ Γ.U) = σ := by
            rw [sup_inf_assoc_of_le ac (le_sup_left : σ ≤ σ ⊔ Γ.U)]
            have : ac ⊓ (σ ⊔ Γ.U) = ⊥ := (hac_atom.le_iff.mp inf_le_left).resolve_right
              (fun hh => hac_not_σU (hh ▸ inf_le_right))
            rw [this, sup_bot_eq]
          exact hσ_ne_C'sc ((hσ_atom.le_iff.mp (le_inf hle hC'sc_le_σU |>.trans this.le)).resolve_left hC'sc_atom.1).symm

        have hσac_cov_π : σ ⊔ ac ⋖ π := by
          have hacU_eq_l : ac ⊔ Γ.U = l := by
            have h_cov := line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hac_atom hac_on
            have hac_lt : ac < ac ⊔ Γ.U := lt_of_le_of_ne le_sup_left
              (fun h => hac_ne_U ((hac_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1).symm)
            exact (h_cov.eq_or_eq hac_lt.le (sup_le hac_on (show Γ.U ≤ l from le_sup_right))).resolve_left (ne_of_gt hac_lt)
          have hσl_eq : σ ⊔ l = π := by
            have hl_lt : l < σ ⊔ l := lt_of_le_of_ne le_sup_right
              (fun h => hσ_not_l (le_sup_left.trans h.symm.le))
            exact (hl_cov_π.eq_or_eq hl_lt.le (sup_le hσ_plane hl_cov_π.le)).resolve_left (ne_of_gt hl_lt)
          have hσacU : σ ⊔ ac ⊔ Γ.U = π := by rw [sup_assoc, hacU_eq_l]; exact hσl_eq
          have hU_not_σac : ¬ Γ.U ≤ σ ⊔ ac := by
            intro hle
            have : (σ ⊔ ac) ⊓ l = ac := line_direction hσ_atom hσ_not_l hac_on
            exact hac_ne_U ((hac_atom.le_iff.mp (le_inf hle (show Γ.U ≤ l from le_sup_right) |>.trans this.le)).resolve_left Γ.hU.1).symm
          rw [← hσacU]; exact line_covBy_plane hσ_atom hac_atom Γ.hU hσ_ne_ac
            (fun h => hσ_not_m (h ▸ (show Γ.U ≤ m from le_sup_left))) hac_ne_U hU_not_σac
        exact (hσac_cov_π.eq_or_eq (lt_of_le_of_ne le_sup_left
          (fun h => hC'sc_not_σac (le_sup_right.trans h.symm.le))).le
          (sup_le (sup_le hσ_plane (hac_on.trans le_sup_left)) hC'sc_plane)).resolve_left
          (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => hC'sc_not_σac (le_sup_right.trans h.symm.le))))
      have hCs_ne_C'sc : C_s ≠ C'_sc := by
        intro h
        have hCs_le_σU : C_s ≤ σ ⊔ Γ.U := h ▸ hC'sc_le_σU

        have hσ_not_q' : ¬ σ ≤ q := by
          intro hσq
          have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
            intro hle'
            have hOCl' : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
              rw [sup_comm Γ.O Γ.C, show l = Γ.O ⊔ Γ.U from rfl]
              exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
                line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
            exact Γ.hOU ((Γ.hO.le_iff.mp (le_inf hle' (show Γ.U ≤ l from le_sup_right) |>.trans hOCl'.le)).resolve_left Γ.hU.1).symm
          have hq_OC : q ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
            rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C, sup_inf_assoc_of_le Γ.U (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)]
            have : Γ.U ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
              (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun hh => hU_not_OC (hh ▸ inf_le_right))
            rw [this, sup_bot_eq]
          exact hCσ ((Γ.hC.le_iff.mp (le_inf hσq hσ_on_OC |>.trans hq_OC.le)).resolve_left hσ_atom.1).symm
        have hσ_ne_U' : σ ≠ Γ.U := fun h' => hσ_not_m (h' ▸ le_sup_left)
        have hqσU : q ⊓ (σ ⊔ Γ.U) = Γ.U := by
          rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm σ Γ.U]
          exact modular_intersection Γ.hU Γ.hC hσ_atom hUC hσ_ne_U'.symm hCσ hσ_not_q'
        exact hCs_ne_U ((Γ.hU.le_iff.mp (le_inf hCs_on_q hCs_le_σU |>.trans hqσU.le)).resolve_left hCs_atom.1)
      have hCa_cov : Γ.C ⊔ a ⋖ π := by
        have hCaU : Γ.C ⊔ a ⊔ Γ.U = π := by rw [sup_assoc, haU_eq_l]; exact hCl_eq_π
        have hU_not_Ca : ¬ Γ.U ≤ Γ.C ⊔ a := by
          intro hle
          have : (Γ.C ⊔ a) ⊓ l = a := line_direction Γ.hC Γ.hC_not_l ha_on
          exact ha_ne_U ((ha.le_iff.mp (le_inf hle (show Γ.U ≤ l from le_sup_right) |>.trans this.le)).resolve_left Γ.hU.1).symm
        rw [← hCaU]; exact line_covBy_plane Γ.hC ha Γ.hU (Ne.symm ha_ne_C) (Ne.symm hUC) ha_ne_U hU_not_Ca
      have hCCs_cov : Γ.C ⊔ C_s ⋖ π := by
        have hCCs_eq_q : Γ.C ⊔ C_s = q := by
          rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C]
          have hC_lt : Γ.C < Γ.C ⊔ C_s := lt_of_le_of_ne le_sup_left
            (fun h => hC_ne_Cs ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hCs_atom.1).symm)
          exact ((atom_covBy_join Γ.hC Γ.hU (Ne.symm hUC)).eq_or_eq hC_lt.le
            (sup_le le_sup_left (by rw [sup_comm]; exact hCs_on_q))).resolve_left (ne_of_gt hC_lt)
        rw [hCCs_eq_q]
        have hmq_cov : m ⊓ q ⋖ m := by rw [inf_comm, hqm_eq_U]; exact atom_covBy_join Γ.hU Γ.hV hUV
        have hmq_eq_π : m ⊔ q = π := by
          rw [show q = Γ.U ⊔ Γ.C from rfl]; show m ⊔ (Γ.U ⊔ Γ.C) = π
          rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
          have hm_lt : m < m ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))
          exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hm_le_π Γ.hC_plane)).resolve_left (ne_of_gt hm_lt)
        rw [← hmq_eq_π, sup_comm]
        have := covBy_sup_of_inf_covBy_left hmq_cov
        rwa [sup_comm] at this
      have haCs_cov : a ⊔ C_s ⋖ π := by
        have hC_not_aCs : ¬ Γ.C ≤ a ⊔ C_s := by
          intro hle
          have : (C_s ⊔ a) ⊓ q = C_s := by
            change (C_s ⊔ a) ⊓ (Γ.U ⊔ Γ.C) = C_s
            rw [sup_inf_assoc_of_le a (hCs_on_q : C_s ≤ Γ.U ⊔ Γ.C)]
            have : a ⊓ (Γ.U ⊔ Γ.C) = ⊥ := (ha.le_iff.mp inf_le_left).resolve_right
              (fun hh => ha_not_q (hh ▸ inf_le_right))
            rw [this, sup_bot_eq]
          have hC_le_Cs : Γ.C ≤ C_s :=
            le_inf (sup_comm a C_s ▸ hle) (le_sup_right : Γ.C ≤ q) |>.trans this.le
          exact hC_ne_Cs ((hCs_atom.le_iff.mp hC_le_Cs).resolve_left Γ.hC.1)
        have hπ_eq : π = a ⊔ C_s ⊔ Γ.C := by
          have : Γ.C ⊔ a ⊔ C_s = a ⊔ C_s ⊔ Γ.C := by
            rw [sup_comm Γ.C a, sup_assoc, sup_comm Γ.C C_s, ← sup_assoc]
          rw [hπA.symm, this]
        rw [hπ_eq]; exact line_covBy_plane ha hCs_atom Γ.hC ha_ne_Cs
          ha_ne_C (Ne.symm hC_ne_Cs) hC_not_aCs

      have hac_on_Oa : ac ≤ Γ.O ⊔ a := by
        have hOa_eq_l : Γ.O ⊔ a = l := by
          have hO_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
            (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
          exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
            (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt hO_lt)
        exact hOa_eq_l ▸ hac_on

      obtain ⟨axis, h_axis_le, h_axis_ne, h_pt1, h_pt2, h_pt3⟩ :=
        desargues_planar Γ.hO Γ.hC ha hCs_atom hσ_atom hac_atom hC'sc_atom
          (show Γ.O ≤ π from le_sup_left.trans le_sup_left)
          Γ.hC_plane (ha_on.trans le_sup_left) hCs_plane
          hσ_plane (hac_on.trans le_sup_left) hC'sc_plane
          hσ_on_OC hac_on_Oa hC'sc_le_OCs
          ha_ne_C.symm hC_ne_Cs ha_ne_Cs
          hσ_ne_ac hσ_ne_C'sc hac_ne_C'sc
          hCa_ne_σac hCCs_ne_σC'sc haCs_ne_acC'sc
          hπA hπB
          (fun h => Γ.hC_not_l (h ▸ le_sup_left)) (fun h => ha_ne_O h.symm)
          (fun h => hCs_not_l (h ▸ (show Γ.O ≤ l from le_sup_left)))
          (fun h => hσ_not_l (h ▸ (show Γ.O ≤ l from le_sup_left)))
          (fun h => hac_ne_O h.symm)
          (fun h => hC'sc_not_l (h ▸ (show Γ.O ≤ l from le_sup_left)))
          hCσ ha_ne_ac hCs_ne_C'sc
          R hR hR_not h_irred
          hCa_cov hCCs_cov haCs_cov

      have ha_not_m' : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
      have haC_le_π' : a ⊔ Γ.C ≤ π := sup_le (ha_on.trans le_sup_left) Γ.hC_plane
      have hda_atom : IsAtom ((a ⊔ Γ.C) ⊓ m) :=
        line_meets_m_at_atom ha Γ.hC ha_ne_C haC_le_π' hm_le_π Γ.m_covBy_π ha_not_m'

      have hda_le_axis : (a ⊔ Γ.C) ⊓ m ≤ axis := by
        have h1 : (a ⊔ Γ.C) ⊓ m ≤ Γ.C ⊔ a := (sup_comm a Γ.C).symm ▸ inf_le_left
        have h2 : (a ⊔ Γ.C) ⊓ m ≤ σ ⊔ ac := hd_a ▸ inf_le_left
        exact (le_inf h1 h2).trans h_pt1

      have hU_le_axis : Γ.U ≤ axis := by

        have hCCs_eq_q : Γ.C ⊔ C_s = q := by
          have hCs_le_q' : C_s ≤ Γ.C ⊔ Γ.U := by rw [sup_comm]; exact hCs_on_q
          have hC_lt : Γ.C < Γ.C ⊔ C_s := lt_of_le_of_ne le_sup_left
            (fun h => hC_ne_Cs ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hCs_atom.1).symm)
          rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C]
          exact ((atom_covBy_join Γ.hC Γ.hU (Ne.symm hUC)).eq_or_eq hC_lt.le
            (sup_le le_sup_left hCs_le_q')).resolve_left (ne_of_gt hC_lt)
        have hU_le_CCs : Γ.U ≤ Γ.C ⊔ C_s := hCCs_eq_q ▸ (show Γ.U ≤ q from le_sup_left)
        have hU_le_σC'sc : Γ.U ≤ σ ⊔ C'_sc := by

          have hσ_ne_U' : σ ≠ Γ.U := fun h => hσ_not_m (h ▸ le_sup_left)
          have hσ_lt : σ < σ ⊔ C'_sc := lt_of_le_of_ne le_sup_left
            (fun h => hσ_ne_C'sc ((hσ_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hC'sc_atom.1).symm)
          have hσC'sc_eq : σ ⊔ C'_sc = σ ⊔ Γ.U :=
            ((atom_covBy_join hσ_atom Γ.hU hσ_ne_U').eq_or_eq hσ_lt.le
              (sup_le le_sup_left hC'sc_le_σU)).resolve_left (ne_of_gt hσ_lt)
          exact hσC'sc_eq ▸ le_sup_right
        exact (le_inf hU_le_CCs hU_le_σC'sc).trans h_pt2

      have hda_ne_U : (a ⊔ Γ.C) ⊓ m ≠ Γ.U := by
        intro h
        have haC_l : (a ⊔ Γ.C) ⊓ l = a := by
          rw [sup_comm a Γ.C]; exact inf_comm l (Γ.C ⊔ a) ▸
            line_direction Γ.hC Γ.hC_not_l ha_on
        have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := h.symm ▸ inf_le_left
        have hU_le_a : Γ.U ≤ a := (le_inf hU_le_aC (show Γ.U ≤ l from le_sup_right)).trans haC_l.le
        exact ha_ne_U ((ha.le_iff.mp hU_le_a).resolve_left Γ.hU.1).symm

      have hm_le_axis : m ≤ axis := by
        have hda_U_eq_m : (a ⊔ Γ.C) ⊓ m ⊔ Γ.U = m := by
          have hU_lt : Γ.U < Γ.U ⊔ (a ⊔ Γ.C) ⊓ m := lt_of_le_of_ne le_sup_left
            (fun h => hda_ne_U ((Γ.hU.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hda_atom.1))
          rw [sup_comm]
          exact ((atom_covBy_join Γ.hU Γ.hV hUV).eq_or_eq hU_lt.le
            (sup_le le_sup_left inf_le_right)).resolve_left (ne_of_gt hU_lt)
        exact hda_U_eq_m ▸ sup_le hda_le_axis hU_le_axis

      have haxis_eq_m : axis = m :=
        (Γ.m_covBy_π.eq_or_eq hm_le_axis h_axis_le).resolve_right h_axis_ne
      rw [← haxis_eq_m]; exact h_pt3

    have haCs_eq_aeb : a ⊔ C_s = a ⊔ e_b := by

      have ha_ne_Cs : a ≠ C_s := fun h => hCs_not_l (h ▸ ha_on)
      have ha_ne_eb : a ≠ e_b := by
        intro h; exact (fun hle => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on hle))
          (h ▸ inf_le_right : a ≤ m)
      have ha_lt : a < a ⊔ C_s := lt_of_le_of_ne le_sup_left
        (fun h => ha_ne_Cs ((ha.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hCs_atom.1).symm)
      have h_le : a ⊔ C_s ≤ a ⊔ e_b := sup_le le_sup_left hCs_le_a_eb
      exact ((atom_covBy_join ha heb_atom ha_ne_eb).eq_or_eq ha_lt.le h_le).resolve_left
        (ne_of_gt ha_lt)
    have haCs_dir : (a ⊔ C_s) ⊓ m = e_b := by
      rw [haCs_eq_aeb]
      have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
      exact line_direction ha ha_not_m (inf_le_right : e_b ≤ m)

    have heb_le_acC'sc : e_b ≤ ac ⊔ C'_sc := by

      have hmeet_le_eb : (a ⊔ C_s) ⊓ (ac ⊔ C'_sc) ≤ e_b := by
        have h1 : (a ⊔ C_s) ⊓ (ac ⊔ C'_sc) ≤ a ⊔ C_s := inf_le_left
        have h2 : (a ⊔ C_s) ⊓ (ac ⊔ C'_sc) ≤ m := haxis3_on_m
        calc (a ⊔ C_s) ⊓ (ac ⊔ C'_sc) ≤ (a ⊔ C_s) ⊓ m := le_inf h1 h2
          _ = e_b := haCs_dir

      have hmeet_le_ac_C'sc : (a ⊔ C_s) ⊓ (ac ⊔ C'_sc) ≤ ac ⊔ C'_sc := inf_le_right

      have hmeet_ne_bot : (a ⊔ C_s) ⊓ (ac ⊔ C'_sc) ≠ ⊥ := by

        have ha_ne_Cs : a ≠ C_s := fun h => hCs_not_l (h ▸ ha_on)
        have hO_not_aCs : ¬ Γ.O ≤ a ⊔ C_s := by
          intro hle
          have hdir : (a ⊔ C_s) ⊓ l = a := by
            rw [sup_comm a C_s]; exact inf_comm l (C_s ⊔ a) ▸
              line_direction hCs_atom hCs_not_l ha_on
          exact ha_ne_O ((ha.le_iff.mp (le_inf hle (show Γ.O ≤ l from le_sup_left) |>.trans hdir.le)).resolve_left Γ.hO.1).symm
        have haCs_cov : a ⊔ C_s ⋖ π := by
          have haCs_O_eq : a ⊔ C_s ⊔ Γ.O = π := by
            have hOa_eq_l : Γ.O ⊔ a = l := by
              have hO_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
                (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
              exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
                (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt hO_lt)

            have h1 : a ⊔ C_s ⊔ Γ.O = l ⊔ C_s := by
              rw [sup_comm (a ⊔ C_s) Γ.O, ← sup_assoc, hOa_eq_l]

            have h2 : l ⊔ C_s = π := by
              have hl_lt : l < l ⊔ C_s := lt_of_le_of_ne le_sup_left
                (fun h => hCs_not_l (le_sup_right.trans h.symm.le))
              exact (hl_covBy.eq_or_eq hl_lt.le (sup_le le_sup_left hCs_plane)).resolve_left
                (ne_of_gt hl_lt)
            rw [h1, h2]
          rw [← haCs_O_eq]
          exact line_covBy_plane ha hCs_atom Γ.hO ha_ne_Cs ha_ne_O (Ne.symm (fun h => hCs_ne_O h.symm)) hO_not_aCs
        have hacC'sc_le_π : ac ⊔ C'_sc ≤ π := sup_le (hac_on.trans le_sup_left) hC'sc_plane
        have hacC'sc_not_le : ¬ (ac ⊔ C'_sc ≤ a ⊔ C_s) := by
          intro hle

          have hdir_aCs : (a ⊔ C_s) ⊓ l = a := by
            rw [sup_comm a C_s]; exact inf_comm l (C_s ⊔ a) ▸
              line_direction hCs_atom hCs_not_l ha_on
          have hac_le_a : ac ≤ a :=
            (le_inf (le_sup_left.trans hle) hac_on).trans hdir_aCs.le
          have hac_eq_a : ac = a := (ha.le_iff.mp hac_le_a).resolve_left hac_atom.1

          have ha_not_OCs : ¬ a ≤ Γ.O ⊔ C_s := by
            intro hle'
            have hOCs_l : (Γ.O ⊔ C_s) ⊓ l = Γ.O := by
              rw [sup_comm Γ.O C_s]; exact inf_comm l (C_s ⊔ Γ.O) ▸
                line_direction hCs_atom hCs_not_l (show Γ.O ≤ l from le_sup_left)
            have ha_le_O : a ≤ Γ.O := le_inf hle' ha_on |>.trans hOCs_l.le
            exact ha_ne_O ((Γ.hO.le_iff.mp ha_le_O).resolve_left ha.1)
          have haCs_OCs : (a ⊔ C_s) ⊓ (Γ.O ⊔ C_s) = C_s := by
            rw [sup_comm a C_s, sup_comm Γ.O C_s]
            have hO_not_Csa : ¬ Γ.O ≤ C_s ⊔ a := by
              rw [sup_comm C_s a]; exact hO_not_aCs
            exact modular_intersection hCs_atom ha Γ.hO (Ne.symm ha_ne_Cs) hCs_ne_O ha_ne_O hO_not_Csa
          have hC'sc_le_Cs : C'_sc ≤ C_s :=
            (le_inf (le_sup_right.trans hle) hC'sc_le_OCs).trans haCs_OCs.le
          have hC'sc_eq_Cs : C'_sc = C_s := (hCs_atom.le_iff.mp hC'sc_le_Cs).resolve_left hC'sc_atom.1

          have hC'sc_le_σU' : C_s ≤ σ ⊔ Γ.U := hC'sc_eq_Cs ▸ hC'sc_le_σU

          have hσ_not_q' : ¬ σ ≤ q := by
            intro hσq
            have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
              intro hle'
              have hOCl' : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
                rw [sup_comm Γ.O Γ.C, show l = Γ.O ⊔ Γ.U from rfl]
                exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
                  line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
              exact Γ.hOU ((Γ.hO.le_iff.mp (le_inf hle' (show Γ.U ≤ l from le_sup_right) |>.trans hOCl'.le)).resolve_left Γ.hU.1).symm
            have hq_OC : q ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
              rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C, sup_inf_assoc_of_le Γ.U (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)]
              have : Γ.U ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
                (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun hh => hU_not_OC (hh ▸ inf_le_right))
              rw [this, sup_bot_eq]
            exact hCσ ((Γ.hC.le_iff.mp (le_inf hσq hσ_on_OC |>.trans hq_OC.le)).resolve_left hσ_atom.1).symm
          have hσ_ne_U' : σ ≠ Γ.U := fun h => hσ_not_m (h ▸ le_sup_left)
          have hqσU_eq_U' : q ⊓ (σ ⊔ Γ.U) = Γ.U := by
            rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm σ Γ.U]
            exact modular_intersection Γ.hU Γ.hC hσ_atom hUC hσ_ne_U'.symm hCσ hσ_not_q'
          have hCs_le_U : C_s ≤ Γ.U :=
            (le_inf hCs_on_q hC'sc_le_σU').trans hqσU_eq_U'.le
          exact hCs_ne_U ((Γ.hU.le_iff.mp hCs_le_U).resolve_left hCs_atom.1)
        have hac_ne_C'sc : ac ≠ C'_sc := fun h => hC'sc_not_l (h ▸ hac_on)
        have hac_lt : ac < ac ⊔ C'_sc := lt_of_le_of_ne le_sup_left
          (fun h => hac_ne_C'sc ((hac_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hC'sc_atom.1).symm)
        exact lines_meet_if_coplanar haCs_cov hacC'sc_le_π hacC'sc_not_le hac_atom hac_lt

      have hmeet_eq_eb : (a ⊔ C_s) ⊓ (ac ⊔ C'_sc) = e_b :=
        (heb_atom.le_iff.mp hmeet_le_eb).resolve_left hmeet_ne_bot
      exact hmeet_eq_eb ▸ hmeet_le_ac_C'sc

    have hC'sc_le_aceb : C'_sc ≤ ac ⊔ e_b := by

      have hac_ne_eb : ac ≠ e_b := by
        intro h; exact (fun hle => hac_ne_U (Γ.atom_on_both_eq_U hac_atom hac_on hle))
          (h ▸ inf_le_right : ac ≤ m)
      have hac_ne_C'sc : ac ≠ C'_sc := fun h => hC'sc_not_l (h ▸ hac_on)
      have hac_lt : ac < ac ⊔ e_b := lt_of_le_of_ne le_sup_left
        (fun h => hac_ne_eb ((hac_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          heb_atom.1).symm)
      have h_le : ac ⊔ e_b ≤ ac ⊔ C'_sc := sup_le le_sup_left heb_le_acC'sc
      have hac_lt' : ac < ac ⊔ C'_sc := lt_of_le_of_ne le_sup_left
        (fun h => hac_ne_C'sc ((hac_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hC'sc_atom.1).symm)
      have h_eq : ac ⊔ e_b = ac ⊔ C'_sc :=
        ((atom_covBy_join hac_atom hC'sc_atom hac_ne_C'sc).eq_or_eq hac_lt.le h_le).resolve_left
          (ne_of_gt hac_lt)
      exact h_eq ▸ le_sup_right

    have hC'sc_eq_meet : C'_sc = (σ ⊔ Γ.U) ⊓ (ac ⊔ e_b) := by
      have h_le : C'_sc ≤ (σ ⊔ Γ.U) ⊓ (ac ⊔ e_b) := le_inf hC'sc_le_σU hC'sc_le_aceb
      have h_meet_atom : IsAtom ((σ ⊔ Γ.U) ⊓ (ac ⊔ e_b)) := by

        have hσ_ne_U : σ ≠ Γ.U := fun h => hσ_not_m (h ▸ le_sup_left)
        have hac_not_m : ¬ ac ≤ m := fun h => hac_ne_U (Γ.atom_on_both_eq_U hac_atom hac_on h)

        have hσU_dir : (σ ⊔ Γ.U) ⊓ m = Γ.U :=
          line_direction hσ_atom hσ_not_m (le_sup_left : Γ.U ≤ m)

        have haceb_dir : (ac ⊔ e_b) ⊓ m = e_b :=
          line_direction hac_atom hac_not_m (inf_le_right : e_b ≤ m)

        have hU_ne_eb : Γ.U ≠ e_b := by
          intro h
          have hOCb_l : (Γ.O ⊔ C_b) ⊓ l = Γ.O := by
            rw [sup_comm Γ.O C_b]; exact inf_comm l (C_b ⊔ Γ.O) ▸
              line_direction hCb_atom hCb_not_l (show Γ.O ≤ l from le_sup_left)
          exact Γ.hOU ((Γ.hO.le_iff.mp (le_inf (h ▸ (inf_le_left : e_b ≤ Γ.O ⊔ C_b)) (show Γ.U ≤ l from le_sup_right) |>.trans hOCb_l.le)).resolve_left Γ.hU.1).symm

        have h_lines_ne : σ ⊔ Γ.U ≠ ac ⊔ e_b := by
          intro heq; exact hU_ne_eb (hσU_dir.symm.trans (heq ▸ haceb_dir))

        have haceb_le_π : ac ⊔ e_b ≤ π :=
          sup_le (hac_on.trans le_sup_left) ((inf_le_right : e_b ≤ m).trans hm_le_π)

        have haceb_not_le : ¬ (ac ⊔ e_b ≤ σ ⊔ Γ.U) := by
          intro hle
          exact hU_ne_eb ((Γ.hU.le_iff.mp ((le_inf (le_sup_right.trans hle) (inf_le_right : e_b ≤ m)).trans hσU_dir.le)).resolve_left heb_atom.1).symm

        have hσU_cov : σ ⊔ Γ.U ⋖ π := by
          have hO_not_σU : ¬ Γ.O ≤ σ ⊔ Γ.U := by
            intro hle

            have hσ_inf_l : σ ⊓ l = ⊥ :=
              (hσ_atom.le_iff.mp inf_le_left).resolve_right (fun h => hσ_not_l (h ▸ inf_le_right))
            have hσUl : (σ ⊔ Γ.U) ⊓ l = Γ.U := by
              rw [sup_comm σ Γ.U]; exact (sup_inf_assoc_of_le σ (le_sup_right : Γ.U ≤ l)).symm ▸ by rw [hσ_inf_l, sup_bot_eq]
            exact Γ.hOU ((Γ.hU.le_iff.mp (le_inf hle (show Γ.O ≤ l from le_sup_left) |>.trans hσUl.le)).resolve_left Γ.hO.1)
          have hσUO_eq : σ ⊔ Γ.U ⊔ Γ.O = π := by
            have h1 : σ ⊔ Γ.U ⊔ Γ.O = σ ⊔ l := by
              rw [sup_assoc, sup_comm Γ.U Γ.O]
            have h2 : σ ⊔ l = π := by
              have hl_lt : l < σ ⊔ l := lt_of_le_of_ne le_sup_right
                (fun h => hσ_not_l (le_sup_left.trans h.symm.le))
              exact (hl_covBy.eq_or_eq hl_lt.le
                (sup_le hσ_plane le_sup_left)).resolve_left (ne_of_gt hl_lt)
            rw [h1, h2]
          rw [← hσUO_eq]
          exact line_covBy_plane hσ_atom Γ.hU Γ.hO hσ_ne_U
            (fun h => hσ_not_l (h ▸ (show Γ.O ≤ l from le_sup_left)))
            (Ne.symm Γ.hOU) hO_not_σU
        have hac_ne_eb : ac ≠ e_b := fun h => hac_not_m (h ▸ inf_le_right)
        have hac_lt : ac < ac ⊔ e_b := lt_of_le_of_ne le_sup_left
          (fun h => hac_ne_eb ((hac_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left heb_atom.1).symm)
        have h_ne_bot : (σ ⊔ Γ.U) ⊓ (ac ⊔ e_b) ≠ ⊥ :=
          lines_meet_if_coplanar hσU_cov haceb_le_π haceb_not_le hac_atom hac_lt
        have h_lt : (σ ⊔ Γ.U) ⊓ (ac ⊔ e_b) < σ ⊔ Γ.U := by
          apply lt_of_le_of_ne inf_le_left; intro h

          have hσU_le : σ ⊔ Γ.U ≤ ac ⊔ e_b := h ▸ inf_le_right
          have hU_le_eb : Γ.U ≤ e_b :=
            (le_inf (le_sup_right.trans hσU_le) (le_sup_left : Γ.U ≤ m)).trans haceb_dir.le
          exact hU_ne_eb ((heb_atom.le_iff.mp hU_le_eb).resolve_left Γ.hU.1)
        exact line_height_two hσ_atom Γ.hU hσ_ne_U h_ne_bot.bot_lt h_lt
      exact (h_meet_atom.le_iff.mp h_le).resolve_left hC'sc_atom.1

    have hOC'bc_eq_OCb : Γ.O ⊔ C'_bc = Γ.O ⊔ C_b := by

      have hO_ne_C'bc : Γ.O ≠ C'_bc := by
        intro h

        have hO_le_bcE : Γ.O ≤ bc ⊔ Γ.E := h ▸ (h_mki_b ▸ inf_le_right : C'_bc ≤ bc ⊔ Γ.E)
        have hbcE_l : (bc ⊔ Γ.E) ⊓ l = bc := by
          change (bc ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = bc; rw [sup_comm bc Γ.E]
          exact line_direction Γ.hE_atom Γ.hE_not_l hbc_on
        have hO_le_bc : Γ.O ≤ bc := le_inf hO_le_bcE (show Γ.O ≤ l from le_sup_left) |>.trans hbcE_l.le
        exact hbc_ne_O ((hbc_atom.le_iff.mp hO_le_bc).resolve_left Γ.hO.1).symm
      have hO_ne_Cb : Γ.O ≠ C_b := fun h => hCb_not_l (h ▸ le_sup_left)
      have hO_lt : Γ.O < Γ.O ⊔ C'_bc := lt_of_le_of_ne le_sup_left
        (fun h => hO_ne_C'bc ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hC'bc_atom.1).symm)
      exact ((atom_covBy_join Γ.hO hCb_atom hO_ne_Cb).eq_or_eq hO_lt.le
        (sup_le le_sup_left hC'bc_le_OCb)).resolve_left (ne_of_gt hO_lt)
    have heb_eq : (Γ.O ⊔ C'_bc) ⊓ m = e_b := by
      rw [hOC'bc_eq_OCb]
    have hC'bc_ne_U : C'_bc ≠ Γ.U := by
      intro h

      have hU_le_bcE : Γ.U ≤ bc ⊔ Γ.E := h ▸ (h_mki_b ▸ inf_le_right : C'_bc ≤ bc ⊔ Γ.E)
      have hbcE_l : (bc ⊔ Γ.E) ⊓ l = bc := by
        change (bc ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = bc; rw [sup_comm bc Γ.E]
        exact line_direction Γ.hE_atom Γ.hE_not_l hbc_on
      have hU_le_bc : Γ.U ≤ bc := le_inf hU_le_bcE (show Γ.U ≤ l from le_sup_right) |>.trans hbcE_l.le
      exact hbc_ne_U ((hbc_atom.le_iff.mp hU_le_bc).resolve_left Γ.hU.1).symm
    have hC'bcU_eq_σU : C'_bc ⊔ Γ.U = σ ⊔ Γ.U := by

      have hσ_ne_U : σ ≠ Γ.U := fun h => hσ_not_m (h ▸ le_sup_left)
      have hU_lt : Γ.U < Γ.U ⊔ C'_bc := lt_of_le_of_ne le_sup_left
        (fun h => hC'bc_ne_U (((Γ.hU.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hC'bc_atom.1)))
      rw [sup_comm C'_bc Γ.U, sup_comm σ Γ.U]
      exact ((atom_covBy_join Γ.hU hσ_atom (Ne.symm hσ_ne_U)).eq_or_eq hU_lt.le
        (sup_le le_sup_left (sup_comm Γ.U σ ▸ hC'bc_le_σU))).resolve_left (ne_of_gt hU_lt)

    have h_ki_mul_local : parallelogram_completion Γ.O ac C_bc m =
        parallelogram_completion Γ.O (coord_add Γ ac bc) Γ.C m :=
      key_identity Γ ac bc hac_atom hbc_atom hac_on hbc_on hac_ne_O hbc_ne_O
        hac_ne_U hbc_ne_U hac_ne_bc R hR hR_not h_irred

    have hacbc_ne_O_local : coord_add Γ ac bc ≠ Γ.O := hacbc_ne_O
    have hOacbc_eq_l_local : Γ.O ⊔ coord_add Γ ac bc = l := by
      have hO_lt : Γ.O < Γ.O ⊔ coord_add Γ ac bc := lt_of_le_of_ne le_sup_left
        (fun h => hacbc_ne_O_local ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hacbc_atom.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
        (sup_le le_sup_left hacbc_on)).resolve_left (ne_of_gt hO_lt)
    have hCacbc_eq_beta_local : parallelogram_completion Γ.O (coord_add Γ ac bc) Γ.C m =
        q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := pc_eq_beta (coord_add Γ ac bc) hOacbc_eq_l_local

    have hpc_acbc : parallelogram_completion Γ.O ac C_bc m =
        q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by
      rw [h_ki_mul_local, hCacbc_eq_beta_local]

    have hq_eq : q ⊓ (ac ⊔ e_bc) = q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by
      rw [← hpc_eq', hpc_acbc]

    have hC'sc_eq_acbc : C'_sc = (σ ⊔ Γ.U) ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by

      have hOac_eq_l : Γ.O ⊔ ac = l := by
        have hO_lt : Γ.O < Γ.O ⊔ ac := lt_of_le_of_ne le_sup_left
          (fun h => hac_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hac_atom.1))
        exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
          (sup_le le_sup_left hac_on)).resolve_left (ne_of_gt hO_lt)
      have hOac_m : (Γ.O ⊔ ac) ⊓ m = Γ.U := by rw [hOac_eq_l]; exact hlm_eq_U
      have hpc_C'bc_eq : parallelogram_completion Γ.O ac C'_bc m = C'_sc := by
        show (C'_bc ⊔ (Γ.O ⊔ ac) ⊓ m) ⊓ (ac ⊔ (Γ.O ⊔ C'_bc) ⊓ m) = C'_sc
        rw [hOac_m, heb_eq, hC'bcU_eq_σU, hC'sc_eq_meet]

      set P := parallelogram_completion Γ.O ac C_bc m with hP_def
      have hP_eq : P = q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := hpc_acbc

      have hwd : parallelogram_completion Γ.O ac C'_bc m =
          parallelogram_completion C_bc P C'_bc m := by

        have hbc_not_m : ¬ bc ≤ m := fun h => hbc_ne_U (Γ.atom_on_both_eq_U hbc_atom hbc_on h)
        have hbc_ne_E : bc ≠ Γ.E := fun h => hbc_not_m (h ▸ Γ.hE_on_m)
        have hbcE_l : (bc ⊔ Γ.E) ⊓ l = bc := by
          rw [sup_comm]; exact line_direction Γ.hE_atom Γ.hE_not_l hbc_on
        have hCbc_le_bcE : C_bc ≤ bc ⊔ Γ.E := hCbc_eq_beta ▸ inf_le_right
        have hO_not_bcE : ¬ Γ.O ≤ bc ⊔ Γ.E := by
          intro hle'
          exact (Ne.symm hbc_ne_O) ((hbc_atom.le_iff.mp (le_inf hle'
            (show Γ.O ≤ l from le_sup_left) |>.trans hbcE_l.le)).resolve_left Γ.hO.1)

        have hσU_l : (σ ⊔ Γ.U) ⊓ l = Γ.U :=
          line_direction hσ_atom hσ_not_l (show Γ.U ≤ l from le_sup_right)

        have hσU_m : (σ ⊔ Γ.U) ⊓ m = Γ.U :=
          line_direction hσ_atom hσ_not_m (le_sup_left : Γ.U ≤ m)

        have hσ_not_q : ¬ σ ≤ q := by
          intro hσq
          have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
            intro hle'
            have hOCl : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
              rw [sup_comm Γ.O Γ.C, show l = Γ.O ⊔ Γ.U from rfl]
              exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
                line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
            exact Γ.hOU ((Γ.hO.le_iff.mp (le_inf hle' (show Γ.U ≤ l from le_sup_right)
              |>.trans hOCl.le)).resolve_left Γ.hU.1).symm
          have hq_OC : q ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
            rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C,
                sup_inf_assoc_of_le Γ.U (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)]
            rw [(Γ.hU.le_iff.mp inf_le_left).resolve_right
              (fun hh => hU_not_OC (hh ▸ inf_le_right)), sup_bot_eq]
          exact hCσ ((Γ.hC.le_iff.mp (le_inf hσq hσ_on_OC
            |>.trans hq_OC.le)).resolve_left hσ_atom.1).symm
        have hσ_ne_U' : σ ≠ Γ.U := fun h' => hσ_not_m (h' ▸ le_sup_left)
        have hqσU : q ⊓ (σ ⊔ Γ.U) = Γ.U := by
          rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm σ Γ.U]
          exact modular_intersection Γ.hU Γ.hC hσ_atom hUC hσ_ne_U'.symm hCσ hσ_not_q

        have hO_le_pi : Γ.O ≤ π := le_sup_left.trans le_sup_left
        have hac_le_pi : ac ≤ π := hac_on.trans le_sup_left
        have hC'bc_le_pi : C'_bc ≤ π :=
          hC'bc_le_σU.trans (sup_le hσ_plane ((show Γ.U ≤ m from le_sup_left).trans hm_le_π))

        have hO_ne_ac : Γ.O ≠ ac := Ne.symm hac_ne_O
        have hO_ne_C'bc : Γ.O ≠ C'_bc := by
          intro h; exact hbc_ne_O ((hbc_atom.le_iff.mp (le_inf (h ▸ hC'bc_le_bcE)
            (show Γ.O ≤ l from le_sup_left) |>.trans hbcE_l.le)).resolve_left Γ.hO.1).symm
        have hac_ne_Cbc : ac ≠ C_bc := fun h => hCbc_not_l (h ▸ hac_on)
        have hac_ne_C'bc : ac ≠ C'_bc := by
          intro h; exact hac_ne_U ((Γ.hU.le_iff.mp (le_inf (h ▸ hC'bc_le_σU) hac_on
            |>.trans hσU_l.le)).resolve_left hac_atom.1)
        have hCbc_ne_C'bc' : C_bc ≠ C'_bc := by
          intro h; exact hCbc_ne_U ((Γ.hU.le_iff.mp (le_inf hCbc_on_q (h ▸ hC'bc_le_σU)
            |>.trans hqσU.le)).resolve_left hCbc_atom.1)

        have hac_not_m : ¬ ac ≤ m := fun h => hac_ne_U (Γ.atom_on_both_eq_U hac_atom hac_on h)
        have hCbc_not_m' : ¬ C_bc ≤ m := by
          intro hle; exact hCbc_ne_U ((Γ.hU.le_iff.mp (le_inf hCbc_on_q hle
            |>.trans hqm_eq_U.le)).resolve_left hCbc_atom.1)
        have hC'bc_not_m : ¬ C'_bc ≤ m := by
          intro hle; exact hC'bc_ne_U ((Γ.hU.le_iff.mp (le_inf hC'bc_le_σU hle
            |>.trans hσU_m.le)).resolve_left hC'bc_atom.1)

        have hm_line' : ∀ x, IsAtom x → x ≤ m → x ⋖ m :=
          fun x hx hxm => line_covers_its_atoms Γ.hU Γ.hV hUV hx hxm

        have hCbc_not_Oac : ¬ C_bc ≤ Γ.O ⊔ ac := hOac_eq_l ▸ hCbc_not_l
        have hC'bc_not_Oac : ¬ C'_bc ≤ Γ.O ⊔ ac := by
          rw [hOac_eq_l]; intro hle
          exact hC'bc_ne_U ((Γ.hU.le_iff.mp (le_inf hC'bc_le_σU hle
            |>.trans hσU_l.le)).resolve_left hC'bc_atom.1)

        have hbcE_covBy_pi : bc ⊔ Γ.E ⋖ π := by

          have hbcO_eq_l : bc ⊔ Γ.O = l := by
            have hO_lt : Γ.O < Γ.O ⊔ bc := lt_of_le_of_ne le_sup_left
              (fun h => hbc_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hbc_atom.1))
            rw [sup_comm]; exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
              (sup_le (show Γ.O ≤ l from le_sup_left) hbc_on)).resolve_left (ne_of_gt hO_lt)
          have hbcEO_eq_pi : bc ⊔ Γ.E ⊔ Γ.O = π := by
            have : bc ⊔ Γ.E ⊔ Γ.O = l ⊔ Γ.E := by
              rw [sup_assoc, sup_comm Γ.E Γ.O, ← sup_assoc, hbcO_eq_l]
            rw [this]
            have hl_lt : l < l ⊔ Γ.E := lt_of_le_of_ne le_sup_left
              (fun h => Γ.hE_not_l (le_sup_right.trans h.symm.le))
            exact (hl_covBy.eq_or_eq hl_lt.le
              (sup_le le_sup_left (Γ.hE_on_m.trans hm_le_π))).resolve_left (ne_of_gt hl_lt)
          have hE_ne_O : Γ.E ≠ Γ.O := fun h => Γ.hE_not_l (h.symm ▸ (show Γ.O ≤ l from le_sup_left))
          exact hbcEO_eq_pi ▸ line_covBy_plane hbc_atom Γ.hE_atom Γ.hO hbc_ne_E
            hbc_ne_O hE_ne_O hO_not_bcE
        have hC'bc_not_OCbc : ¬ C'_bc ≤ Γ.O ⊔ C_bc := by
          intro hle

          have hOCbc_ne_bcE : Γ.O ⊔ C_bc ≠ bc ⊔ Γ.E :=
            fun heq => hO_not_bcE (le_sup_left.trans heq.le)
          have hmeet_ne_bot : (Γ.O ⊔ C_bc) ⊓ (bc ⊔ Γ.E) ≠ ⊥ := by
            rw [inf_comm]
            exact lines_meet_if_coplanar hbcE_covBy_pi
              (sup_le hO_le_pi hCbc_plane) (fun h => hO_not_bcE (le_sup_left.trans h))
              Γ.hO (lt_of_le_of_ne le_sup_left
                (fun h => hO_ne_Cbc ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hCbc_atom.1).symm))
          have hmeet_lt : (Γ.O ⊔ C_bc) ⊓ (bc ⊔ Γ.E) < Γ.O ⊔ C_bc := by
            apply lt_of_le_of_ne inf_le_left; intro h
            exact hO_not_bcE (le_sup_left.trans (h ▸ inf_le_right))
          have hmeet_atom : IsAtom ((Γ.O ⊔ C_bc) ⊓ (bc ⊔ Γ.E)) :=
            line_height_two Γ.hO hCbc_atom hO_ne_Cbc hmeet_ne_bot.bot_lt hmeet_lt
          have hCbc_le_meet : C_bc ≤ (Γ.O ⊔ C_bc) ⊓ (bc ⊔ Γ.E) :=
            le_inf le_sup_right hCbc_le_bcE
          have hC'bc_le_meet : C'_bc ≤ (Γ.O ⊔ C_bc) ⊓ (bc ⊔ Γ.E) :=
            le_inf hle hC'bc_le_bcE
          exact hCbc_ne_C'bc' ((hmeet_atom.le_iff.mp hCbc_le_meet).resolve_left hCbc_atom.1
            |>.trans ((hmeet_atom.le_iff.mp hC'bc_le_meet).resolve_left hC'bc_atom.1).symm)

        have hCbc_not_OC'bc : ¬ C_bc ≤ Γ.O ⊔ C'_bc := by
          intro hle
          have hOC'bc_ne_bcE : Γ.O ⊔ C'_bc ≠ bc ⊔ Γ.E :=
            fun heq => hO_not_bcE (le_sup_left.trans heq.le)
          have hmeet_ne_bot : (Γ.O ⊔ C'_bc) ⊓ (bc ⊔ Γ.E) ≠ ⊥ := by
            rw [inf_comm]
            exact lines_meet_if_coplanar hbcE_covBy_pi
              (sup_le hO_le_pi hC'bc_le_pi) (fun h => hO_not_bcE (le_sup_left.trans h))
              Γ.hO (lt_of_le_of_ne le_sup_left
                (fun h => hO_ne_C'bc ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hC'bc_atom.1).symm))
          have hmeet_lt : (Γ.O ⊔ C'_bc) ⊓ (bc ⊔ Γ.E) < Γ.O ⊔ C'_bc := by
            apply lt_of_le_of_ne inf_le_left; intro h
            exact hO_not_bcE (le_sup_left.trans (h ▸ inf_le_right))
          have hmeet_atom : IsAtom ((Γ.O ⊔ C'_bc) ⊓ (bc ⊔ Γ.E)) :=
            line_height_two Γ.hO hC'bc_atom hO_ne_C'bc hmeet_ne_bot.bot_lt hmeet_lt
          have hC'bc_le_meet : C'_bc ≤ (Γ.O ⊔ C'_bc) ⊓ (bc ⊔ Γ.E) :=
            le_inf le_sup_right hC'bc_le_bcE
          have hCbc_le_meet : C_bc ≤ (Γ.O ⊔ C'_bc) ⊓ (bc ⊔ Γ.E) :=
            le_inf hle hCbc_le_bcE
          exact hCbc_ne_C'bc' ((hmeet_atom.le_iff.mp hCbc_le_meet).resolve_left hCbc_atom.1
            |>.trans ((hmeet_atom.le_iff.mp hC'bc_le_meet).resolve_left hC'bc_atom.1).symm)

        have hC'bc_not_q : ¬ C'_bc ≤ q := by
          intro hle; exact hC'bc_ne_U ((Γ.hU.le_iff.mp (le_inf hle hC'bc_le_σU
            |>.trans hqσU.le)).resolve_left hC'bc_atom.1)
        have hP_le_q : P ≤ q := hpc_eq'.symm ▸ inf_le_left
        have hC'bc_not_CbcP : ¬ C'_bc ≤ C_bc ⊔ P := by
          intro hle; exact hC'bc_not_q (hle.trans (sup_le hCbc_on_q hP_le_q))

        have h_span : Γ.O ⊔ C_bc ⊔ C'_bc = π := by

          have hOCbc_covBy_pi : Γ.O ⊔ C_bc ⋖ π := by

            have hebc_covBy_m : e_bc ⋖ m := hm_line' e_bc hebc_atom inf_le_right
            have h_inf_cov : m ⊓ (Γ.O ⊔ C_bc) ⋖ m := inf_comm (Γ.O ⊔ C_bc) m ▸ hebc_covBy_m
            have hm_cov_sup := covBy_sup_of_inf_covBy_left h_inf_cov

            have hOCbc_le_pi : Γ.O ⊔ C_bc ≤ π := sup_le hO_le_pi hCbc_plane
            have hm_sup_OCbc_le : m ⊔ (Γ.O ⊔ C_bc) ≤ π := sup_le hm_le_π hOCbc_le_pi
            have hm_ne_sup : m ≠ m ⊔ (Γ.O ⊔ C_bc) := by
              intro h; exact Γ.hO_not_m (le_sup_left.trans (le_sup_right.trans h.symm.le))
            have hm_sup_eq : m ⊔ (Γ.O ⊔ C_bc) = π :=
              (Γ.m_covBy_π.eq_or_eq (lt_of_le_of_ne le_sup_left hm_ne_sup).le
                hm_sup_OCbc_le).resolve_left (Ne.symm hm_ne_sup)

            have hebc_covBy_OCbc : e_bc ⋖ Γ.O ⊔ C_bc :=
              line_covers_its_atoms Γ.hO hCbc_atom hO_ne_Cbc hebc_atom inf_le_left

            rwa [hm_sup_eq] at hm_cov_sup
          have hlt : Γ.O ⊔ C_bc < Γ.O ⊔ C_bc ⊔ C'_bc := lt_of_le_of_ne le_sup_left
            (fun h => hC'bc_not_OCbc (le_sup_right.trans h.symm.le))
          exact (hOCbc_covBy_pi.eq_or_eq hlt.le
            (sup_le (sup_le hO_le_pi hCbc_plane) hC'bc_le_pi)).resolve_left (ne_of_gt hlt)
        exact parallelogram_completion_well_defined
          Γ.hO hac_atom hCbc_atom hC'bc_atom
          hO_ne_ac hO_ne_Cbc hO_ne_C'bc hac_ne_Cbc hac_ne_C'bc hCbc_ne_C'bc'
          hO_le_pi hac_le_pi hCbc_plane hC'bc_le_pi
          hm_le_π Γ.m_covBy_π hm_line'
          Γ.hO_not_m hac_not_m hCbc_not_m' hC'bc_not_m
          hCbc_not_Oac hC'bc_not_Oac hC'bc_not_OCbc hCbc_not_OC'bc hC'bc_not_CbcP
          h_span R hR hR_not h_irred

      have hCbc_ne_P : C_bc ≠ P := by

        intro heq; rw [hCbc_eq_beta, hP_eq] at heq

        have hbc_ne_E : bc ≠ Γ.E := fun h => hbc_ne_U (Γ.atom_on_both_eq_U hbc_atom hbc_on (h ▸ Γ.hE_on_m))
        have hacbc_ne_E : coord_add Γ ac bc ≠ Γ.E :=
          fun h => hacbc_ne_U (Γ.atom_on_both_eq_U hacbc_atom hacbc_on (h ▸ Γ.hE_on_m))

        have hP'_atom := beta_atom Γ hbc_atom hbc_on hbc_ne_O hbc_ne_U
        have hP'_cov := line_covers_its_atoms hbc_atom Γ.hE_atom hbc_ne_E hP'_atom inf_le_right
        have hE_not_q : ¬ Γ.E ≤ q := fun hle =>
          Γ.hEU ((Γ.hU.le_iff.mp (le_inf hle Γ.hE_on_m |>.trans hqm_eq_U.le)).resolve_left Γ.hE_atom.1)
        have hP'_ne_E : q ⊓ (bc ⊔ Γ.E) ≠ Γ.E := fun h => hE_not_q (h ▸ inf_le_left)
        have hP'_lt : q ⊓ (bc ⊔ Γ.E) < q ⊓ (bc ⊔ Γ.E) ⊔ Γ.E := lt_of_le_of_ne le_sup_left
          (fun h => hP'_ne_E ((hP'_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_atom.1).symm)
        have hP'E_eq : q ⊓ (bc ⊔ Γ.E) ⊔ Γ.E = bc ⊔ Γ.E :=
          (hP'_cov.eq_or_eq hP'_lt.le (sup_le inf_le_right le_sup_right)).resolve_left (ne_of_gt hP'_lt)
        have hP2_atom := beta_atom Γ hacbc_atom hacbc_on hacbc_ne_O hacbc_ne_U
        have hP2_cov := line_covers_its_atoms hacbc_atom Γ.hE_atom hacbc_ne_E hP2_atom inf_le_right
        have hP2_ne_E : q ⊓ (coord_add Γ ac bc ⊔ Γ.E) ≠ Γ.E := fun h => hE_not_q (h ▸ inf_le_left)
        have hP2_lt : q ⊓ (coord_add Γ ac bc ⊔ Γ.E) < q ⊓ (coord_add Γ ac bc ⊔ Γ.E) ⊔ Γ.E := lt_of_le_of_ne le_sup_left
          (fun h => hP2_ne_E ((hP2_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_atom.1).symm)
        have hP2E_eq : q ⊓ (coord_add Γ ac bc ⊔ Γ.E) ⊔ Γ.E = coord_add Γ ac bc ⊔ Γ.E :=
          (hP2_cov.eq_or_eq hP2_lt.le (sup_le inf_le_right le_sup_right)).resolve_left (ne_of_gt hP2_lt)
        have hlines_eq : bc ⊔ Γ.E = coord_add Γ ac bc ⊔ Γ.E := by rw [← hP'E_eq, heq, hP2E_eq]
        have hbc_eq : bc = coord_add Γ ac bc := by
          have h1 : (bc ⊔ Γ.E) ⊓ l = bc := by
            rw [sup_comm]; exact line_direction Γ.hE_atom Γ.hE_not_l hbc_on
          have h2 : (coord_add Γ ac bc ⊔ Γ.E) ⊓ l = coord_add Γ ac bc := by
            rw [sup_comm]; exact line_direction Γ.hE_atom Γ.hE_not_l hacbc_on
          calc bc = (bc ⊔ Γ.E) ⊓ l := h1.symm
            _ = (coord_add Γ ac bc ⊔ Γ.E) ⊓ l := by rw [hlines_eq]
            _ = coord_add Γ ac bc := h2

        have hac_ne_C : ac ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hac_on)
        have hac_not_m : ¬ ac ≤ m := fun h => hac_ne_U (Γ.atom_on_both_eq_U hac_atom hac_on h)
        set d_ac := (ac ⊔ Γ.C) ⊓ m
        have hd_atom : IsAtom d_ac :=
          line_meets_m_at_atom hac_atom Γ.hC hac_ne_C (sup_le (hac_on.trans le_sup_left) Γ.hC_plane) hm_le_π Γ.m_covBy_π hac_not_m
        have hCbc_not_m : ¬ C_bc ≤ m := by
          intro hle
          exact hCbc_ne_U ((Γ.hU.le_iff.mp (le_inf hCbc_on_q hle |>.trans hqm_eq_U.le)).resolve_left hCbc_atom.1)
        have hCbc_atom' : IsAtom C_bc := hCbc_eq_beta ▸ hP'_atom
        have hd_ne_Cbc : d_ac ≠ C_bc := fun h => hCbc_not_m (h ▸ inf_le_right)
        have hbc_le_ECbc : bc ≤ Γ.E ⊔ C_bc := by
          rw [hCbc_eq_beta]
          calc bc ≤ bc ⊔ Γ.E := le_sup_left
            _ = q ⊓ (bc ⊔ Γ.E) ⊔ Γ.E := hP'E_eq.symm
            _ = Γ.E ⊔ q ⊓ (bc ⊔ Γ.E) := sup_comm _ _
        have hbc_le_dCbc : bc ≤ d_ac ⊔ C_bc := by

          rw [hbc_eq]; rw [hCbc_eq_beta]; show coord_add Γ ac bc ≤ d_ac ⊔ q ⊓ (bc ⊔ Γ.E)
          exact (inf_le_left : coord_add Γ ac bc ≤ (ac ⊔ Γ.C) ⊓ m ⊔ (bc ⊔ Γ.E) ⊓ q).trans
            (sup_le_sup_left (by rw [inf_comm]) _)
        have hbc_ne_Cbc : bc ≠ C_bc := by
          intro h; rw [hCbc_eq_beta] at h
          exact hbc_ne_U ((Γ.hU.le_iff.mp (le_inf (h ▸ inf_le_left : bc ≤ q) hbc_on |>.trans
            (inf_comm l q ▸ hlq_eq_U).le)).resolve_left hbc_atom.1)
        have hbc_lt : bc < bc ⊔ C_bc := lt_of_le_of_ne le_sup_left
          (fun h => hbc_ne_Cbc ((hbc_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hCbc_atom'.1).symm)

        have h_le : bc ⊔ C_bc ≤ d_ac ⊔ C_bc := sup_le hbc_le_dCbc le_sup_right
        have hbcCbc_eq_dCbc : bc ⊔ C_bc = d_ac ⊔ C_bc :=
          ((sup_comm C_bc d_ac ▸ atom_covBy_join hCbc_atom' hd_atom (Ne.symm hd_ne_Cbc) :
            C_bc ⋖ d_ac ⊔ C_bc).eq_or_eq (le_sup_right : C_bc ≤ bc ⊔ C_bc) h_le).resolve_left
            (fun hCbc_eq => hbc_ne_U ((Γ.hU.le_iff.mp (le_inf
              (le_sup_left.trans (hCbc_eq ▸ hCbc_on_q))
              hbc_on |>.trans (inf_comm l q ▸ hlq_eq_U).le)).resolve_left hbc_atom.1))
        have hd_le_ECbc : d_ac ≤ Γ.E ⊔ C_bc :=
          le_sup_left.trans hbcCbc_eq_dCbc.symm.le |>.trans (sup_le hbc_le_ECbc le_sup_right)
        have hECbc_m : (Γ.E ⊔ C_bc) ⊓ m = Γ.E := by
          rw [sup_comm]; exact line_direction hCbc_atom' hCbc_not_m Γ.hE_on_m
        have hd_eq_E : d_ac = Γ.E :=
          (Γ.hE_atom.le_iff.mp (le_inf hd_le_ECbc inf_le_right |>.trans hECbc_m.le)).resolve_left hd_atom.1

        have hC_ne_E : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
        have hE_le_acC : Γ.E ≤ ac ⊔ Γ.C := hd_eq_E ▸ inf_le_left
        have hC_lt_CE : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
          (fun h => hC_ne_E ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_atom.1).symm)
        have hO_ne_C : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
        have hCE_eq_Cac : Γ.C ⊔ Γ.E = Γ.C ⊔ ac :=
          ((atom_covBy_join Γ.hC hac_atom (Ne.symm hac_ne_C)).eq_or_eq hC_lt_CE.le
            (sup_le le_sup_left (sup_comm ac Γ.C ▸ hE_le_acC))).resolve_left (ne_of_gt hC_lt_CE)
        have hCE_eq_CO : Γ.C ⊔ Γ.E = Γ.C ⊔ Γ.O :=
          ((atom_covBy_join Γ.hC Γ.hO (Ne.symm hO_ne_C)).eq_or_eq hC_lt_CE.le
            (sup_le le_sup_left (sup_comm Γ.O Γ.C ▸ (show Γ.E ≤ Γ.O ⊔ Γ.C from inf_le_left)))).resolve_left (ne_of_gt hC_lt_CE)
        have hac_le_OC : ac ≤ Γ.O ⊔ Γ.C :=
          le_sup_right.trans (hCE_eq_Cac.symm.le.trans (hCE_eq_CO.le.trans (sup_comm Γ.C Γ.O).le))
        have hOCl : (Γ.C ⊔ Γ.O) ⊓ l = Γ.O := line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
        exact hac_ne_O ((Γ.hO.le_iff.mp (le_inf (sup_comm Γ.O Γ.C ▸ hac_le_OC) hac_on |>.trans hOCl.le)).resolve_left hac_atom.1)
      have hP_atom : IsAtom P := hP_eq ▸ beta_atom Γ hacbc_atom hacbc_on hacbc_ne_O hacbc_ne_U
      have hP_le_q : P ≤ q := hP_eq ▸ inf_le_left
      have hCbcP_eq_q : C_bc ⊔ P = q := by

        have hCbc_atom' : IsAtom C_bc := hCbc_eq_beta ▸ beta_atom Γ hbc_atom hbc_on hbc_ne_O hbc_ne_U
        have hCbc_le_q : C_bc ≤ q := hCbc_eq_beta ▸ inf_le_left
        have hCbc_lt : C_bc < C_bc ⊔ P := lt_of_le_of_ne le_sup_left
          (fun h => hCbc_ne_P ((hCbc_atom'.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hP_atom.1).symm)
        exact ((line_covers_its_atoms Γ.hU Γ.hC hUC hCbc_atom' hCbc_le_q).eq_or_eq hCbc_lt.le
          (sup_le hCbc_le_q hP_le_q)).resolve_left (ne_of_gt hCbc_lt)
      have hCbcP_m : (C_bc ⊔ P) ⊓ m = Γ.U := by rw [hCbcP_eq_q]; exact hqm_eq_U
      have hCbc_le_bcE : C_bc ≤ bc ⊔ Γ.E := hCbc_eq_beta ▸ inf_le_right
      have hCbc_ne_C'bc : C_bc ≠ C'_bc := by
        intro h
        have hσ_not_q' : ¬ σ ≤ q := by
          intro hσq
          have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
            intro hle'
            have hOCl : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
              rw [sup_comm Γ.O Γ.C, show l = Γ.O ⊔ Γ.U from rfl]
              exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
                line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
            exact Γ.hOU ((Γ.hO.le_iff.mp (le_inf hle' (show Γ.U ≤ l from le_sup_right) |>.trans hOCl.le)).resolve_left Γ.hU.1).symm
          have hq_OC : q ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
            rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm Γ.U Γ.C, sup_inf_assoc_of_le Γ.U (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)]
            have : Γ.U ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
              (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun hh => hU_not_OC (hh ▸ inf_le_right))
            rw [this, sup_bot_eq]
          exact hCσ ((Γ.hC.le_iff.mp (le_inf hσq hσ_on_OC |>.trans hq_OC.le)).resolve_left hσ_atom.1).symm
        have hσ_ne_U' : σ ≠ Γ.U := fun h' => hσ_not_m (h' ▸ le_sup_left)
        have hqσU : q ⊓ (σ ⊔ Γ.U) = Γ.U := by
          rw [show q = Γ.U ⊔ Γ.C from rfl, sup_comm σ Γ.U]
          exact modular_intersection Γ.hU Γ.hC hσ_atom hUC hσ_ne_U'.symm hCσ hσ_not_q'
        exact hCbc_ne_U ((Γ.hU.le_iff.mp (le_inf hCbc_on_q (h ▸ hC'bc_le_σU) |>.trans hqσU.le)).resolve_left hCbc_atom.1)
      have hbc_not_m : ¬ bc ≤ m := fun h => hbc_ne_U (Γ.atom_on_both_eq_U hbc_atom hbc_on h)
      have hbc_ne_E : bc ≠ Γ.E := fun h => hbc_not_m (h ▸ Γ.hE_on_m)
      have hCbc_lt' : C_bc < C_bc ⊔ C'_bc := lt_of_le_of_ne le_sup_left
        (fun h => hCbc_ne_C'bc ((hCbc_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hC'bc_atom.1).symm)
      have hCbcC'bc_eq_bcE : C_bc ⊔ C'_bc = bc ⊔ Γ.E :=
        ((line_covers_its_atoms hbc_atom Γ.hE_atom hbc_ne_E hCbc_atom hCbc_le_bcE).eq_or_eq
          (le_sup_left : C_bc ≤ C_bc ⊔ C'_bc)
          (sup_le hCbc_le_bcE hC'bc_le_bcE)).resolve_left
          (fun h => hCbc_ne_C'bc ((hCbc_atom.le_iff.mp (le_sup_right.trans h.le)).resolve_left hC'bc_atom.1).symm)
      have hCbcC'bc_m : (C_bc ⊔ C'_bc) ⊓ m = Γ.E := by
        rw [hCbcC'bc_eq_bcE]; exact line_direction hbc_atom hbc_not_m Γ.hE_on_m

      have hPE_eq : P ⊔ Γ.E = coord_add Γ ac bc ⊔ Γ.E := by
        rw [hP_eq]; apply le_antisymm
        · exact sup_le inf_le_right le_sup_right
        · have hqE_eq_π : q ⊔ Γ.E = π := by
            have hE_not_q : ¬ Γ.E ≤ q := fun hle =>
              Γ.hEU ((Γ.hU.le_iff.mp (hqm_eq_U ▸ le_inf hle Γ.hE_on_m)).resolve_left Γ.hE_atom.1)
            have hq_covBy_π : q ⋖ π := by
              have hmq : m ⊔ q = π := by
                have : m ⊔ q = m ⊔ Γ.C := by
                  show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
                  rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
                rw [this]; exact (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
                  (sup_le hm_le_π Γ.hC_plane)).resolve_left
                  (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
              exact hmq ▸ covBy_sup_of_inf_covBy_left (inf_comm m q ▸ hqm_eq_U ▸ atom_covBy_join Γ.hU Γ.hV hUV)
            exact (hq_covBy_π.eq_or_eq (lt_of_le_of_ne le_sup_left (fun h => hE_not_q (le_sup_right.trans h.symm.le))).le
              (sup_le (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane) (Γ.hE_on_m.trans hm_le_π))).resolve_left
              (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => hE_not_q (le_sup_right.trans h.symm.le))))
          rw [sup_comm (q ⊓ (coord_add Γ ac bc ⊔ Γ.E)) Γ.E,
              (sup_inf_assoc_of_le q (le_sup_right : Γ.E ≤ coord_add Γ ac bc ⊔ Γ.E)).symm,
              sup_comm Γ.E q, hqE_eq_π]
          exact le_inf (sup_le (hacbc_on.trans le_sup_left) (Γ.hE_on_m.trans hm_le_π)) (le_refl _)

      have hRHS : parallelogram_completion C_bc P C'_bc m =
          (σ ⊔ Γ.U) ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by
        show (C'_bc ⊔ (C_bc ⊔ P) ⊓ m) ⊓ (P ⊔ (C_bc ⊔ C'_bc) ⊓ m) =
            (σ ⊔ Γ.U) ⊓ (coord_add Γ ac bc ⊔ Γ.E)
        rw [hCbcP_m, hC'bcU_eq_σU, hCbcC'bc_m, hPE_eq]
      rw [← hpc_C'bc_eq, hwd, hRHS]

    have hsc_eq_acbc : sc = coord_add Γ ac bc := by

      have h_eq : (σ ⊔ Γ.U) ⊓ (sc ⊔ Γ.E) = (σ ⊔ Γ.U) ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by
        rw [← h_mki_s, hC'sc_eq_acbc]

      have hE_not_σU : ¬ Γ.E ≤ σ ⊔ Γ.U := by
        intro hle

        have hσU_dir : (σ ⊔ Γ.U) ⊓ m = Γ.U :=
          line_direction hσ_atom hσ_not_m (le_sup_left : Γ.U ≤ m)
        have hE_le_U : Γ.E ≤ Γ.U := (le_inf hle Γ.hE_on_m).trans hσU_dir.le
        exact Γ.hEU ((Γ.hU.le_iff.mp hE_le_U).resolve_left Γ.hE_atom.1)

      by_contra hne

      have h_lines_ne : sc ⊔ Γ.E ≠ coord_add Γ ac bc ⊔ Γ.E := by
        intro heq

        have hsc_l : (sc ⊔ Γ.E) ⊓ l = sc := by
          change (sc ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = sc; rw [sup_comm sc Γ.E]
          exact line_direction Γ.hE_atom Γ.hE_not_l hsc_on
        have hacbc_l : (coord_add Γ ac bc ⊔ Γ.E) ⊓ l = coord_add Γ ac bc := by
          change (coord_add Γ ac bc ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = coord_add Γ ac bc
          rw [sup_comm (coord_add Γ ac bc) Γ.E]
          exact line_direction Γ.hE_atom Γ.hE_not_l hacbc_on
        exact hne (hsc_l.symm.trans (heq ▸ hacbc_l))

      have hC'sc_le_both : C'_sc ≤ (sc ⊔ Γ.E) ⊓ (coord_add Γ ac bc ⊔ Γ.E) :=
        le_inf hC'sc_le_scE (hC'sc_eq_acbc ▸ inf_le_right)

      have h_meet_eq_E : (sc ⊔ Γ.E) ⊓ (coord_add Γ ac bc ⊔ Γ.E) = Γ.E := by

        have hsc_ne_E : sc ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hsc_on)
        have hacbc_ne_E : coord_add Γ ac bc ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hacbc_on)
        have hsc_ne_acbc : sc ≠ coord_add Γ ac bc := hne
        have hacbc_not_le : ¬ coord_add Γ ac bc ≤ Γ.E ⊔ sc := by
          intro hle
          have hscE_l : (sc ⊔ Γ.E) ⊓ l = sc := by
            change (sc ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = sc
            rw [sup_comm sc Γ.E]
            exact line_direction Γ.hE_atom Γ.hE_not_l hsc_on
          have hacbc_le : coord_add Γ ac bc ≤ sc :=
            (le_inf (sup_comm Γ.E sc ▸ hle) hacbc_on).trans hscE_l.le
          exact hsc_ne_acbc ((hsc_atom.le_iff.mp hacbc_le).resolve_left hacbc_atom.1).symm
        rw [sup_comm sc Γ.E, sup_comm (coord_add Γ ac bc) Γ.E]
        exact modular_intersection Γ.hE_atom hsc_atom hacbc_atom hsc_ne_E.symm
          hacbc_ne_E.symm hsc_ne_acbc hacbc_not_le

      have hC'sc_le_E : C'_sc ≤ Γ.E := hC'sc_le_both.trans h_meet_eq_E.le
      exact hC'sc_not_m ((Γ.hE_atom.le_iff.mp hC'sc_le_E).resolve_left hC'sc_atom.1 ▸ Γ.hE_on_m)

    show C_sc = q ⊓ (ac ⊔ e_bc)
    rw [show C_sc = q ⊓ (sc ⊔ Γ.E) from rfl, hsc_eq_acbc, ← hq_eq]

  have h_ki_mul : parallelogram_completion Γ.O ac C_bc m =
      parallelogram_completion Γ.O (coord_add Γ ac bc) Γ.C m :=
    key_identity Γ ac bc hac_atom hbc_atom hac_on hbc_on hac_ne_O hbc_ne_O
      hac_ne_U hbc_ne_U hac_ne_bc R hR hR_not h_irred

  have pc_eq_beta : ∀ (x : L), Γ.O ⊔ x = l →
      parallelogram_completion Γ.O x Γ.C m = q ⊓ (x ⊔ Γ.E) := by
    intro x hOx_eq_l
    unfold parallelogram_completion

    show (Γ.C ⊔ (Γ.O ⊔ x) ⊓ m) ⊓ (x ⊔ (Γ.O ⊔ Γ.C) ⊓ m) = q ⊓ (x ⊔ Γ.E)
    rw [hOx_eq_l, hlm_eq_U]
    rw [show Γ.C ⊔ Γ.U = q from by rw [show q = Γ.U ⊔ Γ.C from rfl]; exact sup_comm _ _]
    rfl

  have hObc_eq_l : Γ.O ⊔ bc = l := by
    have hO_lt : Γ.O < Γ.O ⊔ bc := lt_of_le_of_ne le_sup_left
      (fun h => hbc_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hbc_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hbc_on)).resolve_left (ne_of_gt hO_lt)
  have hCbc_eq_beta : C_bc = q ⊓ (bc ⊔ Γ.E) := pc_eq_beta bc hObc_eq_l

  have hOacbc_eq_l : Γ.O ⊔ coord_add Γ ac bc = l := by
    have hO_lt : Γ.O < Γ.O ⊔ coord_add Γ ac bc := lt_of_le_of_ne le_sup_left
      (fun h => hacbc_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hacbc_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hacbc_on)).resolve_left (ne_of_gt hO_lt)
  have hCacbc_eq_beta : parallelogram_completion Γ.O (coord_add Γ ac bc) Γ.C m =
      q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := pc_eq_beta (coord_add Γ ac bc) hOacbc_eq_l

  have h_beta_eq : C_sc = q ⊓ (coord_add Γ ac bc ⊔ Γ.E) := by
    rw [h_core, ← hpc_eq', h_ki_mul, hCacbc_eq_beta]

  have recover : ∀ (x : L), IsAtom x → x ≤ l → x ≠ Γ.O → x ≠ Γ.U →
      (q ⊓ (x ⊔ Γ.E) ⊔ Γ.E) ⊓ l = x := by
    intro x hx hx_l hx_ne_O hx_ne_U

    have hbx_le_xE : q ⊓ (x ⊔ Γ.E) ⊔ Γ.E ≤ x ⊔ Γ.E :=
      sup_le (inf_le_right) le_sup_right
    have hxE_le_bxE : x ⊔ Γ.E ≤ q ⊓ (x ⊔ Γ.E) ⊔ Γ.E := by

      have hqE_eq_π : q ⊔ Γ.E = π := by
        have hE_not_q : ¬ Γ.E ≤ q := fun hle =>
          Γ.hEU ((Γ.hU.le_iff.mp (hqm_eq_U ▸ le_inf hle Γ.hE_on_m)).resolve_left Γ.hE_atom.1)
        have hq_covBy_π : q ⋖ π := by
          have h_inf : m ⊓ q ⋖ m := by
            rw [inf_comm, hqm_eq_U]
            exact atom_covBy_join Γ.hU Γ.hV hUV
          have hmq : m ⊔ q = π := by
            have : m ⊔ q = m ⊔ Γ.C := by
              show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
              rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
            rw [this]
            exact (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
              (sup_le hm_le_π Γ.hC_plane)).resolve_left
              (ne_of_gt (lt_of_le_of_ne le_sup_left
                (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
          exact hmq ▸ covBy_sup_of_inf_covBy_left h_inf
        have hq_lt : q < q ⊔ Γ.E := lt_of_le_of_ne le_sup_left
          (fun h => hE_not_q (le_sup_right.trans h.symm.le))
        exact (hq_covBy_π.eq_or_eq hq_lt.le
          (sup_le (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
            (Γ.hE_on_m.trans hm_le_π))).resolve_left (ne_of_gt hq_lt)

      have hxE_le_π : x ⊔ Γ.E ≤ π := sup_le (hx_l.trans le_sup_left) (Γ.hE_on_m.trans hm_le_π)

      have h_mod : Γ.E ⊔ q ⊓ (x ⊔ Γ.E) = (Γ.E ⊔ q) ⊓ (x ⊔ Γ.E) :=
        (sup_inf_assoc_of_le q (le_sup_right : Γ.E ≤ x ⊔ Γ.E)).symm
      rw [sup_comm (q ⊓ (x ⊔ Γ.E)) Γ.E, h_mod, sup_comm Γ.E q, hqE_eq_π]
      exact le_inf hxE_le_π (le_refl _)
    have h_eq : q ⊓ (x ⊔ Γ.E) ⊔ Γ.E = x ⊔ Γ.E := le_antisymm hbx_le_xE hxE_le_bxE
    rw [h_eq, sup_inf_assoc_of_le Γ.E hx_l, hE_inf_l, sup_bot_eq]

  calc sc
      = (q ⊓ (sc ⊔ Γ.E) ⊔ Γ.E) ⊓ l := (recover sc hsc_atom hsc_on hsc_ne_O hsc_ne_U).symm
    _ = (q ⊓ (coord_add Γ ac bc ⊔ Γ.E) ⊔ Γ.E) ⊓ l := by
        show (C_sc ⊔ Γ.E) ⊓ l = (q ⊓ (coord_add Γ ac bc ⊔ Γ.E) ⊔ Γ.E) ⊓ l
        rw [h_beta_eq]
    _ = coord_add Γ ac bc := recover (coord_add Γ ac bc) hacbc_atom hacbc_on hacbc_ne_O hacbc_ne_U
/-- info: 'Foam.Bridges.coord_mul_right_distrib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_mul_right_distrib

end Foam.Bridges
