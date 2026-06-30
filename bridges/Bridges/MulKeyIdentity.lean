import Bridges.Dilation
namespace Foam.Bridges
universe u
variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

theorem beta_atom (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    IsAtom ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) := by
  set q := Γ.U ⊔ Γ.C
  set m := Γ.U ⊔ Γ.V
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  have ha_ne_E : a ≠ Γ.E := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on (h ▸ Γ.hE_on_m))
  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)

  have hqm_eq_U : q ⊓ m = Γ.U := by
    change (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [this, sup_bot_eq]
  have hq_covBy : q ⋖ π := by
    have h_inf : m ⊓ q ⋖ m := by rw [inf_comm, hqm_eq_U]; exact atom_covBy_join Γ.hU Γ.hV hUV
    have h1 := covBy_sup_of_inf_covBy_left h_inf
    have hmq : m ⊔ q = m ⊔ Γ.C := by
      show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
      rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
    have hmC : m ⊔ Γ.C = π :=
      (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
        (sup_le Γ.m_covBy_π.le Γ.hC_plane)).resolve_left
        (ne_of_gt (lt_of_le_of_ne le_sup_left
          (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
    rwa [hmq, hmC] at h1

  have haE_covBy : a ⊔ Γ.E ⋖ π := by
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
    have h_covBy := line_covBy_plane ha Γ.hE_atom Γ.hO ha_ne_E ha_ne_O
      (fun h => Γ.hE_not_l (h ▸ le_sup_left)) hO_not_aE

    have haEO_eq : a ⊔ Γ.E ⊔ Γ.O = π := by
      have hl_le : Γ.O ⊔ Γ.U ≤ a ⊔ Γ.E ⊔ Γ.O := by
        have hOa_le : Γ.O ⊔ a ≤ a ⊔ Γ.E ⊔ Γ.O :=
          sup_le le_sup_right (le_sup_left.trans le_sup_left)
        have hOa_eq : Γ.O ⊔ a = Γ.O ⊔ Γ.U :=
          ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq
            (lt_of_le_of_ne le_sup_left (fun h => ha_ne_O
              ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))).le
            (sup_le le_sup_left ha_on)).resolve_left
            (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => ha_ne_O
              ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))))
        exact hOa_eq ▸ hOa_le
      have hE_le : Γ.E ≤ a ⊔ Γ.E ⊔ Γ.O := le_sup_right.trans le_sup_left

      have hl_lt_lE : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h => Γ.hE_not_l (le_sup_right.trans h.symm.le))
      have hlE_eq : (Γ.O ⊔ Γ.U) ⊔ Γ.E = π := by
        have hl_covBy : Γ.O ⊔ Γ.U ⋖ π := by
          have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
            (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
          exact show Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V from
            sup_comm (Γ.O ⊔ Γ.U) Γ.V ▸ covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
        exact (hl_covBy.eq_or_eq hl_lt_lE.le
          (sup_le le_sup_left (Γ.hE_on_m.trans Γ.m_covBy_π.le))).resolve_left
          (ne_of_gt hl_lt_lE)
      exact le_antisymm
        (sup_le (sup_le (ha_on.trans le_sup_left) (Γ.hE_on_m.trans Γ.m_covBy_π.le))
          (show Γ.O ≤ π from le_sup_left.trans le_sup_left))
        (hlE_eq ▸ sup_le hl_le hE_le)
    rwa [haEO_eq] at h_covBy

  have hU_not_aE : ¬ Γ.U ≤ a ⊔ Γ.E := by
    intro h
    have ha_lt : a < a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h' => ha_ne_U ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
    have haU_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt.le
        (sup_le le_sup_left h)).resolve_left (ne_of_gt ha_lt)
    exact Γ.hE_not_l (le_sup_right.trans (haU_eq.symm.le.trans (sup_le ha_on le_sup_right)))
  exact line_meets_m_at_atom Γ.hU Γ.hC hUC
    (sup_le (le_sup_right.trans (le_sup_left : Γ.O ⊔ Γ.U ≤ π)) Γ.hC_plane)
    haE_covBy.le haE_covBy hU_not_aE

theorem beta_not_l (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    ¬ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.O ⊔ Γ.U := by
  set C_a := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)
  have hCa_atom := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have ha_ne_E : a ≠ Γ.E := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on (h ▸ Γ.hE_on_m))
  have ha_not_m : ¬ a ≤ Γ.U ⊔ Γ.V := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  intro h
  have hlq : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
    rw [inf_comm, sup_comm Γ.U Γ.C]
    exact line_direction Γ.hC Γ.hC_not_l (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U)
  have hCa_eq_U : C_a = Γ.U :=
    (Γ.hU.le_iff.mp (le_inf h (inf_le_left : C_a ≤ Γ.U ⊔ Γ.C) |>.trans hlq.le)).resolve_left
      hCa_atom.1
  have hU_le_aE : Γ.U ≤ a ⊔ Γ.E := hCa_eq_U ▸ (inf_le_right : C_a ≤ a ⊔ Γ.E)
  have ha_lt : a < a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
    (fun h' => ha_ne_U ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
  have haU_eq : a ⊔ Γ.U = a ⊔ Γ.E :=
    ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt.le
      (sup_le le_sup_left hU_le_aE)).resolve_left (ne_of_gt ha_lt)
  exact Γ.hE_not_l (le_sup_right.trans (haU_eq.symm.le.trans (sup_le ha_on le_sup_right)))

theorem beta_plane (Γ : CoordSystem L)
    {a : L} (_ha_on : a ≤ Γ.O ⊔ Γ.U) :
    (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
  inf_le_left.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)

theorem dilation_mul_key_identity (Γ : CoordSystem L)
    (a c : L) (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    let C_a := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)
    let σ := dilation_ext Γ c Γ.C
    let ac := coord_mul Γ a c
    dilation_ext Γ c C_a = (σ ⊔ Γ.U) ⊓ (ac ⊔ Γ.E) := by
  intro C_a σ ac

  by_cases hcI : c = Γ.I
  ·
    subst hcI
    have hσ_eq : σ = Γ.C := dilation_ext_identity Γ Γ.hC Γ.hC_plane Γ.hC_not_l
    have hac_eq : ac = a := coord_mul_right_one Γ a ha ha_on
    rw [hσ_eq, hac_eq, sup_comm Γ.C Γ.U]
    exact dilation_ext_identity Γ (beta_atom Γ ha ha_on ha_ne_O ha_ne_U)
      (beta_plane Γ ha_on) (beta_not_l Γ ha ha_on ha_ne_O ha_ne_U)

  set l := Γ.O ⊔ Γ.U with hl_def
  set m := Γ.U ⊔ Γ.V with hm_def
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def

  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have ha_ne_E : a ≠ Γ.E := fun h => ha_not_m (h ▸ Γ.hE_on_m)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hIC : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)

  have hl_covBy : l ⋖ π := by
    change Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
    have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have h := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from sup_comm _ _] at h

  have hOa_eq_l : Γ.O ⊔ a = l := by
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq
      (lt_of_le_of_ne le_sup_left (fun h => ha_ne_O
        ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))).le
      (sup_le le_sup_left ha_on)).resolve_left
      (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h => ha_ne_O
        ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))))

  have hqm_eq_U : (Γ.U ⊔ Γ.C) ⊓ m = Γ.U := by
    change (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    calc (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U ⊔ Γ.C ⊓ (Γ.U ⊔ Γ.V) :=
          sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)
      _ = Γ.U := by
          have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
            (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
          rw [this, sup_bot_eq]

  have haE_covBy : a ⊔ Γ.E ⋖ π := by
    have hO_not_aE : ¬ Γ.O ≤ a ⊔ Γ.E := by
      intro hO_le
      have hl_le : l ≤ a ⊔ Γ.E := hOa_eq_l ▸ sup_le hO_le le_sup_left
      have ha_lt_l : a < l := (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt
      exact Γ.hE_not_l (le_sup_right.trans
        (((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_on hl_le).resolve_left
          (ne_of_gt ha_lt_l)).symm.le)
    have haEO_eq : a ⊔ Γ.E ⊔ Γ.O = π := by
      have hl_le : l ≤ a ⊔ Γ.E ⊔ Γ.O := by
        rw [← hOa_eq_l]; exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
      have hl_lt : l < l ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h' => Γ.hE_not_l (le_sup_right.trans h'.symm.le))
      have hlE_eq : l ⊔ Γ.E = π :=
        (hl_covBy.eq_or_eq hl_lt.le (sup_le hl_covBy.le (Γ.hE_on_m.trans Γ.m_covBy_π.le))).resolve_left
          (ne_of_gt hl_lt)
      exact le_antisymm
        (sup_le (sup_le (ha_on.trans le_sup_left) (Γ.hE_on_m.trans Γ.m_covBy_π.le))
          (show Γ.O ≤ π from le_sup_left.trans le_sup_left))
        (hlE_eq ▸ sup_le hl_le (le_sup_right.trans le_sup_left))
    rw [← haEO_eq]
    exact line_covBy_plane ha Γ.hE_atom Γ.hO ha_ne_E ha_ne_O
      (fun h' => Γ.hE_not_l (h' ▸ le_sup_left)) hO_not_aE

  set d_a := (a ⊔ Γ.C) ⊓ m with hda_def
  have hda_atom : IsAtom d_a :=
    line_meets_m_at_atom ha Γ.hC ha_ne_C
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane)
      Γ.m_covBy_π.le Γ.m_covBy_π ha_not_m

  have hCa_le_q : C_a ≤ Γ.U ⊔ Γ.C := inf_le_left
  have hCa_le_aE : C_a ≤ a ⊔ Γ.E := inf_le_right
  have hCa_atom : IsAtom C_a := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hCa_not_l : ¬ C_a ≤ l := beta_not_l Γ ha ha_on ha_ne_O ha_ne_U
  have hCa_not_m : ¬ C_a ≤ m := by
    intro h
    have hCa_eq_E : C_a = Γ.E :=
      (Γ.hE_atom.le_iff.mp (le_inf hCa_le_aE h |>.trans
        (line_direction ha ha_not_m Γ.hE_on_m).le)).resolve_left hCa_atom.1
    have hE_le_q : Γ.E ≤ Γ.U ⊔ Γ.C := hCa_eq_E ▸ hCa_le_q
    exact Γ.hEU ((Γ.hU.le_iff.mp (le_inf hE_le_q Γ.hE_on_m |>.trans
      hqm_eq_U.le)).resolve_left Γ.hE_atom.1)
  have hCa_plane : C_a ≤ π := beta_plane Γ ha_on
  have hCa_ne_O : C_a ≠ Γ.O := fun h => hCa_not_l (h ▸ le_sup_left)
  have hCa_ne_I : C_a ≠ Γ.I := fun h => hCa_not_l (h ▸ Γ.hI_on)
  have hCa_ne_U : C_a ≠ Γ.U := fun h => hCa_not_l (h ▸ le_sup_right)
  have hCa_ne_C : C_a ≠ Γ.C := by
    intro h

    have hC_le_aE : Γ.C ≤ a ⊔ Γ.E := h ▸ hCa_le_aE
    have ha_lt_aC : a < a ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h' => ha_ne_C ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hC.1).symm)
    have haC_eq_aE : a ⊔ Γ.C = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt_aC.le
        (sup_le le_sup_left hC_le_aE)).resolve_left (ne_of_gt ha_lt_aC)

    have hda_eq_E : d_a = Γ.E := by
      have h1 : d_a = (a ⊔ Γ.E) ⊓ m := by rw [← haC_eq_aE]
      rw [h1]; exact line_direction ha ha_not_m Γ.hE_on_m

    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle

      have hl_le : l ≤ a ⊔ Γ.C := hOa_eq_l ▸ (sup_le hle le_sup_left : Γ.O ⊔ a ≤ a ⊔ Γ.C)
      have ha_lt_l : a < l := (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt
      exact Γ.hC_not_l (le_sup_right.trans
        (((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq ha_on hl_le).resolve_left
          (ne_of_gt ha_lt_l)).symm.le)
    have hE_le_C : Γ.E ≤ Γ.C := by
      have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := hda_eq_E ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
      have hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C := inf_le_left
      have hmod := modular_intersection Γ.hC ha Γ.hO ha_ne_C.symm hOC.symm ha_ne_O
        (show ¬ Γ.O ≤ Γ.C ⊔ a from sup_comm a Γ.C ▸ hO_not_aC)

      calc Γ.E ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.O) :=
            le_inf (sup_comm a Γ.C ▸ hE_le_aC) (sup_comm Γ.O Γ.C ▸ hE_le_OC)
        _ = Γ.C := hmod
    exact (fun hEC : Γ.E ≠ Γ.C => hEC ((Γ.hC.le_iff.mp hE_le_C).resolve_left Γ.hE_atom.1))
      (fun h' => Γ.hC_not_m (h' ▸ Γ.hE_on_m))

  have hσ_atom : IsAtom σ :=
    dilation_ext_atom Γ Γ.hC hc hc_on hc_ne_O hc_ne_U
      Γ.hC_plane Γ.hC_not_l (Ne.symm hOC) (Ne.symm hIC) Γ.hC_not_m
  have hσ_on_OC : σ ≤ Γ.O ⊔ Γ.C := by
    change (Γ.O ⊔ Γ.C) ⊓ (c ⊔ (Γ.I ⊔ Γ.C) ⊓ m) ≤ Γ.O ⊔ Γ.C; exact inf_le_left
  have hσ_on_cEI : σ ≤ c ⊔ Γ.E_I := by
    change (Γ.O ⊔ Γ.C) ⊓ (c ⊔ (Γ.I ⊔ Γ.C) ⊓ m) ≤ c ⊔ Γ.E_I; exact inf_le_right
  have hσ_plane : σ ≤ π := dilation_ext_plane Γ Γ.hC hc hc_on Γ.hC_plane

  have hσ_not_m : ¬ σ ≤ m := by
    change ¬ dilation_ext Γ c Γ.C ≤ Γ.U ⊔ Γ.V
    exact dilation_ext_not_m Γ Γ.hC hc hc_on hc_ne_O hc_ne_U
      Γ.hC_plane Γ.hC_not_m Γ.hC_not_l (Ne.symm hOC) (Ne.symm hIC) hcI

  have hσ_not_l : ¬ σ ≤ l := by
    intro h
    have hOCl : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O := by
      change (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.O
      rw [sup_comm Γ.O Γ.C]
      exact inf_comm (Γ.O ⊔ Γ.U) (Γ.C ⊔ Γ.O) ▸
        line_direction Γ.hC Γ.hC_not_l (show Γ.O ≤ l from le_sup_left)
    have hσ_eq_O : σ = Γ.O := (Γ.hO.le_iff.mp ((le_inf hσ_on_OC h).trans hOCl.le)).resolve_left hσ_atom.1
    have hO_le_cEI : Γ.O ≤ c ⊔ Γ.E_I := hσ_eq_O.symm ▸ hσ_on_cEI
    have hcEI_l : (c ⊔ Γ.E_I) ⊓ l = c := by
      change (c ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = c; rw [sup_comm c Γ.E_I]
      exact line_direction Γ.hE_I_atom Γ.hE_I_not_l hc_on
    exact hc_ne_O ((hc.le_iff.mp (le_inf hO_le_cEI (show Γ.O ≤ l from le_sup_left)
      |>.trans hcEI_l.le)).resolve_left Γ.hO.1).symm

  by_cases haI : a = Γ.I
  ·
    subst haI

    have hac_eq : ac = c := coord_mul_left_one Γ c hc hc_on hc_ne_U
    rw [hac_eq]

    have hICa_eq_IE : Γ.I ⊔ C_a = Γ.I ⊔ Γ.E := by
      have h_lt : Γ.I < Γ.I ⊔ C_a := lt_of_le_of_ne le_sup_left
        (fun h => hCa_ne_I ((Γ.hI.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hCa_atom.1))
      exact ((atom_covBy_join Γ.hI Γ.hE_atom ha_ne_E).eq_or_eq h_lt.le
        (sup_le le_sup_left (inf_le_right : C_a ≤ Γ.I ⊔ Γ.E))).resolve_left (ne_of_gt h_lt)

    have hdir : (Γ.I ⊔ C_a) ⊓ m = Γ.E := by
      rw [hICa_eq_IE]; exact line_direction Γ.hI ha_not_m Γ.hE_on_m

    have hDE_eq : dilation_ext Γ c C_a = (Γ.O ⊔ C_a) ⊓ (c ⊔ Γ.E) := by
      show (Γ.O ⊔ C_a) ⊓ (c ⊔ (Γ.I ⊔ C_a) ⊓ m) = (Γ.O ⊔ C_a) ⊓ (c ⊔ Γ.E); rw [hdir]

    have hDE_atom : IsAtom (dilation_ext Γ c C_a) :=
      dilation_ext_atom Γ hCa_atom hc hc_on hc_ne_O hc_ne_U hCa_plane hCa_not_l
        hCa_ne_O hCa_ne_I hCa_not_m

    have hCa_not_OC : ¬ C_a ≤ Γ.O ⊔ Γ.C := by
      intro hle

      have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
        intro h'; exact Γ.hC_not_l (le_sup_right.trans
          (((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
            (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU Γ.hO le_sup_left).lt.le
            (sup_le le_sup_left h')).resolve_left
            (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU Γ.hO le_sup_left).lt)).symm.le)
      have hOCq : (Γ.C ⊔ Γ.O) ⊓ (Γ.C ⊔ Γ.U) = Γ.C :=
        modular_intersection Γ.hC Γ.hO Γ.hU hOC.symm hUC.symm Γ.hOU
          (sup_comm Γ.O Γ.C ▸ hU_not_OC)
      exact hCa_ne_C ((Γ.hC.le_iff.mp ((le_inf hle hCa_le_q).trans
        (show (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C) ≤ Γ.C from
          sup_comm Γ.O Γ.C ▸ sup_comm Γ.U Γ.C ▸ hOCq.le))).resolve_left hCa_atom.1)

    have hσ_ne_DE : σ ≠ dilation_ext Γ c C_a := by
      intro h
      have h1 : σ ≤ Γ.O ⊔ C_a := by rw [h]; unfold dilation_ext; exact inf_le_left
      have hmod : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ C_a) = Γ.O :=
        modular_intersection Γ.hO Γ.hC hCa_atom hOC hCa_ne_O.symm
          (Ne.symm hCa_ne_C) hCa_not_OC
      exact hσ_not_l (((Γ.hO.le_iff.mp ((le_inf hσ_on_OC h1).trans hmod.le)).resolve_left
        hσ_atom.1) ▸ (show Γ.O ≤ l from le_sup_left))

    have hCCa_eq_q : Γ.C ⊔ C_a = Γ.U ⊔ Γ.C := by
      have hC_lt : Γ.C < Γ.C ⊔ C_a := lt_of_le_of_ne le_sup_left
        (fun h => hCa_ne_C ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hCa_atom.1))
      exact ((sup_comm Γ.C Γ.U ▸ atom_covBy_join Γ.hC Γ.hU (Ne.symm hUC) :
        Γ.C ⋖ Γ.U ⊔ Γ.C).eq_or_eq hC_lt.le
        (sup_le le_sup_right hCa_le_q)).resolve_left (ne_of_gt hC_lt)

    have hDPD := dilation_preserves_direction Γ Γ.hC hCa_atom c hc hc_on hc_ne_O hc_ne_U
      Γ.hC_plane hCa_plane Γ.hC_not_m hCa_not_m Γ.hC_not_l hCa_not_l
      (Ne.symm hOC) hCa_ne_O (Ne.symm hCa_ne_C) (Ne.symm hIC) hCa_ne_I
      hσ_ne_DE R hR hR_not h_irred

    rw [hCCa_eq_q, hqm_eq_U] at hDPD

    have hU_le_σDE : Γ.U ≤ σ ⊔ dilation_ext Γ c C_a :=
      (le_of_eq hDPD).trans inf_le_left

    have hσ_ne_U : σ ≠ Γ.U := fun h => hσ_not_l (h ▸ (le_sup_right : Γ.U ≤ l))
    have hσU_eq_σDE : σ ⊔ Γ.U = σ ⊔ dilation_ext Γ c C_a := by
      have hσ_lt : σ < σ ⊔ Γ.U := lt_of_le_of_ne le_sup_left
        (fun h => hσ_ne_U ((hσ_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          Γ.hU.1).symm)
      exact ((atom_covBy_join hσ_atom hDE_atom hσ_ne_DE).eq_or_eq hσ_lt.le
        (sup_le le_sup_left hU_le_σDE)).resolve_left (ne_of_gt hσ_lt)

    have hDE_le_σU : dilation_ext Γ c C_a ≤ σ ⊔ Γ.U :=
      le_sup_right.trans hσU_eq_σDE.symm.le

    have hDE_le_cE : dilation_ext Γ c C_a ≤ c ⊔ Γ.E :=
      hDE_eq ▸ inf_le_right

    have hDE_le : dilation_ext Γ c C_a ≤ (σ ⊔ Γ.U) ⊓ (c ⊔ Γ.E) :=
      le_inf hDE_le_σU hDE_le_cE

    have hRHS_atom : IsAtom ((σ ⊔ Γ.U) ⊓ (c ⊔ Γ.E)) := by
      apply line_height_two hσ_atom Γ.hU hσ_ne_U
      · exact lt_of_lt_of_le hDE_atom.bot_lt hDE_le
      · apply lt_of_le_of_ne inf_le_left; intro heq

        have hσU_le : σ ⊔ Γ.U ≤ c ⊔ Γ.E := inf_eq_left.mp heq
        have hU_le_c : Γ.U ≤ c := by
          have h1 : Γ.U ≤ (c ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) :=
            le_inf (le_sup_right.trans hσU_le) le_sup_right
          rw [sup_comm c Γ.E] at h1
          exact h1.trans (line_direction Γ.hE_atom Γ.hE_not_l hc_on).le
        exact hc_ne_U ((hc.le_iff.mp hU_le_c).resolve_left Γ.hU.1).symm

    exact (hRHS_atom.le_iff.mp hDE_le).resolve_left hDE_atom.1

  set G := (a ⊔ Γ.E) ⊓ (Γ.I ⊔ Γ.C) with hG_def
  have hG_le_aE : G ≤ a ⊔ Γ.E := inf_le_left
  have hG_le_IC : G ≤ Γ.I ⊔ Γ.C := inf_le_right
  have hG_plane : G ≤ π := inf_le_left.trans haE_covBy.le

  have ha_not_IC : ¬ a ≤ Γ.I ⊔ Γ.C := by
    intro h
    have hlIC : (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.C) = Γ.I := by
      rw [inf_comm, sup_comm Γ.I Γ.C]
      exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on
    exact haI ((Γ.hI.le_iff.mp ((le_inf ha_on h).trans hlIC.le)).resolve_left ha.1)
  have hIC_covBy : Γ.I ⊔ Γ.C ⋖ π := by
    have hO_not_IC : ¬ Γ.O ≤ Γ.I ⊔ Γ.C := by
      intro h
      have hlIC : (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.C) = Γ.I := by
        rw [inf_comm, sup_comm Γ.I Γ.C]
        exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on
      exact Γ.hOI ((Γ.hI.le_iff.mp ((le_inf (show Γ.O ≤ Γ.O ⊔ Γ.U from le_sup_left) h).trans
        hlIC.le)).resolve_left Γ.hO.1)
    have hOI_eq_l : Γ.O ⊔ Γ.I = l :=
      ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq
        (lt_of_le_of_ne le_sup_left (fun h' => Γ.hOI
          ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hI.1).symm)).le
        (sup_le le_sup_left Γ.hI_on)).resolve_left
        (ne_of_gt (lt_of_le_of_ne le_sup_left (fun h' => Γ.hOI
          ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hI.1).symm)))
    have h_covBy_ICO := line_covBy_plane Γ.hI Γ.hC Γ.hO hIC (Ne.symm Γ.hOI)
      (Ne.symm hOC) hO_not_IC

    have hICO_eq : Γ.I ⊔ Γ.C ⊔ Γ.O = π := by
      have h_le_π : Γ.I ⊔ Γ.C ⊔ Γ.O ≤ π :=
        sup_le (sup_le (Γ.hI_on.trans le_sup_left) Γ.hC_plane) (show Γ.O ≤ π from le_sup_left.trans le_sup_left)
      have hIC_lt : Γ.I ⊔ Γ.C < Γ.I ⊔ Γ.C ⊔ Γ.O := h_covBy_ICO.lt
      exact le_antisymm h_le_π (by

        have hl_le : l ≤ Γ.I ⊔ Γ.C ⊔ Γ.O :=
          hOI_eq_l ▸ sup_le le_sup_right (le_sup_left.trans le_sup_left)
        have hl_lt : l < Γ.I ⊔ Γ.C ⊔ Γ.O := lt_of_le_of_ne hl_le
          (fun h' => Γ.hC_not_l ((le_sup_right.trans le_sup_left).trans h'.symm.le))
        exact ((hl_covBy.eq_or_eq hl_lt.le h_le_π).resolve_left (ne_of_gt hl_lt)).symm.le)
    rwa [hICO_eq] at h_covBy_ICO
  have hG_atom : IsAtom G :=
    line_meets_m_at_atom ha Γ.hE_atom ha_ne_E
      (sup_le (ha_on.trans le_sup_left) (Γ.hE_on_m.trans Γ.m_covBy_π.le))
      hIC_covBy.le hIC_covBy ha_not_IC
  have hG_not_l : ¬ G ≤ l := by
    intro h
    have hlIC : (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.C) = Γ.I := by
      rw [inf_comm, sup_comm Γ.I Γ.C]
      exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on
    have hG_eq_I : G = Γ.I :=
      (Γ.hI.le_iff.mp ((le_inf h hG_le_IC).trans hlIC.le)).resolve_left hG_atom.1
    have hI_le_aE : Γ.I ≤ a ⊔ Γ.E := hG_eq_I ▸ hG_le_aE
    have ha_lt_aI : a < a ⊔ Γ.I := lt_of_le_of_ne le_sup_left
      (fun h' => haI ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hI.1).symm)
    have haI_eq_aE : a ⊔ Γ.I = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt_aI.le
        (sup_le le_sup_left hI_le_aE)).resolve_left (ne_of_gt ha_lt_aI)
    exact Γ.hE_not_l (le_sup_right.trans (haI_eq_aE.symm.le.trans (sup_le ha_on Γ.hI_on)))
  have hG_not_m : ¬ G ≤ m := by
    intro h
    have hG_eq_E : G = Γ.E :=
      (Γ.hE_atom.le_iff.mp (le_inf hG_le_aE h |>.trans
        (line_direction ha ha_not_m Γ.hE_on_m).le)).resolve_left hG_atom.1
    have hE_le_IC : Γ.E ≤ Γ.I ⊔ Γ.C := hG_eq_E ▸ hG_le_IC
    have hE_eq_EI : Γ.E = Γ.E_I :=
      (Γ.hE_I_atom.le_iff.mp (le_inf hE_le_IC Γ.hE_on_m)).resolve_left Γ.hE_atom.1
    have hC_ne_E : Γ.C ≠ Γ.E := fun h' => Γ.hC_not_m (h' ▸ Γ.hE_on_m)
    have hC_lt_CE : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h' => hC_ne_E ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hE_atom.1).symm)
    have hCE_eq_OC : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C :=
      ((sup_comm Γ.C Γ.O ▸ atom_covBy_join Γ.hC Γ.hO (Ne.symm hOC) : Γ.C ⋖ Γ.O ⊔ Γ.C).eq_or_eq
        hC_lt_CE.le (sup_le le_sup_right (inf_le_left : Γ.E ≤ Γ.O ⊔ Γ.C))).resolve_left
        (ne_of_gt hC_lt_CE)
    have hC_ne_EI : Γ.C ≠ Γ.E_I := fun h' => Γ.hC_not_m (h' ▸ Γ.hE_I_on_m)
    have hC_lt_CEI : Γ.C < Γ.C ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
      (fun h' => hC_ne_EI ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hE_I_atom.1).symm)
    have hCEI_eq_IC : Γ.C ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
      ((sup_comm Γ.C Γ.I ▸ atom_covBy_join Γ.hC Γ.hI (Ne.symm hIC) : Γ.C ⋖ Γ.I ⊔ Γ.C).eq_or_eq
        hC_lt_CEI.le (sup_le le_sup_right Γ.hE_I_le_IC)).resolve_left
        (ne_of_gt hC_lt_CEI)
    have hOC_eq_IC : Γ.O ⊔ Γ.C = Γ.I ⊔ Γ.C := by
      calc Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.E := hCE_eq_OC.symm
        _ = Γ.C ⊔ Γ.E_I := by rw [hE_eq_EI]
        _ = Γ.I ⊔ Γ.C := hCEI_eq_IC
    have hlIC : l ⊓ (Γ.I ⊔ Γ.C) = Γ.I := by
      change (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.C) = Γ.I
      rw [inf_comm, sup_comm Γ.I Γ.C]
      exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on
    exact Γ.hOI ((Γ.hI.le_iff.mp (le_inf (le_sup_left.trans hOC_eq_IC.le)
      (show Γ.O ≤ l from le_sup_left) |>.trans (inf_comm l _ ▸ hlIC).le)).resolve_left Γ.hO.1)
  have hG_ne_O : G ≠ Γ.O := fun h => hG_not_l (h ▸ le_sup_left)
  have hG_ne_I : G ≠ Γ.I := by
    intro h
    have hI_le_aE : Γ.I ≤ a ⊔ Γ.E := h ▸ hG_le_aE
    have ha_lt_aI : a < a ⊔ Γ.I := lt_of_le_of_ne le_sup_left
      (fun h' => haI ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hI.1).symm)
    have haI_eq_aE : a ⊔ Γ.I = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt_aI.le
        (sup_le le_sup_left hI_le_aE)).resolve_left (ne_of_gt ha_lt_aI)
    exact Γ.hE_not_l (le_sup_right.trans (haI_eq_aE.symm.le.trans (sup_le ha_on Γ.hI_on)))
  have hG_ne_C : G ≠ Γ.C := by
    intro h
    have hC_le_aE : Γ.C ≤ a ⊔ Γ.E := h ▸ hG_le_aE
    have ha_lt_aC : a < a ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h' => ha_ne_C ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hC.1).symm)
    have haC_eq_aE : a ⊔ Γ.C = a ⊔ Γ.E :=
      ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt_aC.le
        (sup_le le_sup_left hC_le_aE)).resolve_left (ne_of_gt ha_lt_aC)

    have hda_eq_E : d_a = Γ.E := by
      have h1 : d_a = (a ⊔ Γ.E) ⊓ m := by rw [← haC_eq_aE]
      rw [h1]; exact line_direction ha ha_not_m Γ.hE_on_m
    have hO_not_aC : ¬ Γ.O ≤ a ⊔ Γ.C := by
      intro hle
      have hl_le : l ≤ a ⊔ Γ.C := hOa_eq_l ▸ (sup_le hle le_sup_left : Γ.O ⊔ a ≤ a ⊔ Γ.C)
      exact Γ.hC_not_l (le_sup_right.trans
        (((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq ha_on hl_le).resolve_left
          (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)).symm.le)
    have hE_le_C : Γ.E ≤ Γ.C := by
      have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := hda_eq_E ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
      have hmod := modular_intersection Γ.hC ha Γ.hO ha_ne_C.symm hOC.symm ha_ne_O
        (show ¬ Γ.O ≤ Γ.C ⊔ a from sup_comm a Γ.C ▸ hO_not_aC)
      calc Γ.E ≤ (Γ.C ⊔ a) ⊓ (Γ.C ⊔ Γ.O) :=
            le_inf (sup_comm a Γ.C ▸ hE_le_aC) (sup_comm Γ.O Γ.C ▸ (CoordSystem.hE_le_OC : Γ.E ≤ Γ.O ⊔ Γ.C))
        _ = Γ.C := hmod
    have hE_eq_C := (Γ.hC.le_iff.mp hE_le_C).resolve_left Γ.hE_atom.1
    exact Γ.hC_not_m (hE_eq_C ▸ Γ.hE_on_m)

  have haG_eq_aE : a ⊔ G = a ⊔ Γ.E := by
    have h_lt : a < a ⊔ G := lt_of_le_of_ne le_sup_left
      (fun h => hG_not_l ((ha.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hG_atom.1 ▸ ha_on))
    exact ((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left hG_le_aE)).resolve_left (ne_of_gt h_lt)

  have hIG_eq_IC : Γ.I ⊔ G = Γ.I ⊔ Γ.C := by
    have hI_lt : Γ.I < Γ.I ⊔ G := lt_of_le_of_ne le_sup_left
      (fun h => hG_ne_I ((Γ.hI.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hG_atom.1))
    exact ((atom_covBy_join Γ.hI Γ.hC hIC).eq_or_eq hI_lt.le
      (sup_le le_sup_left hG_le_IC)).resolve_left (ne_of_gt hI_lt)

  have hCG_eq_IC : Γ.C ⊔ G = Γ.I ⊔ Γ.C := by
    have hC_lt : Γ.C < Γ.C ⊔ G := lt_of_le_of_ne le_sup_left
      (fun h => hG_ne_C ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hG_atom.1))
    have : Γ.C ⋖ Γ.I ⊔ Γ.C := sup_comm Γ.C Γ.I ▸ atom_covBy_join Γ.hC Γ.hI (Ne.symm hIC)
    exact (this.eq_or_eq hC_lt.le (sup_le le_sup_right hG_le_IC)).resolve_left
      (ne_of_gt hC_lt)

  have hIG_dir : (Γ.I ⊔ G) ⊓ m = Γ.E_I := by
    change (Γ.I ⊔ G) ⊓ (Γ.U ⊔ Γ.V) = (Γ.I ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V); rw [hIG_eq_IC]

  have hσcG_eq : dilation_ext Γ c G = (Γ.O ⊔ G) ⊓ (c ⊔ Γ.E_I) := by
    change (Γ.O ⊔ G) ⊓ (c ⊔ (Γ.I ⊔ G) ⊓ m) = (Γ.O ⊔ G) ⊓ (c ⊔ Γ.E_I); rw [hIG_dir]

  have hσEI_eq_cEI : σ ⊔ Γ.E_I = c ⊔ Γ.E_I := by
    have hc_ne_EI : c ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hc_on)
    by_cases hσc : σ = c
    · rw [hσc]
    · have hc_lt : c < c ⊔ σ := lt_of_le_of_ne le_sup_left
        (fun h => hσc ((hc.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hσ_atom.1))
      have hcσ_eq : c ⊔ σ = c ⊔ Γ.E_I :=
        ((atom_covBy_join hc Γ.hE_I_atom hc_ne_EI).eq_or_eq hc_lt.le
          (sup_le le_sup_left hσ_on_cEI)).resolve_left (ne_of_gt hc_lt)
      have hσ_ne_EI' : σ ≠ Γ.E_I := fun h' => hσ_not_m (h' ▸ Γ.hE_I_on_m)
      have hσ_cov := line_covers_its_atoms hc Γ.hE_I_atom hc_ne_EI hσ_atom hσ_on_cEI
      have hσ_lt : σ < σ ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
        (fun h' => hσ_ne_EI' ((hσ_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_I_atom.1).symm)
      exact (hσ_cov.eq_or_eq hσ_lt.le (sup_le hσ_on_cEI le_sup_right)).resolve_left
        (ne_of_gt hσ_lt)

  have hside1 : (Γ.O ⊔ a) ⊓ (σ ⊔ d_a) = ac := by
    rw [hOa_eq_l, inf_comm]; rfl
  have hda_ne_EI : d_a ≠ Γ.E_I := by
    intro h

    have hC_ne_da : Γ.C ≠ d_a := fun h' => Γ.hC_not_m (h' ▸ inf_le_right)
    have hC_lt_Cda : Γ.C < Γ.C ⊔ d_a := lt_of_le_of_ne le_sup_left
      (fun h' => hC_ne_da ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left hda_atom.1).symm)
    have hCda_le_aC : Γ.C ⊔ d_a ≤ a ⊔ Γ.C := sup_le le_sup_right (inf_le_left : d_a ≤ a ⊔ Γ.C)
    have hC_ne_EI : Γ.C ≠ Γ.E_I := fun h' => Γ.hC_not_m (h' ▸ Γ.hE_I_on_m)
    have hC_lt_CEI : Γ.C < Γ.C ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
      (fun h' => hC_ne_EI ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hE_I_atom.1).symm)
    have hCEI_le_IC : Γ.C ⊔ Γ.E_I ≤ Γ.I ⊔ Γ.C := sup_le le_sup_right Γ.hE_I_le_IC
    have hCda_eq_CEI : Γ.C ⊔ d_a = Γ.C ⊔ Γ.E_I := by rw [h]

    have hCa_cov : Γ.C ⋖ a ⊔ Γ.C :=
      sup_comm Γ.C a ▸ atom_covBy_join Γ.hC ha (Ne.symm ha_ne_C)
    have hCda_eq_aC : Γ.C ⊔ d_a = a ⊔ Γ.C :=
      (hCa_cov.eq_or_eq hC_lt_Cda.le hCda_le_aC).resolve_left (ne_of_gt hC_lt_Cda)
    have hIC_cov : Γ.C ⋖ Γ.I ⊔ Γ.C :=
      sup_comm Γ.C Γ.I ▸ atom_covBy_join Γ.hC Γ.hI (Ne.symm hIC)
    have hCEI_eq_IC : Γ.C ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
      (hIC_cov.eq_or_eq hC_lt_CEI.le hCEI_le_IC).resolve_left (ne_of_gt hC_lt_CEI)

    have haC_eq_IC : a ⊔ Γ.C = Γ.I ⊔ Γ.C :=
      hCda_eq_aC.symm.trans (hCda_eq_CEI.trans hCEI_eq_IC)

    have hCa_dir : (a ⊔ Γ.C) ⊓ l = a := by
      show (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a
      rw [sup_comm a Γ.C]; exact line_direction Γ.hC Γ.hC_not_l ha_on
    have hCI_dir : (Γ.I ⊔ Γ.C) ⊓ l = Γ.I := by
      show (Γ.I ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.I
      rw [sup_comm Γ.I Γ.C]; exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on
    have : a = Γ.I := by
      calc a = (a ⊔ Γ.C) ⊓ l := hCa_dir.symm
        _ = (Γ.I ⊔ Γ.C) ⊓ l := by rw [haC_eq_IC]
        _ = Γ.I := hCI_dir
    exact haI this
  have hdaEI_eq_m : d_a ⊔ Γ.E_I = m := by
    have hda_lt : d_a < d_a ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
      (fun h => hda_ne_EI ((hda_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_I_atom.1).symm)
    have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    exact ((line_covers_its_atoms Γ.hU Γ.hV hUV
      hda_atom (inf_le_right : d_a ≤ m)).eq_or_eq hda_lt.le
      (sup_le (inf_le_right : d_a ≤ m) Γ.hE_I_on_m)).resolve_left (ne_of_gt hda_lt)
  have hside2 : (a ⊔ G) ⊓ (d_a ⊔ Γ.E_I) = Γ.E := by
    rw [haG_eq_aE, hdaEI_eq_m]; exact line_direction ha ha_not_m Γ.hE_on_m
  have hside3 : (Γ.O ⊔ G) ⊓ (σ ⊔ Γ.E_I) = dilation_ext Γ c G := by
    rw [hσEI_eq_cEI, ← hσcG_eq]

  have hσ_le_CO : σ ≤ Γ.C ⊔ Γ.O := sup_comm Γ.O Γ.C ▸ hσ_on_OC
  have hda_le_Ca : d_a ≤ Γ.C ⊔ a := sup_comm a Γ.C ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
  have hEI_le_CG : Γ.E_I ≤ Γ.C ⊔ G := Γ.hE_I_le_IC.trans hCG_eq_IC.symm.le
  have hda_plane : d_a ≤ π := (inf_le_right : d_a ≤ m).trans Γ.m_covBy_π.le
  have hOaG_eq_π : Γ.O ⊔ a ⊔ G = π := by
    rw [hOa_eq_l]
    have hl_lt : l < l ⊔ G := lt_of_le_of_ne le_sup_left
      (fun h => hG_not_l (le_sup_right.trans h.symm.le))
    exact (hl_covBy.eq_or_eq hl_lt.le (sup_le hl_covBy.le hG_plane)).resolve_left
      (ne_of_gt hl_lt)
  have hσdaEI_eq_π : σ ⊔ d_a ⊔ Γ.E_I = π := by

    rw [sup_assoc, hdaEI_eq_m]
    have hm_lt : m < σ ⊔ m := lt_of_le_of_ne le_sup_right
      (fun h => hσ_not_m (le_sup_left.trans h.symm.le))
    exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hσ_plane Γ.m_covBy_π.le)).resolve_left
      (ne_of_gt hm_lt)
  have hOa_covBy : Γ.O ⊔ a ⋖ π := hOa_eq_l ▸ hl_covBy
  have hOG_covBy : Γ.O ⊔ G ⋖ π := by
    have ha_not_OG : ¬ a ≤ Γ.O ⊔ G := by
      intro h
      have hl_le : l ≤ Γ.O ⊔ G := hOa_eq_l ▸ sup_le le_sup_left h
      have hO_cov := atom_covBy_join Γ.hO hG_atom (Ne.symm hG_ne_O)
      have hO_lt_l := (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
      have hl_eq_OG := (hO_cov.eq_or_eq hO_lt_l.le hl_le).resolve_left (ne_of_gt hO_lt_l)
      exact hG_not_l (le_sup_right.trans hl_eq_OG.symm.le)
    rw [← hOaG_eq_π]
    have h_covBy := line_covBy_plane Γ.hO hG_atom ha (Ne.symm hG_ne_O) (Ne.symm ha_ne_O)
      (fun h => hG_not_l (h ▸ ha_on)) ha_not_OG
    convert h_covBy using 1; ac_rfl
  have haG_covBy : a ⊔ G ⋖ π := haG_eq_aE ▸ haE_covBy
  have ha_ne_G : a ≠ G := fun h => hG_not_l (h ▸ ha_on)
  have hσ_ne_da : σ ≠ d_a := fun h => hσ_not_m (h ▸ inf_le_right)
  have hσ_ne_EI : σ ≠ Γ.E_I := fun h => hσ_not_m (h ▸ Γ.hE_I_on_m)
  have hOa_ne_σda : Γ.O ⊔ a ≠ σ ⊔ d_a := by
    rw [hOa_eq_l]; intro h; exact hσ_not_l (le_sup_left.trans h.symm.le)
  have hOG_ne_σEI : Γ.O ⊔ G ≠ σ ⊔ Γ.E_I := by
    rw [hσEI_eq_cEI]
    intro h
    have hO_le_cEI : Γ.O ≤ c ⊔ Γ.E_I := le_sup_left.trans h.le
    have hcEI_l : (c ⊔ Γ.E_I) ⊓ l = c := by
      change (c ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = c; rw [sup_comm c Γ.E_I]
      exact line_direction Γ.hE_I_atom Γ.hE_I_not_l hc_on
    exact hc_ne_O ((hc.le_iff.mp (le_inf hO_le_cEI (show Γ.O ≤ l from le_sup_left)
      |>.trans hcEI_l.le)).resolve_left Γ.hO.1).symm
  have haG_ne_daEI : a ⊔ G ≠ d_a ⊔ Γ.E_I := by
    rw [haG_eq_aE, hdaEI_eq_m]; intro h; exact ha_not_m (le_sup_left.trans h.le)
  have hC_ne_da : Γ.C ≠ d_a := fun h => Γ.hC_not_m (h ▸ inf_le_right)
  have hC_ne_σ : Γ.C ≠ σ := by
    intro h
    exact (dilation_ext_ne_P Γ Γ.hC hc hc_on hc_ne_O hc_ne_U
      Γ.hC_plane Γ.hC_not_m Γ.hC_not_l (Ne.symm hOC) (Ne.symm hIC) hcI) h.symm
  have hO_ne_σ : Γ.O ≠ σ := by
    intro h; apply hc_ne_O
    have hO_le_cEI : Γ.O ≤ c ⊔ Γ.E_I := h ▸ hσ_on_cEI
    have hcEI_l : (c ⊔ Γ.E_I) ⊓ l = c := by
      change (c ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = c
      rw [sup_comm c Γ.E_I]
      exact line_direction Γ.hE_I_atom Γ.hE_I_not_l hc_on
    exact ((hc.le_iff.mp (le_inf hO_le_cEI (show Γ.O ≤ l from le_sup_left)
      |>.trans hcEI_l.le)).resolve_left Γ.hO.1).symm
  have ha_ne_da : a ≠ d_a := fun h => ha_not_m (h ▸ inf_le_right)
  have hG_ne_EI : G ≠ Γ.E_I := fun h => hG_not_m (h ▸ Γ.hE_I_on_m)

  obtain ⟨axis, haxis_le, haxis_ne, hax1, hax2, hax3⟩ :=
    desargues_planar Γ.hC Γ.hO ha hG_atom hσ_atom hda_atom Γ.hE_I_atom
      Γ.hC_plane (show Γ.O ≤ π from le_sup_left.trans le_sup_left)
      (ha_on.trans le_sup_left) hG_plane hσ_plane hda_plane
      (Γ.hE_I_on_m.trans Γ.m_covBy_π.le)
      hσ_le_CO hda_le_Ca hEI_le_CG
      (Ne.symm ha_ne_O) (Ne.symm hG_ne_O) ha_ne_G
      hσ_ne_da hσ_ne_EI hda_ne_EI
      hOa_ne_σda hOG_ne_σEI haG_ne_daEI
      hOaG_eq_π hσdaEI_eq_π
      (Ne.symm hOC) (Ne.symm ha_ne_C) (Ne.symm hG_ne_C)
      hC_ne_σ hC_ne_da (fun h => Γ.hC_not_m (h ▸ Γ.hE_I_on_m))
      hO_ne_σ ha_ne_da hG_ne_EI
      R hR hR_not h_irred
      hOa_covBy hOG_covBy haG_covBy

  have hσcG_le_acE : dilation_ext Γ c G ≤ ac ⊔ Γ.E := by
    have hac_le : ac ≤ axis := hside1 ▸ hax1
    have hE_le : Γ.E ≤ axis := hside2 ▸ hax3
    have hσcG_le : dilation_ext Γ c G ≤ axis := hside3 ▸ hax2

    have hac_atom : IsAtom ac := by

      have hda_ne_U' : d_a ≠ Γ.U := by
        intro h
        have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := h ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
        have haCl : (a ⊔ Γ.C) ⊓ l = a := by
          change (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a
          rw [sup_comm a Γ.C]; exact line_direction Γ.hC Γ.hC_not_l ha_on
        exact ha_ne_U ((ha.le_iff.mp (le_inf hU_le_aC (show Γ.U ≤ l from le_sup_right)
          |>.trans haCl.le)).resolve_left Γ.hU.1).symm

      have hU_not_σda : ¬ Γ.U ≤ σ ⊔ d_a := by
        intro hU_le
        have hdaU_le : d_a ⊔ Γ.U ≤ σ ⊔ d_a := sup_le le_sup_right hU_le
        have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
        have hdaU_eq_m : d_a ⊔ Γ.U = m := by
          have hda_lt : d_a < d_a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
            (fun h' => hda_ne_U' ((hda_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
              Γ.hU.1).symm)
          exact ((line_covers_its_atoms Γ.hU Γ.hV hUV hda_atom
            (inf_le_right : d_a ≤ m)).eq_or_eq hda_lt.le
            (sup_le (inf_le_right : d_a ≤ m) le_sup_left)).resolve_left (ne_of_gt hda_lt)
        have hm_le_σda : m ≤ σ ⊔ d_a := hdaU_eq_m ▸ hdaU_le
        have hσm_eq_π : σ ⊔ m = π := by
          have hm_lt : m < σ ⊔ m := lt_of_le_of_ne le_sup_right
            (fun h => hσ_not_m (le_sup_left.trans h.symm.le))
          exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hσ_plane Γ.m_covBy_π.le)).resolve_left
            (ne_of_gt hm_lt)
        have hσda_eq_π : σ ⊔ d_a = π :=
          le_antisymm (sup_le hσ_plane hda_plane)
            (hσm_eq_π ▸ sup_le le_sup_left hm_le_σda)
        have hσ_covBy_π : σ ⋖ π := hσda_eq_π ▸ atom_covBy_join hσ_atom hda_atom hσ_ne_da
        have hσ_ne_l : (σ : L) ≠ l := fun h => hσ_not_l (h.symm ▸ le_refl _)
        have ⟨_, h2⟩ := planes_meet_covBy hσ_covBy_π hl_covBy hσ_ne_l
        have hσl_bot : σ ⊓ l = ⊥ :=
          (hσ_atom.le_iff.mp inf_le_left).resolve_right (fun h => hσ_not_l (h ▸ inf_le_right))
        exact (hσl_bot ▸ h2).2 Γ.hO.bot_lt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt

      have hσda_covBy : σ ⊔ d_a ⋖ π := by
        have hdaU_eq_m : d_a ⊔ Γ.U = m := by
          have hda_lt : d_a < d_a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
            (fun h' => hda_ne_U' ((hda_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
              Γ.hU.1).symm)
          have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
          exact ((line_covers_its_atoms Γ.hU Γ.hV hUV hda_atom
            (inf_le_right : d_a ≤ m)).eq_or_eq hda_lt.le
            (sup_le (inf_le_right : d_a ≤ m) le_sup_left)).resolve_left (ne_of_gt hda_lt)
        have hσdaU_eq_π : σ ⊔ d_a ⊔ Γ.U = π := by
          rw [sup_assoc, hdaU_eq_m]
          have hm_lt : m < σ ⊔ m := lt_of_le_of_ne le_sup_right
            (fun h => hσ_not_m (le_sup_left.trans h.symm.le))
          exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hσ_plane Γ.m_covBy_π.le)).resolve_left
            (ne_of_gt hm_lt)
        rw [← hσdaU_eq_π]
        exact line_covBy_plane hσ_atom hda_atom Γ.hU hσ_ne_da
          (fun h => hU_not_σda (h ▸ le_sup_left)) hda_ne_U' hU_not_σda

      have hσda_ne_l : σ ⊔ d_a ≠ l := (hOa_eq_l ▸ hOa_ne_σda).symm
      have ⟨_, hmeet_covBy_l⟩ := planes_meet_covBy hσda_covBy hl_covBy hσda_ne_l

      have hmeet_ne_bot : (σ ⊔ d_a) ⊓ l ≠ ⊥ := fun h =>
        (h ▸ hmeet_covBy_l).2 Γ.hO.bot_lt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
      exact line_height_two Γ.hO Γ.hU Γ.hOU
        (bot_lt_iff_ne_bot.mpr hmeet_ne_bot) hmeet_covBy_l.lt
    have hac_on : ac ≤ l := by show coord_mul Γ a c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
    have hac_ne_E : ac ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hac_on)
    have hac_lt : ac < ac ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hac_ne_E ((hac_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_atom.1).symm)
    have hacE_le : ac ⊔ Γ.E ≤ axis := sup_le hac_le hE_le

    have haxis_lt : axis < π := lt_of_le_of_ne haxis_le haxis_ne
    have hacE_eq_axis : ac ⊔ Γ.E = axis := by

      have hac_not_m : ¬ ac ≤ m := by
        intro h

        have hO_not_m : ¬ Γ.O ≤ m := fun hOm =>
          Γ.hOU (Γ.atom_on_both_eq_U Γ.hO (show Γ.O ≤ l from le_sup_left) hOm)
        have hlm_eq_U : l ⊓ m = Γ.U := by
          change (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
          exact line_direction Γ.hO hO_not_m le_sup_left
        have hac_eq_U : ac = Γ.U :=
          (Γ.hU.le_iff.mp (le_inf hac_on h |>.trans hlm_eq_U.le)).resolve_left hac_atom.1

        have hU_le_σda : Γ.U ≤ σ ⊔ d_a := hac_eq_U ▸ (inf_le_left : ac ≤ σ ⊔ d_a)
        have hda_ne_U'' : d_a ≠ Γ.U := by
          intro hd; exact ha_ne_U ((ha.le_iff.mp (le_inf
            (hd ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C) : Γ.U ≤ a ⊔ Γ.C)
            (show Γ.U ≤ l from le_sup_right) |>.trans
            (show (a ⊔ Γ.C) ⊓ l = a from by
              change (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a
              rw [sup_comm a Γ.C]; exact line_direction Γ.hC Γ.hC_not_l ha_on).le)).resolve_left Γ.hU.1).symm
        have hUV : Γ.U ≠ Γ.V := fun hh => Γ.hV_off (hh ▸ le_sup_right)
        have hdaU_eq_m : d_a ⊔ Γ.U = m := by
          have hda_lt : d_a < d_a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
            (fun h' => hda_ne_U'' ((hda_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
              Γ.hU.1).symm)
          exact ((line_covers_its_atoms Γ.hU Γ.hV hUV hda_atom
            (inf_le_right : d_a ≤ m)).eq_or_eq hda_lt.le
            (sup_le (inf_le_right : d_a ≤ m) le_sup_left)).resolve_left (ne_of_gt hda_lt)
        have hm_le_σda : m ≤ σ ⊔ d_a := hdaU_eq_m ▸ sup_le le_sup_right hU_le_σda
        have hσm_eq_π : σ ⊔ m = π := by
          have hm_lt : m < σ ⊔ m := lt_of_le_of_ne le_sup_right
            (fun hh => hσ_not_m (le_sup_left.trans hh.symm.le))
          exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hσ_plane Γ.m_covBy_π.le)).resolve_left
            (ne_of_gt hm_lt)
        have hσda_eq_π : σ ⊔ d_a = π :=
          le_antisymm (sup_le hσ_plane hda_plane) (hσm_eq_π ▸ sup_le le_sup_left hm_le_σda)
        have hσ_covBy_π : σ ⋖ π := hσda_eq_π ▸ atom_covBy_join hσ_atom hda_atom hσ_ne_da
        have hσ_ne_l : (σ : L) ≠ l := fun hh => hσ_not_l (hh.symm ▸ le_refl _)
        have ⟨_, h2⟩ := planes_meet_covBy hσ_covBy_π hl_covBy hσ_ne_l
        have hσl_bot : σ ⊓ l = ⊥ :=
          (hσ_atom.le_iff.mp inf_le_left).resolve_right (fun hh => hσ_not_l (hh ▸ inf_le_right))
        exact (hσl_bot ▸ h2).2 Γ.hO.bot_lt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt

      have hmacE_eq_E : m ⊓ (ac ⊔ Γ.E) = Γ.E := by
        rw [inf_comm]; exact line_direction hac_atom hac_not_m Γ.hE_on_m
      have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
      have hE_covBy_m : Γ.E ⋖ m := line_covers_its_atoms Γ.hU Γ.hV hUV Γ.hE_atom Γ.hE_on_m
      have hacE_m_eq_π : m ⊔ (ac ⊔ Γ.E) = π := by

        have hmacE_eq_mac : m ⊔ (ac ⊔ Γ.E) = m ⊔ ac := by
          apply le_antisymm
          · exact sup_le le_sup_left (sup_le le_sup_right (Γ.hE_on_m.trans le_sup_left))
          · exact sup_le le_sup_left (le_sup_left.trans le_sup_right)
        rw [hmacE_eq_mac]
        have hm_lt : m < m ⊔ ac := lt_of_le_of_ne le_sup_left
          (fun h => hac_not_m (le_sup_right.trans h.symm.le))
        exact (Γ.m_covBy_π.eq_or_eq hm_lt.le
          (sup_le Γ.m_covBy_π.le (hac_on.trans le_sup_left))).resolve_left (ne_of_gt hm_lt)
      have hmacE_covBy_m : m ⊓ (ac ⊔ Γ.E) ⋖ m := by rw [hmacE_eq_E]; exact hE_covBy_m
      have hacE_covBy_π : ac ⊔ Γ.E ⋖ π := by
        rw [← hacE_m_eq_π]
        exact covBy_sup_of_inf_covBy_left hmacE_covBy_m
      exact (hacE_covBy_π.eq_or_eq hacE_le haxis_le).resolve_right haxis_ne |>.symm
    exact hσcG_le.trans hacE_eq_axis.symm.le

  have hPartA : dilation_ext Γ c C_a ≤ σ ⊔ Γ.U := by

    have hCa_not_OC : ¬ C_a ≤ Γ.O ⊔ Γ.C := by
      intro h
      have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
        intro hU
        have hl_le_OC : l ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left hU
        have hO_lt_l : Γ.O < l := (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
        have hl_eq_OC : l = Γ.O ⊔ Γ.C :=
          ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq hO_lt_l.le hl_le_OC).resolve_left
            (ne_of_gt hO_lt_l)
        exact Γ.hC_not_l (le_sup_right.trans hl_eq_OC.symm.le)

      have hqOC_eq_C : (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
        rw [sup_comm Γ.U Γ.C, sup_comm Γ.O Γ.C]
        calc (Γ.C ⊔ Γ.U) ⊓ (Γ.C ⊔ Γ.O) = Γ.C ⊔ Γ.U ⊓ (Γ.C ⊔ Γ.O) :=
              sup_inf_assoc_of_le Γ.U (le_sup_left : Γ.C ≤ Γ.C ⊔ Γ.O)
          _ = Γ.C := by
              have : Γ.U ⊓ (Γ.C ⊔ Γ.O) = ⊥ :=
                (Γ.hU.le_iff.mp inf_le_left).resolve_right
                  (fun h' => hU_not_OC (sup_comm Γ.C Γ.O ▸ (h' ▸ inf_le_right)))
              rw [this, sup_bot_eq]
      exact hCa_ne_C ((Γ.hC.le_iff.mp (le_inf hCa_le_q h |>.trans hqOC_eq_C.le)).resolve_left
        hCa_atom.1)

    have hσ_ne_σCa : σ ≠ dilation_ext Γ c C_a := by
      intro heq
      have hσ_le_OCa : σ ≤ Γ.O ⊔ C_a := heq ▸ (inf_le_left : dilation_ext Γ c C_a ≤ Γ.O ⊔ C_a)
      have hOCOCa_eq_O : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ C_a) = Γ.O :=
        modular_intersection Γ.hO Γ.hC hCa_atom hOC (Ne.symm hCa_ne_O) (Ne.symm hCa_ne_C)
          hCa_not_OC
      exact hO_ne_σ ((Γ.hO.le_iff.mp (le_inf hσ_on_OC hσ_le_OCa |>.trans
        hOCOCa_eq_O.le)).resolve_left hσ_atom.1).symm

    have hCCa_eq_UC : Γ.C ⊔ C_a = Γ.U ⊔ Γ.C := by
      have hC_lt : Γ.C < Γ.C ⊔ C_a := lt_of_le_of_ne le_sup_left
        (fun h' => hCa_ne_C ((Γ.hC.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          hCa_atom.1))
      exact ((sup_comm Γ.C Γ.U ▸ atom_covBy_join Γ.hC Γ.hU hUC.symm).eq_or_eq hC_lt.le
        (sup_le le_sup_right hCa_le_q)).resolve_left (ne_of_gt hC_lt)
    have hCCa_dir : (Γ.C ⊔ C_a) ⊓ m = Γ.U := hCCa_eq_UC ▸ hqm_eq_U

    have hdpd := dilation_preserves_direction Γ Γ.hC hCa_atom c hc hc_on hc_ne_O hc_ne_U
      Γ.hC_plane hCa_plane Γ.hC_not_m hCa_not_m Γ.hC_not_l hCa_not_l
      (Ne.symm hOC) hCa_ne_O (Ne.symm hCa_ne_C) (Ne.symm hIC) hCa_ne_I
      hσ_ne_σCa R hR hR_not h_irred

    have hU_le : Γ.U ≤ σ ⊔ dilation_ext Γ c C_a := by
      have : (σ ⊔ dilation_ext Γ c C_a) ⊓ m = Γ.U := by rw [← hdpd, hCCa_dir]
      exact this ▸ inf_le_left

    have hσU_le : σ ⊔ Γ.U ≤ σ ⊔ dilation_ext Γ c C_a := sup_le le_sup_left hU_le
    have hσ_ne_U : σ ≠ Γ.U := fun h => hσ_not_m (show σ ≤ m from h ▸ le_sup_left)
    have hσ_lt : σ < σ ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h => hσ_ne_U ((hσ_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hU.1).symm)
    have hσCa_atom := dilation_ext_atom Γ hCa_atom hc hc_on hc_ne_O hc_ne_U
      hCa_plane hCa_not_l hCa_ne_O hCa_ne_I hCa_not_m
    have hσU_eq : σ ⊔ Γ.U = σ ⊔ dilation_ext Γ c C_a :=
      ((atom_covBy_join hσ_atom hσCa_atom hσ_ne_σCa).eq_or_eq hσ_lt.le hσU_le).resolve_left
        (ne_of_gt hσ_lt)
    exact hσU_eq ▸ le_sup_right

  have hPartB : dilation_ext Γ c C_a ≤ ac ⊔ Γ.E := by

    have hG_ne_Ca : G ≠ C_a := by
      intro h
      have hI_not_UC : ¬ Γ.I ≤ Γ.U ⊔ Γ.C := by
        intro hI_le
        have hqlI : (Γ.U ⊔ Γ.C) ⊓ l = Γ.U := by
          change (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.U
          calc (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.U ⊔ Γ.C ⊓ (Γ.O ⊔ Γ.U) :=
                sup_inf_assoc_of_le Γ.C (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U)
            _ = Γ.U := by
                have : Γ.C ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
                  (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h' => Γ.hC_not_l (h' ▸ inf_le_right))
                rw [this, sup_bot_eq]
        have hI_eq_U : Γ.I = Γ.U :=
          (Γ.hU.le_iff.mp (le_inf hI_le Γ.hI_on |>.trans hqlI.le)).resolve_left Γ.hI.1
        exact Γ.hI_not_m (hI_eq_U ▸ le_sup_left)
      have hICUC_eq_C : (Γ.I ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C) = Γ.C := by
        rw [sup_comm Γ.I Γ.C, sup_comm Γ.U Γ.C]
        calc (Γ.C ⊔ Γ.I) ⊓ (Γ.C ⊔ Γ.U) = Γ.C ⊔ Γ.I ⊓ (Γ.C ⊔ Γ.U) :=
              sup_inf_assoc_of_le Γ.I (le_sup_left : Γ.C ≤ Γ.C ⊔ Γ.U)
          _ = Γ.C := by
              have : Γ.I ⊓ (Γ.C ⊔ Γ.U) = ⊥ :=
                (Γ.hI.le_iff.mp inf_le_left).resolve_right
                  (fun h' => hI_not_UC (sup_comm Γ.U Γ.C ▸ (h' ▸ inf_le_right)))
              rw [this, sup_bot_eq]
      exact hG_ne_C ((Γ.hC.le_iff.mp (le_inf hG_le_IC (h ▸ hCa_le_q) |>.trans
        hICUC_eq_C.le)).resolve_left hG_atom.1)

    have hGCa_eq_aE : G ⊔ C_a = a ⊔ Γ.E := by
      have hG_lt_GCa : G < G ⊔ C_a := lt_of_le_of_ne le_sup_left
        (fun h' => hG_ne_Ca ((hG_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          hCa_atom.1).symm)
      have hGCa_le_aE : G ⊔ C_a ≤ a ⊔ Γ.E := sup_le hG_le_aE hCa_le_aE
      have ha_lt_aE : a < a ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h' => ha_ne_E ((ha.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_atom.1).symm)

      have hG_covBy_aE : G ⋖ a ⊔ Γ.E :=
        line_covers_its_atoms ha Γ.hE_atom ha_ne_E hG_atom hG_le_aE
      exact (hG_covBy_aE.eq_or_eq hG_lt_GCa.le hGCa_le_aE).resolve_left (ne_of_gt hG_lt_GCa)

    have hGCa_dir : (G ⊔ C_a) ⊓ m = Γ.E := by
      rw [hGCa_eq_aE]; exact line_direction ha ha_not_m Γ.hE_on_m

    have hσG_ne_σCa : dilation_ext Γ c G ≠ dilation_ext Γ c C_a := by
      intro heq

      have hCa_not_OG : ¬ C_a ≤ Γ.O ⊔ G := by
        intro hle
        have hO_not_aE : ¬ Γ.O ≤ a ⊔ Γ.E := by
          intro hO_le
          have hl_le : l ≤ a ⊔ Γ.E := by
            show Γ.O ⊔ Γ.U ≤ a ⊔ Γ.E
            calc Γ.O ⊔ Γ.U = Γ.O ⊔ a := hOa_eq_l.symm
              _ ≤ a ⊔ Γ.E := sup_le hO_le le_sup_left
          have ha_lt_l := (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt
          exact Γ.hE_not_l (le_sup_right.trans
            (((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_lt_l.le hl_le).resolve_left
              (ne_of_gt ha_lt_l)).symm.le)

        have hO_not_aG : ¬ Γ.O ≤ a ⊔ G := fun h => hO_not_aE (haG_eq_aE ▸ h)
        have hGaGO_eq_G : (G ⊔ a) ⊓ (G ⊔ Γ.O) = G :=
          modular_intersection hG_atom ha Γ.hO (Ne.symm ha_ne_G) hG_ne_O ha_ne_O
            (fun h => hO_not_aG (sup_comm G a ▸ h))
        have hCa_le_Ga : C_a ≤ G ⊔ a :=
          hCa_le_aE.trans (haG_eq_aE.symm ▸ sup_comm a G ▸ le_refl (a ⊔ G))
        have hCa_le_GO : C_a ≤ G ⊔ Γ.O := sup_comm Γ.O G ▸ hle
        exact hG_ne_Ca.symm ((hG_atom.le_iff.mp
          (le_inf hCa_le_Ga hCa_le_GO |>.trans hGaGO_eq_G.le)).resolve_left hCa_atom.1)
      have hσG_atom := dilation_ext_atom Γ hG_atom hc hc_on hc_ne_O hc_ne_U
        hG_plane hG_not_l hG_ne_O hG_ne_I hG_not_m
      have hOGOCa_eq_O : (Γ.O ⊔ G) ⊓ (Γ.O ⊔ C_a) = Γ.O :=
        modular_intersection Γ.hO hG_atom hCa_atom (Ne.symm hG_ne_O) (Ne.symm hCa_ne_O)
          hG_ne_Ca hCa_not_OG
      have hσG_le_OG : dilation_ext Γ c G ≤ Γ.O ⊔ G := inf_le_left
      have hσG_le_OCa : dilation_ext Γ c G ≤ Γ.O ⊔ C_a := by
        calc dilation_ext Γ c G = dilation_ext Γ c C_a := heq
          _ ≤ Γ.O ⊔ C_a := inf_le_left

      have hσG_eq_O : dilation_ext Γ c G = Γ.O :=
        (Γ.hO.le_iff.mp (le_inf hσG_le_OG hσG_le_OCa |>.trans hOGOCa_eq_O.le)).resolve_left
          hσG_atom.1

      have hO_le_cEI : Γ.O ≤ c ⊔ Γ.E_I := by
        have : dilation_ext Γ c G ≤ c ⊔ ((Γ.I ⊔ G) ⊓ m) := inf_le_right
        rw [hIG_dir] at this; rw [hσG_eq_O] at this; exact this
      have hcEI_l : (c ⊔ Γ.E_I) ⊓ l = c := by
        change (c ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = c
        rw [sup_comm c Γ.E_I]
        exact line_direction Γ.hE_I_atom Γ.hE_I_not_l hc_on
      exact hc_ne_O ((hc.le_iff.mp (le_inf hO_le_cEI (show Γ.O ≤ l from le_sup_left) |>.trans
        hcEI_l.le)).resolve_left Γ.hO.1).symm

    have hσG_atom := dilation_ext_atom Γ hG_atom hc hc_on hc_ne_O hc_ne_U
      hG_plane hG_not_l hG_ne_O hG_ne_I hG_not_m
    have hdpd := dilation_preserves_direction Γ hG_atom hCa_atom c hc hc_on hc_ne_O hc_ne_U
      hG_plane hCa_plane hG_not_m hCa_not_m hG_not_l hCa_not_l
      hG_ne_O hCa_ne_O hG_ne_Ca hG_ne_I hCa_ne_I
      hσG_ne_σCa R hR hR_not h_irred

    have hE_le : Γ.E ≤ dilation_ext Γ c G ⊔ dilation_ext Γ c C_a := by
      have h : (dilation_ext Γ c G ⊔ dilation_ext Γ c C_a) ⊓ m = Γ.E := by
        rw [← hdpd, hGCa_dir]
      exact h ▸ inf_le_left

    have hσG_ne_E : dilation_ext Γ c G ≠ Γ.E := fun h =>
      dilation_ext_not_m Γ hG_atom hc hc_on hc_ne_O hc_ne_U
        hG_plane hG_not_m hG_not_l hG_ne_O hG_ne_I hcI (h ▸ Γ.hE_on_m)
    have hσG_lt : dilation_ext Γ c G < dilation_ext Γ c G ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hσG_ne_E ((hσG_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have hσCa_atom := dilation_ext_atom Γ hCa_atom hc hc_on hc_ne_O hc_ne_U
      hCa_plane hCa_not_l hCa_ne_O hCa_ne_I hCa_not_m
    have hσGE_eq : dilation_ext Γ c G ⊔ Γ.E = dilation_ext Γ c G ⊔ dilation_ext Γ c C_a :=
      ((atom_covBy_join hσG_atom hσCa_atom hσG_ne_σCa).eq_or_eq hσG_lt.le
        (sup_le le_sup_left hE_le)).resolve_left (ne_of_gt hσG_lt)
    exact (hσGE_eq ▸ le_sup_right : dilation_ext Γ c C_a ≤ dilation_ext Γ c G ⊔ Γ.E).trans
      (sup_le hσcG_le_acE le_sup_right)

  have hLHS_atom : IsAtom (dilation_ext Γ c C_a) :=
    dilation_ext_atom Γ hCa_atom hc hc_on hc_ne_O hc_ne_U
      hCa_plane hCa_not_l hCa_ne_O hCa_ne_I hCa_not_m
  have hRHS_atom : IsAtom ((σ ⊔ Γ.U) ⊓ (ac ⊔ Γ.E)) := by

    have hbot_lt : ⊥ < (σ ⊔ Γ.U) ⊓ (ac ⊔ Γ.E) :=
      lt_of_lt_of_le hLHS_atom.bot_lt (le_inf hPartA hPartB)

    have hlt : (σ ⊔ Γ.U) ⊓ (ac ⊔ Γ.E) < σ ⊔ Γ.U := by
      apply lt_of_le_of_ne inf_le_left
      intro h

      have hσU_le_acE : σ ⊔ Γ.U ≤ ac ⊔ Γ.E := h ▸ inf_le_right
      have hac_on' : ac ≤ l := show coord_mul Γ a c ≤ Γ.O ⊔ Γ.U from inf_le_right
      have hσUl : (σ ⊔ Γ.U) ⊓ l = Γ.U :=
        line_direction hσ_atom hσ_not_l (show Γ.U ≤ l from le_sup_right)
      have hacEl : (ac ⊔ Γ.E) ⊓ l = ac := by
        change (ac ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = ac
        rw [sup_comm ac Γ.E]
        exact line_direction Γ.hE_atom Γ.hE_not_l hac_on'
      have hU_eq_ac : Γ.U = ac := by
        have hU_le_ac : Γ.U ≤ ac :=
          hσUl ▸ inf_le_inf_right l hσU_le_acE |>.trans hacEl.le

        have hU_covBy_l : Γ.U ⋖ l := by
          show Γ.U ⋖ Γ.O ⊔ Γ.U
          rw [sup_comm]; exact atom_covBy_join Γ.hU Γ.hO (Ne.symm Γ.hOU)
        exact ((hU_covBy_l.eq_or_eq hU_le_ac (show ac ≤ l from inf_le_right)).resolve_right (by
          intro hac_eq_l

          have hl_le_σda : l ≤ σ ⊔ d_a := hac_eq_l ▸ (inf_le_left : ac ≤ σ ⊔ d_a)
          have hσ_le_σda : σ ≤ σ ⊔ d_a := le_sup_left
          have hl_lt_σl : l < σ ⊔ l := lt_of_le_of_ne le_sup_right
            (fun hh => hσ_not_l (le_sup_left.trans hh.symm.le))
          have hσl_eq_π : σ ⊔ l = π :=
            (hl_covBy.eq_or_eq hl_lt_σl.le (sup_le hσ_plane hl_covBy.le)).resolve_left
              (ne_of_gt hl_lt_σl)
          have hπ_le_σda : π ≤ σ ⊔ d_a := hσl_eq_π ▸ sup_le le_sup_left hl_le_σda
          have hσda_eq_π : σ ⊔ d_a = π := le_antisymm (sup_le hσ_plane hda_plane) hπ_le_σda
          have hσ_covBy' : σ ⋖ π := hσda_eq_π ▸ atom_covBy_join hσ_atom hda_atom hσ_ne_da
          have ⟨_, h2'⟩ := planes_meet_covBy hσ_covBy' hl_covBy
            (fun hh => hσ_not_l (hh.symm ▸ le_refl _))
          exact (((hσ_atom.le_iff.mp inf_le_left).resolve_right
            (fun hh => hσ_not_l (hh ▸ inf_le_right))) ▸ h2').2 Γ.hO.bot_lt
            (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)).symm

      have hU_le_σda : Γ.U ≤ σ ⊔ d_a := hU_eq_ac ▸ (inf_le_left : ac ≤ σ ⊔ d_a)

      have hda_ne_U' : d_a ≠ Γ.U := by
        intro hd
        have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := hd ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
        have haCl : (a ⊔ Γ.C) ⊓ l = a := by
          change (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a
          rw [sup_comm a Γ.C]; exact line_direction Γ.hC Γ.hC_not_l ha_on
        exact ha_ne_U ((ha.le_iff.mp (le_inf hU_le_aC (show Γ.U ≤ l from le_sup_right)
          |>.trans haCl.le)).resolve_left Γ.hU.1).symm
      have hUV : Γ.U ≠ Γ.V := fun hh => Γ.hV_off (hh ▸ le_sup_right)
      have hdaU_eq_m : d_a ⊔ Γ.U = m := by
        have hda_lt : d_a < d_a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
          (fun h' => hda_ne_U' ((hda_atom.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
            Γ.hU.1).symm)
        exact ((line_covers_its_atoms Γ.hU Γ.hV hUV hda_atom
          (inf_le_right : d_a ≤ m)).eq_or_eq hda_lt.le
          (sup_le (inf_le_right : d_a ≤ m) le_sup_left)).resolve_left (ne_of_gt hda_lt)
      have hm_le : m ≤ σ ⊔ d_a := hdaU_eq_m ▸ sup_le le_sup_right hU_le_σda
      have hσm_eq_π' : σ ⊔ m = π := by
        have hm_lt : m < σ ⊔ m := lt_of_le_of_ne le_sup_right
          (fun hh => hσ_not_m (le_sup_left.trans hh.symm.le))
        exact (Γ.m_covBy_π.eq_or_eq hm_lt.le (sup_le hσ_plane Γ.m_covBy_π.le)).resolve_left
          (ne_of_gt hm_lt)
      have hσda_eq_π : σ ⊔ d_a = π := le_antisymm (sup_le hσ_plane hda_plane)
        (hσm_eq_π' ▸ sup_le le_sup_left hm_le)
      have hσ_covBy : σ ⋖ π := hσda_eq_π ▸ atom_covBy_join hσ_atom hda_atom hσ_ne_da
      have ⟨_, h2⟩ := planes_meet_covBy hσ_covBy hl_covBy
        (fun hh => hσ_not_l (hh.symm ▸ le_refl _))
      exact (((hσ_atom.le_iff.mp inf_le_left).resolve_right
        (fun hh => hσ_not_l (hh ▸ inf_le_right))) ▸ h2).2 Γ.hO.bot_lt
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt

    have hσ_ne_U' : σ ≠ Γ.U := fun h => hσ_not_m (show σ ≤ m from h ▸ le_sup_left)
    exact line_height_two hσ_atom Γ.hU hσ_ne_U' hbot_lt hlt
  exact (hRHS_atom.le_iff.mp (le_inf hPartA hPartB)).resolve_left hLHS_atom.1
/-- info: 'Foam.Bridges.beta_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms beta_atom

/-- info: 'Foam.Bridges.beta_not_l' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms beta_not_l

/-- info: 'Foam.Bridges.beta_plane' does not depend on any axioms -/
#guard_msgs in #print axioms beta_plane

/-- info: 'Foam.Bridges.dilation_mul_key_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dilation_mul_key_identity

end Foam.Bridges
