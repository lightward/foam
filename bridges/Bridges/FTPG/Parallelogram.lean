import Bridges.FTPG.Coord

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

def parallel (l₁ l₂ m : L) : Prop := l₁ ⊓ m = l₂ ⊓ m

omit [BoundedOrder L] [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
@[simp] theorem parallel_refl (l m : L) : parallel l l m := rfl

omit [BoundedOrder L] [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem parallel_symm {l₁ l₂ m : L} (h : parallel l₁ l₂ m) :
    parallel l₂ l₁ m := h.symm

omit [BoundedOrder L] [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem parallel_trans {l₁ l₂ l₃ m : L} (h₁ : parallel l₁ l₂ m)
    (h₂ : parallel l₂ l₃ m) : parallel l₁ l₃ m := h₁.trans h₂

omit [ComplementedLattice L] in

theorem line_meets_m_at_atom {a b m π : L}
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (hab_le : a ⊔ b ≤ π)
    (_hm_le : m ≤ π) (hm_cov : m ⋖ π)
    (ha_not : ¬ a ≤ m) :
    IsAtom ((a ⊔ b) ⊓ m) := by

  have hab_not_m : ¬ (a ⊔ b) ≤ m :=
    fun h => ha_not (le_trans le_sup_left h)
  have h_meet_ne : m ⊓ (a ⊔ b) ≠ ⊥ :=
    lines_meet_if_coplanar hm_cov hab_le hab_not_m ha
      (lt_of_le_of_ne le_sup_left (fun h =>
        hab ((ha.le_iff.mp (le_sup_right.trans (le_of_eq h.symm))).resolve_left hb.1).symm))

  have h_lt : (a ⊔ b) ⊓ m < a ⊔ b :=
    lt_of_le_of_ne inf_le_left (fun h => hab_not_m (inf_eq_left.mp h))
  have h_pos : ⊥ < (a ⊔ b) ⊓ m := by
    rw [inf_comm (a := a ⊔ b) (b := m)]
    exact bot_lt_iff_ne_bot.mpr h_meet_ne
  exact line_height_two ha hb hab h_pos h_lt

noncomputable def parallelogram_completion
    (P P' Q m : L) : L :=
  let d := (P ⊔ P') ⊓ m
  let e := (P ⊔ Q) ⊓ m
  (Q ⊔ d) ⊓ (P' ⊔ e)

omit [ComplementedLattice L] in

theorem parallelogram_completion_atom
    {P P' Q m π : L}
    (hP : IsAtom P) (hP' : IsAtom P') (hQ : IsAtom Q)
    (hPP' : P ≠ P') (hPQ : P ≠ Q) (hP'Q : P' ≠ Q)

    (hP_le : P ≤ π) (hP'_le : P' ≤ π) (hQ_le : Q ≤ π)

    (hm_le : m ≤ π) (hm_cov : m ⋖ π)
    (hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m)

    (hP_not : ¬ P ≤ m) (hP'_not : ¬ P' ≤ m) (hQ_not : ¬ Q ≤ m)

    (hQ_not_PP' : ¬ Q ≤ P ⊔ P') :
    IsAtom (parallelogram_completion P P' Q m) := by
  unfold parallelogram_completion
  set d := (P ⊔ P') ⊓ m
  set e := (P ⊔ Q) ⊓ m

  have hd : IsAtom d := line_meets_m_at_atom hP hP' hPP'
    (sup_le hP_le hP'_le) hm_le hm_cov hP_not
  have he : IsAtom e := line_meets_m_at_atom hP hQ hPQ
    (sup_le hP_le hQ_le) hm_le hm_cov hP_not

  have hde : d ≠ e := by
    intro h_eq
    have hd_le_PP' : d ≤ P ⊔ P' := inf_le_left
    have he_le_PQ : e ≤ P ⊔ Q := inf_le_left
    have hd_le_PQ : d ≤ P ⊔ Q := h_eq ▸ he_le_PQ
    have hd_le_P : d ≤ P := by
      have := le_inf hd_le_PP' hd_le_PQ
      rwa [modular_intersection hP hP' hQ hPP' hPQ hP'Q hQ_not_PP'] at this
    have : d ≤ P ⊓ m := le_inf hd_le_P (inf_le_right)
    have hPm : P ⊓ m = ⊥ := (hP.le_iff.mp inf_le_left).resolve_right
      (fun h => hP_not (h ▸ inf_le_right))
    exact hd.1 (le_antisymm (hPm ▸ this) bot_le)

  have hQd : Q ≠ d := fun h => hQ_not (h ▸ inf_le_right)
  have hP'e : P' ≠ e := fun h => hP'_not (h ▸ inf_le_right)
  have hd_le_m : d ≤ m := inf_le_right
  have he_le_m : e ≤ m := inf_le_right

  have hd_cov_m : d ⋖ m := hm_line d hd hd_le_m

  have hm_join_Q : m ⊔ Q = π := by
    have h_lt : m < m ⊔ Q := lt_of_le_of_ne le_sup_left
      (fun h => hQ_not (le_sup_right.trans h.symm.le))
    exact (hm_cov.eq_or_eq h_lt.le (sup_le hm_le hQ_le)).resolve_left (ne_of_gt h_lt)
  have hm_join_Qd : m ⊔ (Q ⊔ d) = π := by
    have : m ⊔ (Q ⊔ d) = m ⊔ Q ⊔ d := (sup_assoc m Q d).symm
    rw [this, hm_join_Q]
    exact le_antisymm (sup_le (le_refl π) (hd_le_m.trans hm_le)) le_sup_left
  have hQd_cov : Q ⊔ d ⋖ π := by
    rw [← hm_join_Qd]
    exact covBy_sup_of_inf_covBy_left (by rwa [show m ⊓ (Q ⊔ d) = d from by
      have hd_le_meet : d ≤ m ⊓ (Q ⊔ d) := le_inf hd_le_m le_sup_right
      have hQd_not_m : ¬ Q ⊔ d ≤ m := fun h => hQ_not (le_sup_left.trans h)
      have h_cov : d ⋖ d ⊔ Q := atom_covBy_join hd hQ hQd.symm
      rw [sup_comm] at h_cov
      rcases h_cov.eq_or_eq hd_le_meet inf_le_right with h | h
      · exact h
      · exact absurd (h ▸ inf_le_left : Q ⊔ d ≤ m) hQd_not_m])

  have hd_not_P'e : ¬ d ≤ P' ⊔ e := by
    intro hd_le
    have hd_cov_P'e : d ⋖ P' ⊔ e := line_covers_its_atoms hP' he hP'e hd hd_le
    have h_de_le : d ⊔ e ≤ P' ⊔ e := sup_le hd_le le_sup_right
    have h_d_lt_de : d < d ⊔ e := lt_of_le_of_ne le_sup_left
      (fun h => hde ((hd.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left he.1).symm)
    rcases hd_cov_P'e.eq_or_eq h_d_lt_de.le h_de_le with h | h
    · exact absurd h (ne_of_gt h_d_lt_de)
    · exact hP'_not (le_trans le_sup_left (h ▸ sup_le hd_le_m he_le_m))

  have h_de_eq_m : d ⊔ e = m := by
    have h_lt : d < d ⊔ e := lt_of_le_of_ne le_sup_left
      (fun h => hde ((hd.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left he.1).symm)
    exact (hd_cov_m.eq_or_eq h_lt.le (sup_le hd_le_m he_le_m)).resolve_left (ne_of_gt h_lt)
  have h_plane : (P' ⊔ e) ⊔ d = π := by
    rw [sup_assoc, sup_comm e d, h_de_eq_m]
    have h_lt : m < P' ⊔ m := lt_of_le_of_ne le_sup_right
      (fun h => hP'_not (le_sup_left.trans h.symm.le))
    have : P' ⊔ m ≤ π := sup_le hP'_le hm_le
    exact (hm_cov.eq_or_eq h_lt.le this).resolve_left (ne_of_gt h_lt)
  have hQd_in_plane : Q ⊔ d ≤ (P' ⊔ e) ⊔ d := by
    rw [h_plane]; exact sup_le hQ_le (hd_le_m.trans hm_le)

  exact perspect_atom hd hQ hQd hP' he hP'e hd_not_P'e hQd_in_plane

omit [ComplementedLattice L] [IsAtomistic L] in

theorem line_direction {a d m : L} (ha : IsAtom a) (ha_not : ¬ a ≤ m)
    (hd_le : d ≤ m) : (a ⊔ d) ⊓ m = d := by
  have ham : a ⊓ m = ⊥ := by
    rcases ha.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) ha_not
  have := sup_inf_assoc_of_le a hd_le

  calc (a ⊔ d) ⊓ m = (d ⊔ a) ⊓ m := by rw [sup_comm]
    _ = d ⊔ a ⊓ m := sup_inf_assoc_of_le a hd_le
    _ = d ⊔ ⊥ := by rw [ham]
    _ = d := by simp

omit [ComplementedLattice L] [IsAtomistic L] in

theorem parallelogram_parallel_direction
    {P P' Q m : L}
    (hQ : IsAtom Q) (hQ_not : ¬ Q ≤ m)
    (hd_atom : IsAtom ((P ⊔ P') ⊓ m))
    (hQ'_atom : IsAtom (parallelogram_completion P P' Q m))
    (hQ'_ne_Q : parallelogram_completion P P' Q m ≠ Q) :
    parallel (P ⊔ P') (Q ⊔ parallelogram_completion P P' Q m) m := by
  set Q' := parallelogram_completion P P' Q m with hQ'_def
  set d := (P ⊔ P') ⊓ m
  have hQ'_le_Qd : Q' ≤ Q ⊔ d := by
    unfold parallelogram_completion at hQ'_def; rw [hQ'_def]; exact inf_le_left
  have hQd : Q ≠ d := fun h => hQ_not (h ▸ inf_le_right)
  have hQ_lt_QQ' : Q < Q ⊔ Q' := lt_of_le_of_ne le_sup_left
    (fun h => hQ'_ne_Q ((hQ.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
      hQ'_atom.1))
  have hQQ'_le : Q ⊔ Q' ≤ Q ⊔ d := sup_le le_sup_left hQ'_le_Qd
  have h_cov : Q ⋖ Q ⊔ d := atom_covBy_join hQ hd_atom hQd
  have hQQ'_eq : Q ⊔ Q' = Q ⊔ d :=
    (h_cov.eq_or_eq hQ_lt_QQ'.le hQQ'_le).resolve_left (ne_of_gt hQ_lt_QQ')
  show (P ⊔ P') ⊓ m = (Q ⊔ Q') ⊓ m
  rw [hQQ'_eq, line_direction hQ hQ_not inf_le_right]

omit [ComplementedLattice L] [IsAtomistic L] in

theorem parallelogram_parallel_sides
    {P P' Q m : L}
    (hP' : IsAtom P') (hP'_not : ¬ P' ≤ m)
    (he_atom : IsAtom ((P ⊔ Q) ⊓ m))
    (hQ'_atom : IsAtom (parallelogram_completion P P' Q m))
    (hQ'_ne_P' : parallelogram_completion P P' Q m ≠ P') :
    parallel (P ⊔ Q) (P' ⊔ parallelogram_completion P P' Q m) m := by
  set Q' := parallelogram_completion P P' Q m with hQ'_def
  set e := (P ⊔ Q) ⊓ m
  have hQ'_le_P'e : Q' ≤ P' ⊔ e := by
    unfold parallelogram_completion at hQ'_def; rw [hQ'_def]; exact inf_le_right
  have hP'e : P' ≠ e := fun h => hP'_not (h ▸ inf_le_right)
  have hP'_lt_P'Q' : P' < P' ⊔ Q' := lt_of_le_of_ne le_sup_left
    (fun h => hQ'_ne_P' ((hP'.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
      hQ'_atom.1))
  have hP'Q'_le : P' ⊔ Q' ≤ P' ⊔ e := sup_le le_sup_left hQ'_le_P'e
  have h_cov : P' ⋖ P' ⊔ e := atom_covBy_join hP' he_atom hP'e
  have hP'Q'_eq : P' ⊔ Q' = P' ⊔ e :=
    (h_cov.eq_or_eq hP'_lt_P'Q'.le hP'Q'_le).resolve_left (ne_of_gt hP'_lt_P'Q')
  show (P ⊔ Q) ⊓ m = (P' ⊔ Q') ⊓ m
  rw [hP'Q'_eq, line_direction hP' hP'_not inf_le_right]

theorem coord_add_atom (Γ : CoordSystem L)
    (a b : L) (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (_ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) :
    IsAtom (coord_add Γ a b) := by
  set l := Γ.O ⊔ Γ.U
  set m := Γ.U ⊔ Γ.V
  set q := Γ.U ⊔ Γ.C
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  show IsAtom (((a ⊔ Γ.C) ⊓ m ⊔ (b ⊔ Γ.E) ⊓ q) ⊓ l)
  set a' := (a ⊔ Γ.C) ⊓ m
  set D_b := (b ⊔ Γ.E) ⊓ q
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hb_ne_E : b ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hb_on)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hm_cov : m ⋖ π := by
    show Γ.U ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
    have hO_inf_m : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
    rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = Γ.O ⊔ (Γ.U ⊔ Γ.V) from sup_assoc _ _ _]
    exact covBy_sup_of_inf_covBy_left (hO_inf_m ▸ Γ.hO.bot_covBy)
  have hlq_eq_U : l ⊓ q = Γ.U := by
    show (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U
    rw [sup_comm Γ.O Γ.U]
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm hUC
      (fun h => Γ.hC_not_l (h ▸ le_sup_left))
      (fun h => Γ.hC_not_l (le_trans h (by rw [sup_comm])))
  have hqm_eq_U : q ⊓ m = Γ.U := by
    show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [this, sup_bot_eq]
  have hE_not_q : ¬ Γ.E ≤ q := fun h =>
    Γ.hEU ((Γ.hU.le_iff.mp (hqm_eq_U ▸ le_inf h Γ.hE_on_m)).resolve_left Γ.hE_atom.1)
  have hmC_eq_π : m ⊔ Γ.C = π := by
    have h_lt : m < m ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))
    exact (hm_cov.eq_or_eq h_lt.le (sup_le hm_le_π Γ.hC_plane)).resolve_left (ne_of_gt h_lt)

  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have ha'_atom : IsAtom a' :=
    line_meets_m_at_atom ha Γ.hC ha_ne_C
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane) hm_le_π hm_cov ha_not_m

  have hq_le_π : q ≤ π := sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane
  have hq_cov_π : q ⋖ π := by
    have hV_not_q : ¬ Γ.V ≤ q := fun hle =>
      hUV ((Γ.hU.le_iff.mp (hqm_eq_U ▸ le_inf hle le_sup_right)).resolve_left Γ.hV.1).symm
    have hV_disj_q : Γ.V ⊓ q = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => hV_not_q (h ▸ inf_le_right))
    exact (by have : Γ.V ⊔ q = m ⊔ Γ.C := by
                show Γ.V ⊔ (Γ.U ⊔ Γ.C) = (Γ.U ⊔ Γ.V) ⊔ Γ.C; ac_rfl
              rw [this, hmC_eq_π] : Γ.V ⊔ q = π) ▸
      covBy_sup_of_inf_covBy_left (hV_disj_q ▸ Γ.hV.bot_covBy)

  have hb_not_q : ¬ b ≤ q := fun h =>
    hb_ne_U ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf hb_on h)).resolve_left hb.1)
  have hDb_atom : IsAtom D_b :=
    line_meets_m_at_atom hb Γ.hE_atom hb_ne_E
      (sup_le (hb_on.trans le_sup_left) (Γ.hE_on_m.trans hm_le_π)) hq_le_π hq_cov_π hb_not_q

  have ha'Db : a' ≠ D_b := by
    intro h_eq
    have ha'_le_U : a' ≤ Γ.U := by
      have : a' ≤ q := by rw [h_eq]; exact inf_le_right
      rw [← hqm_eq_U]; exact le_inf this inf_le_right
    have ha'_eq_U := (Γ.hU.le_iff.mp ha'_le_U).resolve_left ha'_atom.1
    have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := ha'_eq_U ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
    have hU_le_a : Γ.U ≤ a :=
      calc Γ.U ≤ l ⊓ (Γ.C ⊔ a) := le_inf le_sup_right (hU_le_aC.trans (sup_comm a Γ.C).le)
        _ = a := inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on
    exact ha_ne_U ((ha.le_iff.mp hU_le_a).resolve_left Γ.hU.1).symm

  have hDb_not_l : ¬ D_b ≤ l := by
    intro h
    have hU_le_bE : Γ.U ≤ b ⊔ Γ.E :=
      ((Γ.hU.le_iff.mp (by rw [← hlq_eq_U]; exact le_inf h inf_le_right)).resolve_left
        hDb_atom.1) ▸ (inf_le_left : D_b ≤ b ⊔ Γ.E)
    have hl_le_bE : l ≤ b ⊔ Γ.E := by
      have hbU_eq_l : b ⊔ Γ.U = l := by
        have h_lt : Γ.U < Γ.U ⊔ b := lt_of_le_of_ne le_sup_left
          (fun h => hb_ne_U ((Γ.hU.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hb.1))
        calc b ⊔ Γ.U = Γ.U ⊔ b := sup_comm _ _
          _ = Γ.U ⊔ Γ.O := ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq h_lt.le
              (sup_le le_sup_left (hb_on.trans (sup_comm Γ.O Γ.U).le))).resolve_left
              (ne_of_gt h_lt)
          _ = l := sup_comm _ _
      exact hbU_eq_l ▸ sup_le le_sup_left hU_le_bE
    rcases (atom_covBy_join hb Γ.hE_atom (fun h => Γ.hE_not_l (h ▸ hb_on))).eq_or_eq
      hb_on hl_le_bE with h_eq | h_eq
    · exact hb_ne_O ((hb.le_iff.mp (le_sup_left.trans h_eq.le)).resolve_left Γ.hO.1).symm
    · exact Γ.hE_not_l (le_sup_right.trans h_eq.symm.le)

  have hDb_le_π : D_b ≤ π := (inf_le_right : D_b ≤ q).trans hq_le_π
  have hl_cov_π : l ⋖ π := by
    have hV_disj_l : Γ.V ⊓ l = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have h2 : l ⋖ Γ.V ⊔ l := covBy_sup_of_inf_covBy_left (hV_disj_l ▸ Γ.hV.bot_covBy)
    rwa [sup_comm] at h2
  have hl_sup_Db : l ⊔ D_b = π :=
    ((hl_cov_π.eq_or_eq (lt_of_le_of_ne le_sup_left
      (fun h => hDb_not_l (le_sup_right.trans h.symm.le))).le
      (sup_le le_sup_left hDb_le_π)).resolve_left
      (ne_of_gt (lt_of_le_of_ne le_sup_left
        (fun h => hDb_not_l (le_sup_right.trans h.symm.le)))))
  exact perspect_atom hDb_atom ha'_atom ha'Db Γ.hO Γ.hU Γ.hOU hDb_not_l
    (sup_le (((inf_le_right : a' ≤ m).trans hm_le_π).trans hl_sup_Db.symm.le) le_sup_right)

/-- info: 'Foam.Bridges.parallel' does not depend on any axioms -/
#guard_msgs in #print axioms parallel

/-- info: 'Foam.Bridges.parallel_symm' does not depend on any axioms -/
#guard_msgs in #print axioms parallel_symm

/-- info: 'Foam.Bridges.parallel_trans' does not depend on any axioms -/
#guard_msgs in #print axioms parallel_trans

/-- info: 'Foam.Bridges.line_meets_m_at_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms line_meets_m_at_atom

/-- info: 'Foam.Bridges.parallelogram_completion_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parallelogram_completion_atom

/-- info: 'Foam.Bridges.line_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms line_direction

/-- info: 'Foam.Bridges.parallelogram_parallel_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parallelogram_parallel_direction

/-- info: 'Foam.Bridges.parallelogram_parallel_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parallelogram_parallel_sides

/-- info: 'Foam.Bridges.coord_add_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_add_atom

end Foam.Bridges
