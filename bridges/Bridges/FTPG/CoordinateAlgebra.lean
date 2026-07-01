import Bridges.FTPG.Deaxiomatize
import Bridges.FTPG.AssocCapstone
import Bridges.FTPG.AddComm
import Bridges.FTPG.MulAssoc
import Bridges.FTPG.LeftDistrib
import Bridges.FTPG.Distrib

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## Gap C : no zero divisors -- coord_mul_ne_O -/

theorem coord_mul_ne_O' (Γ : CoordSystem L)
    (a c : L) (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U) :
    coord_mul Γ a c ≠ Γ.O := by
  set l := Γ.O ⊔ Γ.U with hl
  set m := Γ.U ⊔ Γ.V with hm
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ
  set σ_c := (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) with hσc
  set d_a := (a ⊔ Γ.C) ⊓ m with hda
  have hval : coord_mul Γ a c = (σ_c ⊔ d_a) ⊓ l := rfl
  rw [hval]
  intro hmul_eq_O
  -- basic ne facts
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hc_ne_EI : c ≠ Γ.E_I :=
    fun h => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on (h ▸ Γ.hE_I_on_m))
  -- d_a is an atom
  have hda_atom : IsAtom d_a :=
    line_meets_m_at_atom ha Γ.hC ha_ne_C
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane) hm_le_π Γ.m_covBy_π ha_not_m
  -- σ_c is an atom
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
  -- O ≠ d_a (since d_a ≤ m and O ∉ m)
  have hda_le_m : d_a ≤ m := inf_le_right
  have hO_ne_da : Γ.O ≠ d_a := fun h => Γ.hO_not_m (h ▸ hda_le_m)
  -- σ_c ≠ O (uses c ≠ O)
  have hEI_ne_O : Γ.E_I ≠ Γ.O := fun h => Γ.hO_not_m (h ▸ Γ.hE_I_on_m)
  have hσ_le_cEI : σ_c ≤ c ⊔ Γ.E_I := inf_le_right
  have hσ_ne_O : σ_c ≠ Γ.O := by
    intro h
    have hO_le : Γ.O ≤ c ⊔ Γ.E_I := h ▸ hσ_le_cEI
    have h_eq : c ⊔ Γ.E_I = c ⊔ Γ.O :=
      line_eq_of_atom_le hc Γ.hE_I_atom Γ.hO hc_ne_EI hc_ne_O hEI_ne_O hO_le
    have hEI_le_l : Γ.E_I ≤ Γ.O ⊔ Γ.U := by
      have : Γ.E_I ≤ c ⊔ Γ.O := h_eq ▸ (le_sup_right : Γ.E_I ≤ c ⊔ Γ.E_I)
      exact this.trans (sup_le hc_on le_sup_left)
    exact Γ.hE_I_not_l hEI_le_l
  -- σ_c ≠ d_a
  have hda_ne_σ : d_a ≠ σ_c := by
    intro h_eq
    have hda_le_OC : d_a ≤ Γ.O ⊔ Γ.C := h_eq ▸ (inf_le_left : σ_c ≤ Γ.O ⊔ Γ.C)
    have hda_eq_E : d_a = Γ.E := by
      have h1 : d_a ≤ Γ.E := by
        show d_a ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
        exact le_inf hda_le_OC inf_le_right
      exact (Γ.hE_atom.le_iff.mp h1).resolve_left hda_atom.1
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := hda_eq_E ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
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
  -- Now the contradiction: O ≤ σ_c ⊔ d_a
  have hO_le_join : Γ.O ≤ σ_c ⊔ d_a := hmul_eq_O.symm.le.trans inf_le_left
  -- σ_c ⋖ σ_c ⊔ d_a
  have hcov : σ_c ⋖ σ_c ⊔ d_a := atom_covBy_join hσ_atom hda_atom hda_ne_σ.symm
  have hσ_lt : σ_c < σ_c ⊔ Γ.O := lt_of_le_of_ne le_sup_left
    (fun h => hσ_ne_O ((hσ_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hO.1).symm)
  have hOσ_le : σ_c ⊔ Γ.O ≤ σ_c ⊔ d_a := sup_le le_sup_left hO_le_join
  have hOσ_eq : σ_c ⊔ Γ.O = σ_c ⊔ d_a :=
    (hcov.eq_or_eq hσ_lt.le hOσ_le).resolve_left (ne_of_gt hσ_lt)
  -- so d_a ≤ σ_c ⊔ O ≤ O ⊔ C
  have hda_le_Oσ : d_a ≤ σ_c ⊔ Γ.O := hOσ_eq ▸ (le_sup_right : d_a ≤ σ_c ⊔ d_a)
  have hda_le_OC : d_a ≤ Γ.O ⊔ Γ.C := hda_le_Oσ.trans
    (sup_le (inf_le_left : σ_c ≤ Γ.O ⊔ Γ.C) le_sup_left)
  -- d_a ≤ (O⊔C) ⊓ m = E
  have hda_eq_E : d_a = Γ.E := by
    have h1 : d_a ≤ Γ.E := by
      show d_a ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
      exact le_inf hda_le_OC inf_le_right
    exact (Γ.hE_atom.le_iff.mp h1).resolve_left hda_atom.1
  -- E ≤ a ⊔ C, contradiction (same as hda_ne_σ tail)
  have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := hda_eq_E ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
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

/-! ## Gap C : product of affine atoms is affine -- coord_mul_ne_U -/

theorem coord_mul_ne_U' (Γ : CoordSystem L)
    (a c : L) (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U) :
    coord_mul Γ a c ≠ Γ.U := by
  set l := Γ.O ⊔ Γ.U with hl
  set m := Γ.U ⊔ Γ.V with hm
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ
  set σ_c := (Γ.O ⊔ Γ.C) ⊓ (c ⊔ Γ.E_I) with hσc
  set d_a := (a ⊔ Γ.C) ⊓ m with hda
  have hval : coord_mul Γ a c = (σ_c ⊔ d_a) ⊓ l := rfl
  rw [hval]
  intro hmul_eq_U
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hc_ne_EI : c ≠ Γ.E_I :=
    fun h => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on (h ▸ Γ.hE_I_on_m))
  -- d_a atom
  have hda_atom : IsAtom d_a :=
    line_meets_m_at_atom ha Γ.hC ha_ne_C
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane) hm_le_π Γ.m_covBy_π ha_not_m
  have hda_le_m : d_a ≤ m := inf_le_right
  -- σ_c atom
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
  -- d_a ∉ l  (so d_a ≠ U)
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
  have hda_ne_U : d_a ≠ Γ.U :=
    fun h => hda_not_l (h ▸ (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U))
  -- d_a ≠ σ_c
  have hda_ne_σ : d_a ≠ σ_c := by
    intro h_eq
    have hda_le_OC : d_a ≤ Γ.O ⊔ Γ.C := h_eq ▸ (inf_le_left : σ_c ≤ Γ.O ⊔ Γ.C)
    have hda_eq_E : d_a = Γ.E := by
      have h1 : d_a ≤ Γ.E := by
        show d_a ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
        exact le_inf hda_le_OC inf_le_right
      exact (Γ.hE_atom.le_iff.mp h1).resolve_left hda_atom.1
    have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := hda_eq_E ▸ (inf_le_left : d_a ≤ a ⊔ Γ.C)
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
  -- σ_c ∉ m
  have hE_sup_EI : Γ.E ⊔ Γ.E_I = m := by
    have hE_lt : Γ.E < Γ.E ⊔ Γ.E_I :=
      lt_of_le_of_ne le_sup_left (fun h => Γ.hE_I_ne_E
        ((Γ.hE_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_I_atom.1))
    have hE_covBy_m : Γ.E ⋖ m := by
      rw [hm, ← CoordSystem.EU_eq_m]
      exact atom_covBy_join Γ.hE_atom Γ.hU CoordSystem.hEU
    exact (hE_covBy_m.eq_or_eq hE_lt.le
      (sup_le CoordSystem.hE_on_m Γ.hE_I_on_m)).resolve_left (ne_of_gt hE_lt)
  have hσ_not_m : ¬ σ_c ≤ m := by
    intro h
    have hσ_le_E : σ_c ≤ Γ.E := by
      show σ_c ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
      exact le_inf inf_le_left h
    have hσ_eq_E : σ_c = Γ.E := (Γ.hE_atom.le_iff.mp hσ_le_E).resolve_left hσ_atom.1
    have hE_le_cEI : Γ.E ≤ c ⊔ Γ.E_I := hσ_eq_E ▸ (inf_le_right : σ_c ≤ c ⊔ Γ.E_I)
    have hm_le : m ≤ c ⊔ Γ.E_I := by rw [← hE_sup_EI]; exact sup_le hE_le_cEI le_sup_right
    have hEI_cov : Γ.E_I ⋖ c ⊔ Γ.E_I := by
      rw [sup_comm]; exact atom_covBy_join Γ.hE_I_atom hc (Ne.symm hc_ne_EI)
    have hEI_lt_m : Γ.E_I < m :=
      (line_covers_its_atoms Γ.hU Γ.hV hUV Γ.hE_I_atom Γ.hE_I_on_m).lt
    have hm_eq : m = c ⊔ Γ.E_I :=
      (hEI_cov.eq_or_eq hEI_lt_m.le hm_le).resolve_left (ne_of_gt hEI_lt_m)
    have hc_le_m : c ≤ m := hm_eq.symm ▸ (le_sup_left : c ≤ c ⊔ Γ.E_I)
    exact hc_ne_U (Γ.atom_on_both_eq_U hc hc_on hc_le_m)
  -- contradiction
  have hU_le_join : Γ.U ≤ σ_c ⊔ d_a := hmul_eq_U.symm.le.trans inf_le_left
  have hda_lt : d_a < d_a ⊔ Γ.U := lt_of_le_of_ne le_sup_left
    (fun h => hda_ne_U ((hda_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1).symm)
  have hcov : d_a ⋖ σ_c ⊔ d_a := by
    have := atom_covBy_join hda_atom hσ_atom hda_ne_σ; rwa [sup_comm] at this
  have hdU_le : d_a ⊔ Γ.U ≤ σ_c ⊔ d_a := sup_le le_sup_right hU_le_join
  have hdU_eq : d_a ⊔ Γ.U = σ_c ⊔ d_a :=
    (hcov.eq_or_eq hda_lt.le hdU_le).resolve_left (ne_of_gt hda_lt)
  have hσ_le_dU : σ_c ≤ d_a ⊔ Γ.U := hdU_eq ▸ (le_sup_left : σ_c ≤ σ_c ⊔ d_a)
  have hσ_le_m : σ_c ≤ m := hσ_le_dU.trans (sup_le hda_le_m (le_sup_left : Γ.U ≤ m))
  exact hσ_not_m hσ_le_m

/-! ## Gap C : sum of affine atoms is affine -- coord_add_ne_U -/

theorem coord_add_ne_U' (Γ : CoordSystem L)
    (a b : L) (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) :
    coord_add Γ a b ≠ Γ.U := by
  set l := Γ.O ⊔ Γ.U with hl
  set m := Γ.U ⊔ Γ.V with hm
  set q := Γ.U ⊔ Γ.C with hq
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ
  set a' := (a ⊔ Γ.C) ⊓ m with ha'_def
  set D_b := (b ⊔ Γ.E) ⊓ q with hDb_def
  have hval : coord_add Γ a b = (a' ⊔ D_b) ⊓ l := rfl
  rw [hval]
  intro hadd_eq_U
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hb_ne_E : b ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hb_on)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
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
  -- a' atom
  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have ha'_atom : IsAtom a' :=
    line_meets_m_at_atom ha Γ.hC ha_ne_C
      (sup_le (ha_on.trans le_sup_left) Γ.hC_plane) hm_le_π Γ.m_covBy_π ha_not_m
  have ha'_le_m : a' ≤ m := inf_le_right
  -- D_b atom
  have hq_le_π : q ≤ π := sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane
  have hq_cov_π : q ⋖ π := by
    have hV_not_q : ¬ Γ.V ≤ q := fun hle =>
      hUV ((Γ.hU.le_iff.mp (hqm_eq_U ▸ le_inf hle le_sup_right)).resolve_left Γ.hV.1).symm
    have hV_disj_q : Γ.V ⊓ q = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => hV_not_q (h ▸ inf_le_right))
    have hmC_eq_π : m ⊔ Γ.C = π := by
      have h_lt : m < m ⊔ Γ.C := lt_of_le_of_ne le_sup_left
        (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))
      exact (Γ.m_covBy_π.eq_or_eq h_lt.le (sup_le hm_le_π Γ.hC_plane)).resolve_left (ne_of_gt h_lt)
    exact (by have : Γ.V ⊔ q = m ⊔ Γ.C := by
                show Γ.V ⊔ (Γ.U ⊔ Γ.C) = (Γ.U ⊔ Γ.V) ⊔ Γ.C; ac_rfl
              rw [this, hmC_eq_π] : Γ.V ⊔ q = π) ▸
      covBy_sup_of_inf_covBy_left (hV_disj_q ▸ Γ.hV.bot_covBy)
  have hb_not_q : ¬ b ≤ q := fun h =>
    hb_ne_U ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf hb_on h)).resolve_left hb.1)
  have hDb_atom : IsAtom D_b :=
    line_meets_m_at_atom hb Γ.hE_atom hb_ne_E
      (sup_le (hb_on.trans le_sup_left) (Γ.hE_on_m.trans hm_le_π)) hq_le_π hq_cov_π hb_not_q
  -- a' ≠ U
  have ha'_ne_U : a' ≠ Γ.U := by
    intro h
    have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := h ▸ (inf_le_left : a' ≤ a ⊔ Γ.C)
    have hU_le_a : Γ.U ≤ a :=
      calc Γ.U ≤ l ⊓ (Γ.C ⊔ a) := le_inf le_sup_right (hU_le_aC.trans (sup_comm a Γ.C).le)
        _ = a := inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on
    exact ha_ne_U ((ha.le_iff.mp hU_le_a).resolve_left Γ.hU.1).symm
  -- D_b ≠ U  (D_b ∉ l, but U ∈ l)
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
  have hDb_ne_U : D_b ≠ Γ.U :=
    fun h => hDb_not_l (h ▸ (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U))
  -- a' ≠ D_b
  have ha'Db : a' ≠ D_b := by
    intro h_eq
    have ha'_le_U : a' ≤ Γ.U := by
      have : a' ≤ q := by rw [h_eq]; exact inf_le_right
      rw [← hqm_eq_U]; exact le_inf this inf_le_right
    exact ha'_ne_U ((Γ.hU.le_iff.mp ha'_le_U).resolve_left ha'_atom.1)
  -- contradiction: U ≤ a' ⊔ D_b
  have hU_le_join : Γ.U ≤ a' ⊔ D_b := hadd_eq_U.symm.le.trans inf_le_left
  have ha'_lt : a' < a' ⊔ Γ.U := lt_of_le_of_ne le_sup_left
    (fun h => ha'_ne_U ((ha'_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1).symm)
  have hcov : a' ⋖ a' ⊔ D_b := atom_covBy_join ha'_atom hDb_atom ha'Db
  have ha'U_le : a' ⊔ Γ.U ≤ a' ⊔ D_b := sup_le le_sup_left hU_le_join
  have ha'U_eq : a' ⊔ Γ.U = a' ⊔ D_b :=
    (hcov.eq_or_eq ha'_lt.le ha'U_le).resolve_left (ne_of_gt ha'_lt)
  have hDb_le_a'U : D_b ≤ a' ⊔ Γ.U := ha'U_eq ▸ (le_sup_right : D_b ≤ a' ⊔ D_b)
  have hDb_le_m : D_b ≤ m := hDb_le_a'U.trans (sup_le ha'_le_m (le_sup_left : Γ.U ≤ m))
  have hDb_le_q : D_b ≤ q := inf_le_right
  have hDb_le_U : D_b ≤ Γ.U := hqm_eq_U ▸ le_inf hDb_le_q hDb_le_m
  exact hDb_ne_U ((Γ.hU.le_iff.mp hDb_le_U).resolve_left hDb_atom.1)

/-! ## Coordinate-facing closure wrappers + membership (all witness-free) -/

namespace Coordinate
variable {Γ : CoordSystem L}

theorem add_ne_U (a b : Coordinate Γ) : coord_add Γ a.1 b.1 ≠ Γ.U := by
  by_cases ha : a.1 = Γ.O
  · rw [ha, coord_add_left_zero Γ b.1 b.isAtom b.on_l b.ne_U]; exact b.ne_U
  by_cases hb : b.1 = Γ.O
  · rw [hb, coord_add_right_zero Γ a.1 a.isAtom a.on_l]; exact a.ne_U
  · exact coord_add_ne_U' Γ a.1 b.1 a.isAtom b.isAtom a.on_l b.on_l hb a.ne_U b.ne_U

theorem mul_ne_U (a b : Coordinate Γ) : coord_mul Γ a.1 b.1 ≠ Γ.U := by
  by_cases ha : a.1 = Γ.O
  · rw [ha, coord_mul_left_zero Γ b.1 b.isAtom b.on_l b.ne_U]; exact Γ.hOU
  by_cases hb : b.1 = Γ.O
  · rw [hb, coord_mul_right_zero Γ a.1 a.isAtom a.on_l a.ne_U]; exact Γ.hOU
  · exact coord_mul_ne_U' Γ a.1 b.1 a.isAtom b.isAtom a.on_l b.on_l ha a.ne_U b.ne_U

theorem mul_ne_O (a b : Coordinate Γ) (ha : a.1 ≠ Γ.O) (hb : b.1 ≠ Γ.O) :
    coord_mul Γ a.1 b.1 ≠ Γ.O :=
  coord_mul_ne_O' Γ a.1 b.1 a.isAtom b.isAtom a.on_l b.on_l ha hb a.ne_U b.ne_U

theorem add_isAtom (a b : Coordinate Γ) : IsAtom (coord_add Γ a.1 b.1) := by
  by_cases ha : a.1 = Γ.O
  · rw [ha, coord_add_left_zero Γ b.1 b.isAtom b.on_l b.ne_U]; exact b.isAtom
  by_cases hb : b.1 = Γ.O
  · rw [hb, coord_add_right_zero Γ a.1 a.isAtom a.on_l]; exact a.isAtom
  · exact coord_add_atom Γ a.1 b.1 a.isAtom b.isAtom a.on_l b.on_l ha hb a.ne_U b.ne_U

theorem mul_isAtom (a b : Coordinate Γ) : IsAtom (coord_mul Γ a.1 b.1) := by
  by_cases ha : a.1 = Γ.O
  · rw [ha, coord_mul_left_zero Γ b.1 b.isAtom b.on_l b.ne_U]; exact Γ.hO
  by_cases hb : b.1 = Γ.O
  · rw [hb, coord_mul_right_zero Γ a.1 a.isAtom a.on_l a.ne_U]; exact Γ.hO
  · exact coord_mul_atom Γ a.1 b.1 a.isAtom b.isAtom a.on_l b.on_l ha hb a.ne_U b.ne_U

/-- Totalized (O-aware) coordinate operations, sorry-free. -/
noncomputable def fadd (a b : Coordinate Γ) : Coordinate Γ :=
  ⟨coord_add Γ a.1 b.1, add_isAtom a b, inf_le_right, add_ne_U a b⟩

noncomputable def fmul (a b : Coordinate Γ) : Coordinate Γ :=
  ⟨coord_mul Γ a.1 b.1, mul_isAtom a b, inf_le_right, mul_ne_U a b⟩

open Classical in
noncomputable def fneg (a : Coordinate Γ) : Coordinate Γ :=
  if h : a.1 = Γ.O then ⟨Γ.O, Γ.hO, le_sup_left, Γ.hOU⟩ else
    ⟨coord_neg Γ a.1, coord_neg_atom Γ a.isAtom a.on_l h a.ne_U,
     coord_neg_on_l Γ a.1, coord_neg_ne_U Γ a.isAtom a.on_l h a.ne_U⟩

open Classical in
noncomputable def finv (a : Coordinate Γ) : Coordinate Γ :=
  if h : a.1 = Γ.O then a else
    ⟨coord_inv Γ a.1, coord_inv_atom Γ a.isAtom a.on_l a.ne_U,
     coord_inv_on_l Γ a.1, coord_inv_ne_U Γ a.isAtom a.on_l h⟩

end Coordinate

/-! ## Bundled frame carrying the witnesses the algebraic laws require -/

structure CoordFrame (L : Type u) [Lattice L] [BoundedOrder L]
    [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] where
  Γ : CoordSystem L
  P : L
  hP_atom : IsAtom P
  hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V
  hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U
  hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V
  hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C
  hP_ne_I : P ≠ Γ.I
  hP_ne_O : P ≠ Γ.O
  R : L
  hR_atom : IsAtom R
  hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V
  h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
    ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q

/-! ## Gap D : DivisionRing assembly over the bundled frame.

The nine witness-free / boundary fields are proven sorry-free here, pinning down the
field→lemma map. The six remaining fields (`add_assoc`, `add_comm`, `neg_add_cancel`,
`mul_assoc`, `left_distrib`, `right_distrib`) are the genuine residual: each is supplied
by an algebraic-law lemma whose hypotheses include the frame witnesses `Φ.R`, `Φ.P`,
`Φ.h_irred` PLUS non-degeneracy side conditions
(operands `≠ O`, `≠ U`, pairwise-distinct, intermediate sums/products `≠ O`/`≠ U`, and
`b ≠ I`). Totalizing them therefore needs an O/I/distinctness case analysis whose
degenerate branches (e.g. repeated operands in associativity) are NOT covered by the
currently-available lemmas. -/

namespace Coordinate
variable {Φ : CoordFrame L}

theorem finv_of_ne (a : Coordinate Φ.Γ) (h : a.1 ≠ Φ.Γ.O) :
    (finv a).1 = coord_inv Φ.Γ a.1 := by
  simp only [finv, dif_neg h]

-- The nine witness-free DivisionRing field laws, each PROVEN sorry-free.
theorem field_zero_add (a : Coordinate Φ.Γ) : fadd 0 a = a :=
  Coordinate.ext (coord_add_left_zero Φ.Γ a.1 a.isAtom a.on_l a.ne_U)

theorem field_add_zero (a : Coordinate Φ.Γ) : fadd a 0 = a :=
  Coordinate.ext (coord_add_right_zero Φ.Γ a.1 a.isAtom a.on_l)

theorem field_one_mul (a : Coordinate Φ.Γ) : fmul 1 a = a :=
  Coordinate.ext (coord_mul_left_one Φ.Γ a.1 a.isAtom a.on_l a.ne_U)

theorem field_mul_one (a : Coordinate Φ.Γ) : fmul a 1 = a :=
  Coordinate.ext (coord_mul_right_one Φ.Γ a.1 a.isAtom a.on_l)

theorem field_zero_mul (a : Coordinate Φ.Γ) : fmul 0 a = 0 :=
  Coordinate.ext (coord_mul_left_zero Φ.Γ a.1 a.isAtom a.on_l a.ne_U)

theorem field_mul_zero (a : Coordinate Φ.Γ) : fmul a 0 = 0 :=
  Coordinate.ext (coord_mul_right_zero Φ.Γ a.1 a.isAtom a.on_l a.ne_U)

theorem field_inv_zero : finv (0 : Coordinate Φ.Γ) = 0 := by
  have h : (0 : Coordinate Φ.Γ).1 = Φ.Γ.O := rfl
  simp only [finv, dif_pos h]

theorem field_exists_pair_ne : (0 : Coordinate Φ.Γ) ≠ 1 :=
  fun h => Φ.Γ.hOI (congrArg Subtype.val h)

/-- The DivisionRing right-inverse law -- witness-free (no Mac Lane / `axis_to_sigma_a_le`). -/
theorem field_mul_inv_cancel (a : Coordinate Φ.Γ) (ha : a.1 ≠ Φ.Γ.O) :
    fmul a (finv a) = 1 := by
  apply Coordinate.ext
  show coord_mul Φ.Γ a.1 (finv a).1 = Φ.Γ.I
  rw [finv_of_ne a ha]
  exact coord_mul_right_inv Φ.Γ a.isAtom a.on_l ha a.ne_U

end Coordinate

end Foam.Bridges

#print axioms Foam.Bridges.coord_mul_ne_O'
#print axioms Foam.Bridges.coord_mul_ne_U'
#print axioms Foam.Bridges.coord_add_ne_U'
#print axioms Foam.Bridges.Coordinate.add_ne_U
#print axioms Foam.Bridges.Coordinate.mul_ne_U
#print axioms Foam.Bridges.Coordinate.mul_ne_O
#print axioms Foam.Bridges.Coordinate.fadd
#print axioms Foam.Bridges.Coordinate.fmul
#print axioms Foam.Bridges.Coordinate.fneg
#print axioms Foam.Bridges.Coordinate.finv

#print axioms Foam.Bridges.Coordinate.field_one_mul
#print axioms Foam.Bridges.Coordinate.field_mul_inv_cancel
#print axioms Foam.Bridges.Coordinate.field_zero_add
#print axioms Foam.Bridges.Coordinate.field_inv_zero
