import Bridges.Coord
import Bridges.AddComm

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

omit [ComplementedLattice L] in

theorem perspectivity_val {c a₁ b₁ a₂ b₂ : L}
    (hc : IsAtom c) (ha₁ : IsAtom a₁) (hb₁ : IsAtom b₁) (ha₂ : IsAtom a₂) (hb₂ : IsAtom b₂)
    (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂)
    (hc_not_l₁ : ¬ c ≤ a₁ ⊔ b₁) (hc_not_l₂ : ¬ c ≤ a₂ ⊔ b₂)
    (h_coplanar : a₁ ⊔ b₁ ⊔ c = a₂ ⊔ b₂ ⊔ c)
    (P : AtomsOn (a₁ ⊔ b₁)) :
    (perspectivity hc ha₁ hb₁ ha₂ hb₂ hab₁ hab₂ hc_not_l₁ hc_not_l₂ h_coplanar P).val
      = (P.val ⊔ c) ⊓ (a₂ ⊔ b₂) := by
  obtain ⟨p, hp_atom, hp_le⟩ := P
  rfl

theorem coord_add_left_cancel (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_U : a ≠ Γ.U)
    (h_eq : coord_add Γ a b = coord_add Γ a c) : b = c := by

  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hm_le_π : Γ.U ⊔ Γ.V ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right

  have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
    apply modular_intersection Γ.hU Γ.hC Γ.hV hUC hUV
      (fun h => Γ.hC_not_m (h ▸ le_sup_right))
    intro hle
    exact Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
      (atom_covBy_join Γ.hU Γ.hV hUV).lt.le (sup_le le_sup_left hle)).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hU Γ.hV hUV).lt) ▸ le_sup_right)

  have hE_not_l : ¬ Γ.E ≤ Γ.O ⊔ Γ.U := CoordSystem.hE_not_l
  have hE_not_UC : ¬ Γ.E ≤ Γ.U ⊔ Γ.C := fun h =>
    CoordSystem.hEU (Γ.hU.le_iff.mp (hUC_inf_m ▸ le_inf h CoordSystem.hE_on_m)
      |>.resolve_left Γ.hE_atom.1)
  have h_coplanar1 : (Γ.O ⊔ Γ.U) ⊔ Γ.E = (Γ.U ⊔ Γ.C) ⊔ Γ.E := by
    have hL : (Γ.O ⊔ Γ.U) ⊔ Γ.E = Γ.O ⊔ Γ.U ⊔ Γ.V :=
      calc (Γ.O ⊔ Γ.U) ⊔ Γ.E = Γ.O ⊔ (Γ.U ⊔ Γ.E) := sup_assoc _ _ _
        _ = Γ.O ⊔ (Γ.E ⊔ Γ.U) := by rw [sup_comm Γ.U Γ.E]
        _ = Γ.O ⊔ (Γ.U ⊔ Γ.V) := by rw [CoordSystem.EU_eq_m]
        _ = Γ.O ⊔ Γ.U ⊔ Γ.V := (sup_assoc _ _ _).symm
    have hR : (Γ.U ⊔ Γ.C) ⊔ Γ.E = Γ.O ⊔ Γ.U ⊔ Γ.V :=
      calc (Γ.U ⊔ Γ.C) ⊔ Γ.E = Γ.E ⊔ (Γ.U ⊔ Γ.C) := sup_comm _ _
        _ = (Γ.E ⊔ Γ.U) ⊔ Γ.C := (sup_assoc _ _ _).symm
        _ = (Γ.U ⊔ Γ.V) ⊔ Γ.C := by rw [CoordSystem.EU_eq_m]
        _ = Γ.O ⊔ Γ.U ⊔ Γ.V := Γ.m_sup_C_eq_π
    exact hL.trans hR.symm

  have hp_atom : IsAtom ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) :=
    perspect_atom Γ.hC ha ha_ne_C Γ.hU Γ.hV hUV Γ.hC_not_m
      (sup_le (ha_on.trans (le_sup_left.trans (le_of_eq Γ.m_sup_C_eq_π.symm))) le_sup_right)

  have hp_ne_U : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠ Γ.U := by
    intro hpU
    have hU_le_aC : Γ.U ≤ a ⊔ Γ.C := hpU ▸ (inf_le_left : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ a ⊔ Γ.C)
    have haU_le : a ⊔ Γ.U ≤ a ⊔ Γ.C := sup_le le_sup_left hU_le_aC
    have haU_eq_l : a ⊔ Γ.U = Γ.O ⊔ Γ.U :=
      ((line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).eq_or_eq le_sup_left
        (sup_le ha_on le_sup_right)).resolve_left
        (ne_of_gt (atom_covBy_join ha Γ.hU ha_ne_U).lt)
    have hl_le_aC : Γ.O ⊔ Γ.U ≤ a ⊔ Γ.C := haU_eq_l ▸ haU_le
    have h_eq_l : Γ.O ⊔ Γ.U = a ⊔ Γ.C :=
      ((atom_covBy_join ha Γ.hC ha_ne_C).eq_or_eq ha_on hl_le_aC).resolve_left
        (ne_of_gt (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt)
    exact Γ.hC_not_l (le_of_le_of_eq le_sup_right h_eq_l.symm)
  have hp_not_UC : ¬ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.C := by
    intro h
    have hp_le_U : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U := by
      have hle := le_inf h (inf_le_right : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V)
      rwa [hUC_inf_m] at hle
    exact hp_ne_U ((Γ.hU.le_iff.mp hp_le_U).resolve_left hp_atom.1)
  have hp_not_l : ¬ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hp_le_U : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U := by
      have hle := le_inf h (inf_le_right : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V)
      rwa [Γ.l_inf_m_eq_U] at hle
    exact hp_ne_U ((Γ.hU.le_iff.mp hp_le_U).resolve_left hp_atom.1)
  have h_coplanar2 :
      (Γ.U ⊔ Γ.C) ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = (Γ.O ⊔ Γ.U) ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
    set p := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) with hp_def
    have hp_le_m : p ≤ Γ.U ⊔ Γ.V := inf_le_right

    have hUp_eq_m : Γ.U ⊔ p = Γ.U ⊔ Γ.V :=
      ((atom_covBy_join Γ.hU Γ.hV hUV).eq_or_eq le_sup_left
        (sup_le le_sup_left hp_le_m)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU hp_atom hp_ne_U.symm).lt)
    have hL : (Γ.U ⊔ Γ.C) ⊔ p = Γ.O ⊔ Γ.U ⊔ Γ.V :=
      calc (Γ.U ⊔ Γ.C) ⊔ p = Γ.U ⊔ (Γ.C ⊔ p) := sup_assoc _ _ _
        _ = Γ.U ⊔ (p ⊔ Γ.C) := by rw [sup_comm Γ.C p]
        _ = (Γ.U ⊔ p) ⊔ Γ.C := (sup_assoc _ _ _).symm
        _ = (Γ.U ⊔ Γ.V) ⊔ Γ.C := by rw [hUp_eq_m]
        _ = Γ.O ⊔ Γ.U ⊔ Γ.V := Γ.m_sup_C_eq_π

    have hl_cov : (Γ.O ⊔ Γ.U) ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
      have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
        (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
      have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
      rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
    have hl_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ p :=
      lt_of_le_of_ne le_sup_left (fun h => hp_not_l (le_sup_right.trans h.symm.le))
    have hR : (Γ.O ⊔ Γ.U) ⊔ p = Γ.O ⊔ Γ.U ⊔ Γ.V :=
      (hl_cov.eq_or_eq hl_lt.le (sup_le le_sup_left (hp_le_m.trans hm_le_π))).resolve_left
        (ne_of_gt hl_lt)
    exact hL.trans hR.symm

  have hval : ∀ (x : L) (hx : IsAtom x) (hx_on : x ≤ Γ.O ⊔ Γ.U),
      (perspectivity hp_atom Γ.hU Γ.hC Γ.hO Γ.hU hUC Γ.hOU hp_not_UC hp_not_l h_coplanar2
        (perspectivity Γ.hE_atom Γ.hO Γ.hU Γ.hU Γ.hC Γ.hOU hUC hE_not_l hE_not_UC h_coplanar1
          ⟨x, hx, hx_on⟩)).val = coord_add Γ a x := by
    intro x hx hx_on
    rw [perspectivity_val hp_atom Γ.hU Γ.hC Γ.hO Γ.hU hUC Γ.hOU hp_not_UC hp_not_l h_coplanar2,
      perspectivity_val Γ.hE_atom Γ.hO Γ.hU Γ.hU Γ.hC Γ.hOU hUC hE_not_l hE_not_UC h_coplanar1]
    unfold coord_add
    rw [sup_comm ((x ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V))]

  by_contra hbc
  have hne : (⟨b, hb, hb_on⟩ : AtomsOn (Γ.O ⊔ Γ.U)) ≠ ⟨c, hc, hc_on⟩ :=
    fun h => hbc (congrArg Subtype.val h)
  have h1 := perspectivity_injective Γ.hE_atom Γ.hO Γ.hU Γ.hU Γ.hC Γ.hOU hUC
    hE_not_l hE_not_UC h_coplanar1 hne
  have h2 := perspectivity_injective hp_atom Γ.hU Γ.hC Γ.hO Γ.hU hUC Γ.hOU
    hp_not_UC hp_not_l h_coplanar2 h1
  apply h2
  apply Subtype.ext
  rw [hval b hb hb_on, hval c hc hc_on, h_eq]


theorem coord_add_right_cancel (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hac : a ≠ c) (hbc : b ≠ c)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q)
    (h_eq : coord_add Γ a c = coord_add Γ b c) : a = b := by
  have h1 := coord_add_comm Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U hac
    R hR hR_not h_irred
  have h2 := coord_add_comm Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U hbc
    R hR hR_not h_irred
  exact coord_add_left_cancel Γ c a b hc ha hb hc_on ha_on hb_on hc_ne_U
    (by rw [← h1, ← h2, h_eq])


/-- info: 'Foam.Bridges.perspectivity_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms perspectivity_val

/-- info: 'Foam.Bridges.coord_add_left_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_add_left_cancel

/-- info: 'Foam.Bridges.coord_add_right_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_add_right_cancel

end Foam.Bridges
