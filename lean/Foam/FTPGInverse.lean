/-
# Multiplicative inverse (coord_inv) and a · a⁻¹ = I

## Construction

  d_a = (a ⊔ C) ⊓ m            -- projection of a onto m through C
  σ' = (O ⊔ C) ⊓ (I ⊔ d_a)     -- the point on O⊔C such that σ', I, d_a are
                                  collinear (i.e., σ' = (O⊔C) projection of d_a
                                  along the line through I)
  a⁻¹ = (σ' ⊔ E_I) ⊓ l         -- project σ' back onto l through E_I

Equivalently, a⁻¹ is the unique atom on l satisfying `coord_mul a (a⁻¹) = I`.
The proof: when we expand `coord_mul a (a⁻¹)`, the first leg recovers σ'
((O⊔C) ⊓ (a⁻¹ ⊔ E_I) = σ' by perspectivity inversion through E_I), and σ'
sits on the line I⊔d_a by construction, so σ' ⊔ d_a = I ⊔ d_a (covering),
and `(I ⊔ d_a) ⊓ l = I` by `line_direction` (d_a ∉ l).

## Status

  Definition + atom + on-l + right inverse (a · a⁻¹ = I).
  Left inverse (a⁻¹ · a = I) is open — standard route is via mul-assoc
  (not yet proven) or a direct geometric argument.
-/

import Foam.FTPGMul

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-- The multiplicative inverse of a coordinate. -/
noncomputable def coord_inv (Γ : CoordSystem L) (a : L) : L :=
  ((Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U)

/-- coord_inv is on l. -/
theorem coord_inv_on_l (Γ : CoordSystem L) (a : L) :
    coord_inv Γ a ≤ Γ.O ⊔ Γ.U := by
  unfold coord_inv; exact inf_le_right

/-- `l ⋖ π`. (Reusable helper, local.) -/
private theorem l_covBy_π_inv (Γ : CoordSystem L) :
    (Γ.O ⊔ Γ.U) ⋖ (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
  have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
    (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
  have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
  rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this

/-! ## Helper lemmas on `d_a` and the inverse-projection point `σ'`. -/

/-- `d_a = (a ⊔ C) ⊓ m` is an atom when a is an atom (on l). -/
private theorem d_a_atom (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    IsAtom ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by
  have hAC : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  exact perspect_atom Γ.hC ha hAC Γ.hU Γ.hV hUV Γ.hC_not_m
    (sup_le (ha_on.trans (le_sup_left.trans Γ.m_sup_C_eq_π.symm.le)) le_sup_right)

/-- `d_a` is not on l (when a ≠ U). -/
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

/-- `d_a ≠ E` when a ≠ O.
    `d_a = E` would mean E ≤ a⊔C, hence (via E⊔C = O⊔C) O⊔C ≤ a⊔C, hence O ≤ a⊔C,
    then via l ∩ (a⊔C) = a we get O = a. -/
private theorem d_a_ne_E (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) :
    (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠ Γ.E := by
  intro hd_eq_E
  have hE_le_aC : Γ.E ≤ a ⊔ Γ.C := hd_eq_E.symm.le.trans inf_le_left
  -- E ⊔ C = O ⊔ C (line through E, C is the line through O, C).
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

/-- `I ≠ d_a`: I on l, d_a on m, I = d_a would force I = U. -/
private theorem I_ne_d_a (Γ : CoordSystem L)
    {a : L} (_ha : IsAtom a) (_ha_on : a ≤ Γ.O ⊔ Γ.U) :
    Γ.I ≠ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  intro h
  have hI_le_m : Γ.I ≤ Γ.U ⊔ Γ.V := h.symm ▸ inf_le_right
  have hI_le_lm : Γ.I ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) := le_inf Γ.hI_on hI_le_m
  rw [Γ.l_inf_m_eq_U] at hI_le_lm
  exact Γ.hUI ((Γ.hU.le_iff.mp hI_le_lm).resolve_left Γ.hI.1).symm

/-- `I` is not on `O⊔C`. -/
private theorem hI_not_OC (Γ : CoordSystem L) : ¬ Γ.I ≤ Γ.O ⊔ Γ.C := by
  intro h
  have hI_le : Γ.I ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) := le_inf Γ.hI_on h
  rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _,
      inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)] at hI_le
  exact Γ.hOI ((Γ.hO.le_iff.mp hI_le).resolve_left Γ.hI.1).symm

/-- `σ' = (O⊔C) ⊓ (I ⊔ d_a)` is an atom. -/
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

/-- `σ' ≠ E_I`: σ' is on O⊔C, E_I is not. -/
private theorem sigma'_ne_E_I (Γ : CoordSystem L) (a : L) :
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≠ Γ.E_I :=
  fun h => Γ.hE_I_not_OC (h ▸ inf_le_left)

/-- `σ' ≠ O` (so coord_inv ≠ O). σ' = O would force O ≤ I⊔d_a, then l = I⊔O ≤ I⊔d_a,
    hence U ≤ I⊔d_a, then via line_direction U = d_a, contradicting `d_a_not_l`. -/
private theorem sigma'_ne_O (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≠ Γ.O := by
  intro h
  have hO_le_Id : Γ.O ≤ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := h.symm ▸ inf_le_right
  -- l = I ⊔ O (atom join, both on l, distinct).
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
  -- (I ⊔ d_a) ⊓ m = d_a (line_direction).
  have hId_inf_m : (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.U ⊔ Γ.V) =
      (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    line_direction Γ.hI Γ.hI_not_m inf_le_right
  have hU_le_inf : Γ.U ≤ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.U ⊔ Γ.V) :=
    le_inf hU_le_Id le_sup_left
  rw [hId_inf_m] at hU_le_inf
  have hU_eq_d : Γ.U = (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    ((d_a_atom Γ ha ha_on).le_iff.mp hU_le_inf).resolve_left Γ.hU.1
  exact d_a_not_l Γ ha ha_on ha_ne_U (hU_eq_d.symm.le.trans le_sup_right)

/-- `σ' ≠ E`: σ' = E would force d_a = E, contradicting `d_a_ne_E`. -/
private theorem sigma'_ne_E (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) :
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≠ Γ.E := by
  intro h
  -- σ' = E ⇒ E ≤ I ⊔ d_a; since E ≤ m and (I⊔d_a)⊓m = d_a, conclude E = d_a.
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

/-! ## Atom-ness of `coord_inv`. -/

/-- `coord_inv Γ a` is an atom. -/
theorem coord_inv_atom (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    IsAtom (coord_inv Γ a) := by
  unfold coord_inv
  set σ' := (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) with hσ'_def
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have hσ'_ne_EI := sigma'_ne_E_I Γ a
  have hσ'_le_OC : σ' ≤ Γ.O ⊔ Γ.C := inf_le_left
  -- σ' is not on l (would force σ' = O, contradicting sigma'_ne_O).
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

/-! ## Right multiplicative inverse: `a · a⁻¹ = I`. -/

/-- **Right multiplicative inverse: `a · a⁻¹ = I`.** -/
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
  -- Step 1: inv_a ⊔ E_I = σ' ⊔ E_I (covBy at E_I).
  have hinvEI_le : inv_a ⊔ Γ.E_I ≤ σ' ⊔ Γ.E_I := sup_le hinv_le_σEI le_sup_right
  have hEI_lt_invEI : Γ.E_I < inv_a ⊔ Γ.E_I := lt_of_le_of_ne le_sup_right
    (fun h => hinv_ne_EI ((Γ.hE_I_atom.le_iff.mp
      (le_sup_left.trans h.symm.le)).resolve_left hinv_atom.1))
  have hcov_EI : Γ.E_I ⋖ σ' ⊔ Γ.E_I := by
    have := atom_covBy_join Γ.hE_I_atom hσ'_atom (Ne.symm hσ'_ne_EI)
    rwa [sup_comm] at this
  have hinvEI_eq : inv_a ⊔ Γ.E_I = σ' ⊔ Γ.E_I :=
    (hcov_EI.eq_or_eq hEI_lt_invEI.le hinvEI_le).resolve_left (ne_of_gt hEI_lt_invEI)
  -- Step 2: (O⊔C) ⊓ (σ' ⊔ E_I) = σ' (line_direction: σ' on O⊔C, E_I not on O⊔C).
  have hσ'_le_OC : σ' ≤ Γ.O ⊔ Γ.C := inf_le_left
  have h_dir_OC : (σ' ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) = σ' := by
    rw [show σ' ⊔ Γ.E_I = Γ.E_I ⊔ σ' from sup_comm _ _]
    exact line_direction Γ.hE_I_atom Γ.hE_I_not_OC hσ'_le_OC
  have hOC_inf_invEI : (Γ.O ⊔ Γ.C) ⊓ (inv_a ⊔ Γ.E_I) = σ' := by
    rw [hinvEI_eq, show (Γ.O ⊔ Γ.C) ⊓ (σ' ⊔ Γ.E_I) =
        (σ' ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) from inf_comm _ _, h_dir_OC]
  -- Step 3: σ' ⊔ d_a = I ⊔ d_a (covBy at d_a).
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
  -- Step 4: combine.
  show ((Γ.O ⊔ Γ.C) ⊓ (inv_a ⊔ Γ.E_I) ⊔ d_a) ⊓ (Γ.O ⊔ Γ.U) = Γ.I
  rw [hOC_inf_invEI, hσd_eq]
  -- Goal: (I ⊔ d_a) ⊓ l = I.
  rw [show Γ.I ⊔ d_a = d_a ⊔ Γ.I from sup_comm _ _]
  exact line_direction hd_atom (d_a_not_l Γ ha ha_on ha_ne_U) Γ.hI_on

end Foam.FTPGExplore
