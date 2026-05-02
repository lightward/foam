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

  Definition + atom + on-l + right inverse (a · a⁻¹ = I) PROVEN.
  Non-degeneracy: `coord_inv_ne_O`, `coord_inv_ne_U` PROVEN (warm-ups,
    they reduce to `sigma'_ne_O` / `sigma'_ne_E` via covering arguments).
  Left inverse (a⁻¹ · a = I) — OPEN. Plan below.

## Left inverse plan: a⁻¹ · a = I

The coord_mul expansion gives goal `(σ_a ⊔ d_{a⁻¹}) ⊓ l = I`, where
  σ_a       := (O ⊔ C) ⊓ (a ⊔ E_I)            -- E_I-projection of a
  d_{a⁻¹}   := (a⁻¹ ⊔ C) ⊓ m                  -- C-projection of a⁻¹

The geometric content reduces to: σ_a = σ'_{a⁻¹}, where
  σ'_{a⁻¹} := (O ⊔ C) ⊓ (I ⊔ d_{a⁻¹})         -- I-projection of d_{a⁻¹}

Equivalently: σ_a, I, d_{a⁻¹} are collinear (i.e., I ≤ σ_a ⊔ d_{a⁻¹}).
Equivalently: `coord_inv` is involutive (`coord_inv (coord_inv a) = a`).

Once σ_a ≤ I ⊔ d_{a⁻¹} is in hand, the rest is mechanical:
  σ_a ⊔ d_{a⁻¹} = I ⊔ d_{a⁻¹}   (covering at d_{a⁻¹}, since σ_a ≠ d_{a⁻¹})
  (I ⊔ d_{a⁻¹}) ⊓ l = I         (`line_direction`, since d_{a⁻¹} ∉ l)

### Desargues setup: center C, two triangles

  T₁ := (a, a⁻¹, σ_a)        on (l, l, O⊔C)
  T₂ := (d_a, d_{a⁻¹}, σ')   on (m, m, O⊔C)

  Perspective from C:
    d_a    ≤ C ⊔ a       [d_a := (a⊔C)⊓m by construction]
    d_{a⁻¹} ≤ C ⊔ a⁻¹     [analogously]
    σ'     ≤ C ⊔ σ_a     [σ', σ_a, C all on the line O⊔C, given σ_a ≠ C]

`desargues_planar` produces an axis ℓ (≤ π, ≠ π) containing the three
side intersections:
  X₁₂ := (a⊔a⁻¹) ⊓ (d_a⊔d_{a⁻¹}) = U                  [l ⊓ m]
  X₁₃ := (a⊔σ_a) ⊓ (d_a⊔σ')      = (a⊔E_I) ⊓ (I⊔d_a)  [via σ_a ≤ a⊔E_I, σ' ≤ I⊔d_a]
  X₂₃ := (a⁻¹⊔σ_a) ⊓ (d_{a⁻¹}⊔σ')

The remaining work is reading X₂₃ to extract σ_a ≤ I⊔d_{a⁻¹}. The cleanest
path is likely a **second** Desargues, analogous to `coord_second_desargues`
in `FTPGAddComm.lean` — it consumes the first axis content and closes the
target collinearity. (See `coord_add_left_neg` in `FTPGNeg.lean` for the
double-Desargues pattern in the additive case.)

### Suggested first move next session

Build the multiplicative analogue lemmas

  coord_first_desargues_mul  Γ ha ha_inv ha_on hinv_on ... R hR hR_not h_irred :
    (a⊔σ_a) ⊓ (d_a⊔σ') ≤ U⊔(some axis description)
  coord_second_desargues_mul Γ ... (axis_content_from_first) :
    (a⁻¹⊔σ_a) ⊓ (d_{a⁻¹}⊔σ') ≤ I⊔(something extracting collinearity)

paralleling `FTPGAddComm.coord_first_desargues` (~600 lines) and
`coord_second_desargues` (~800 lines). Then `coord_mul_left_inv` is
~30 lines like `coord_add_left_neg` (~250 lines including its char-2
case-split).

Char-2 case (a = a⁻¹) needs a separate covering argument like
`coord_add_left_neg`'s `ha_eq_na` branch — when a is self-inverse, the
two triangles collapse and the axis identity is replaced by a direct
covering computation.

Hypotheses needed for the headline theorem (matching FTPGNeg):
  ha : IsAtom a, ha_on : a ≤ l, ha_ne_O, ha_ne_U
  R, hR : IsAtom R, hR_not : ¬ R ≤ π, h_irred (third atom on each line)
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

/-- `coord_inv Γ a ≠ O`. If a⁻¹ = O then σ'⊔E_I collapses to O⊔E_I (covering at E_I),
    forcing σ' ≤ (O⊔C)⊓(O⊔E_I) = O, contradicting `sigma'_ne_O`. -/
theorem coord_inv_ne_O (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    coord_inv Γ a ≠ Γ.O := by
  unfold coord_inv
  set σ' := (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) with hσ'_def
  intro h
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have hσ'_ne_EI := sigma'_ne_E_I Γ a
  -- Step 1: O ≤ σ' ⊔ E_I.
  have hO_le_σEI : Γ.O ≤ σ' ⊔ Γ.E_I := h.symm.le.trans inf_le_left
  -- Step 2: σ' ⊔ E_I = O ⊔ E_I (covering at E_I).
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
  -- Step 3: σ' ≤ O ⊔ E_I, σ' ≤ O ⊔ C, so σ' ≤ (O⊔C) ⊓ (O⊔E_I) = O.
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

/-- `coord_inv Γ a ≠ U`. If a⁻¹ = U then σ'⊔E_I collapses to U⊔E_I ≤ m,
    forcing σ' ≤ E (= (O⊔C)⊓m), contradicting `sigma'_ne_E`. -/
theorem coord_inv_ne_U (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_O : a ≠ Γ.O) :
    coord_inv Γ a ≠ Γ.U := by
  unfold coord_inv
  set σ' := (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) with hσ'_def
  intro h
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have hσ'_ne_EI := sigma'_ne_E_I Γ a
  -- Step 1: U ≤ σ' ⊔ E_I.
  have hU_le_σEI : Γ.U ≤ σ' ⊔ Γ.E_I := h.symm.le.trans inf_le_left
  -- Step 2: σ' ⊔ E_I = U ⊔ E_I (covering at E_I).
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
  -- Step 3: σ' ≤ U⊔E_I ≤ m, and σ' ≤ O⊔C, so σ' ≤ (O⊔C)⊓m = E.
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

/-- **σ_{a⁻¹} = σ'_a.** The E_I-projection of `a⁻¹` from `l` to `O⊔C` lands on
    the same atom as the I-projection of `d_a` from `m` to `O⊔C`.

    This is the algebraic content already implicit in `coord_mul_right_inv`'s
    Steps 1+2, factored out as a reusable identity. Used in the left-inverse
    argument: it says σ' ≤ a⁻¹ ⊔ E_I, which lets the Desargues setup
    `T₁ = (a, a⁻¹, σ_a)`, `T₂ = (d_a, d_{a⁻¹}, σ')` close cleanly. -/
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

/-! ## Open frontier: left multiplicative inverse `a⁻¹ · a = I`

This section names the open geometric content as a single `sorry`'d lemma —
`sigma_a_le_I_sup_d_inv` — and reduces the headline `coord_mul_left_inv` to
it via the same closing pattern as `coord_mul_right_inv`. Once that lemma is
discharged (via the planned double-Desargues argument or via
`coord_mul_assoc`), the headline closes mechanically. See top-of-file
docstring for the geometric plan.
-/

/-- `σ_a := (O ⊔ C) ⊓ (a ⊔ E_I)`: the E_I-projection of `a` from `l` onto
    `O⊔C`. Same construction as the second perspectivity in `coord_mul Γ ? a`.
    Atom by `perspect_atom` (pivot `E_I`, line `O⊔C`). -/
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

/-- `σ_a ≠ E`. If `σ_a = E` then covering at `E_I` forces `a ⊔ E_I = E_I ⊔ E`,
    so `a ≤ m`, hence `a ≤ l ⊓ m = U`, contradicting `ha_ne_U`. -/
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

/-- **OPEN GEOMETRIC CONTENT for the generic case of `coord_mul_left_inv`.**

For atoms `a` on `l` distinct from their own inverse (`a ≠ coord_inv Γ a`),
`σ_a` lies on `I ⊔ d_{a⁻¹}`. The char-2 case (`a = coord_inv Γ a`) follows
directly from `sigma_inv_eq_sigma_prime` — see `sigma_a_le_I_sup_d_inv`.

The intended proof: Desargues from center `C` on triangles
`T₁ = (a, a⁻¹, σ_a)` and `T₂ = (d_a, d_{a⁻¹}, σ')`.
* `X₁₂ = (a⊔a⁻¹) ⊓ (d_a⊔d_{a⁻¹}) = U` (l ⊓ m).
* `X₁₃ = (a⊔σ_a) ⊓ (d_a⊔σ') = (a⊔E_I) ⊓ (I⊔d_a)` (using σ_a ≤ a⊔E_I, σ' ≤ I⊔d_a).
* `X₂₃ = (a⁻¹⊔σ_a) ⊓ (d_{a⁻¹}⊔σ')`.
The axis content `X₂₃ ≤ U ⊔ X₁₃` is then unpacked via a second Desargues
(or `collinear_of_common_bound`) to `σ_a ≤ I ⊔ d_{a⁻¹}`. See
`coord_first_desargues` / `coord_second_desargues` in `FTPGAddComm.lean`
for the additive precedent (~600 + ~800 lines).

Distinctness conditions for the Desargues call (all derivable from the
existing hypotheses + `a ≠ coord_inv Γ a`):
* `a ≠ a⁻¹` — case hypothesis.
* `d_a ≠ d_{a⁻¹}` — equivalent to `a ≠ a⁻¹` via the C-perspectivity.
* `a ≠ σ_a`, `a⁻¹ ≠ σ_a` — atoms on `l` vs `O⊔C` (intersect at `O`); use
  `ha_ne_O`, `coord_inv_ne_O`.
* `σ_a ≠ σ'` — both atoms on `O⊔C`; equality would force them to be `E_I`
  via the helper, but `E_I ∉ O⊔C`.
* `σ_a ≠ C` — equivalent to `a ≠ I` (a separate sub-case-split needed; see
  the analysis in the docstring above).

The char-2 case (`a = coord_inv Γ a`) is closed by the helper directly. -/
private theorem sigma_a_le_I_sup_d_inv_distinct (Γ : CoordSystem L)
    {a : L} (_ha : IsAtom a) (_ha_on : a ≤ Γ.O ⊔ Γ.U)
    (_ha_ne_O : a ≠ Γ.O) (_ha_ne_U : a ≠ Γ.U)
    (_ha_ne_inv : a ≠ coord_inv Γ a)
    (_R : L) (_hR : IsAtom _R) (_hR_not : ¬ _R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (_h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤
      Γ.I ⊔ (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  sorry

/-- **`σ_a ≤ I ⊔ d_{a⁻¹}` — the geometric content of `coord_mul_left_inv`.**

Splits on whether `a` equals its own multiplicative inverse:
* **char-2 case** (`a = coord_inv Γ a`): closed by `sigma_inv_eq_sigma_prime`
  applied to itself — substituting `coord_inv a = a` on both sides of the
  helper makes its conclusion exactly `σ_a = (O⊔C)⊓(I⊔d_a)`, and
  `inf_le_right` gives `σ_a ≤ I⊔d_a = I⊔d_{a⁻¹}`. No Desargues required.
* **generic case** (`a ≠ coord_inv Γ a`): delegates to
  `sigma_a_le_I_sup_d_inv_distinct`, the still-open Desargues content. -/
private theorem sigma_a_le_I_sup_d_inv (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤
      Γ.I ⊔ (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  by_cases ha_self : a = coord_inv Γ a
  · -- Char-2 case: helper applied to a, then substituting a = coord_inv a
    -- on both sides gives (O⊔C)⊓(a⊔E_I) = (O⊔C)⊓(I⊔d_a) ≤ I⊔d_a = I⊔d_{coord_inv a}.
    have h := sigma_inv_eq_sigma_prime Γ ha ha_on ha_ne_U
    rw [← ha_self] at h
    rw [h, ← ha_self]
    exact inf_le_right
  · exact sigma_a_le_I_sup_d_inv_distinct Γ ha ha_on ha_ne_O ha_ne_U
      ha_self R hR hR_not h_irred

/-- **Left multiplicative inverse: `a⁻¹ · a = I`.**

Reduces to `sigma_a_le_I_sup_d_inv` (the sole open geometric content) via
the same closing pattern as `coord_mul_right_inv`: σ_a-collinearity upgrades
to `σ_a ⊔ d_{a⁻¹} = I ⊔ d_{a⁻¹}` by covering at `d_{a⁻¹}`, and then
`(I ⊔ d_{a⁻¹}) ⊓ l = I` by `line_direction`. -/
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
  -- Step 1: σ_a ≤ I ⊔ d_inv (the open geometric content).
  have hσa_le_Id : σ_a ≤ Γ.I ⊔ d_inv :=
    sigma_a_le_I_sup_d_inv Γ ha ha_on ha_ne_O ha_ne_U R hR hR_not h_irred
  -- Step 2: σ_a ≠ d_inv (else σ_a ≤ m ∧ σ_a ≤ O⊔C ⇒ σ_a ≤ E ⇒ σ_a = E, contradicts sigma_a_ne_E).
  have hσa_ne_dinv : σ_a ≠ d_inv := by
    intro h
    have hσa_le_m : σ_a ≤ Γ.U ⊔ Γ.V := h.symm ▸ inf_le_right
    have hσa_le_OC : σ_a ≤ Γ.O ⊔ Γ.C := inf_le_left
    have hσa_le_E : σ_a ≤ Γ.E := by
      unfold CoordSystem.E CoordSystem.m
      exact le_inf hσa_le_OC hσa_le_m
    exact hσa_ne_E ((Γ.hE_atom.le_iff.mp hσa_le_E).resolve_left hσa_atom.1)
  -- Step 3: covering at d_inv: σ_a ⊔ d_inv = I ⊔ d_inv.
  have hσd_le_Id : σ_a ⊔ d_inv ≤ Γ.I ⊔ d_inv := sup_le hσa_le_Id le_sup_right
  have hd_lt_σd : d_inv < σ_a ⊔ d_inv := lt_of_le_of_ne le_sup_right
    (fun h => hσa_ne_dinv ((hd_inv_atom.le_iff.mp
      (le_sup_left.trans h.symm.le)).resolve_left hσa_atom.1))
  have hcov_d : d_inv ⋖ Γ.I ⊔ d_inv := by
    have h2 : d_inv ⋖ d_inv ⊔ Γ.I := atom_covBy_join hd_inv_atom Γ.hI hI_ne_dinv.symm
    exact (sup_comm d_inv Γ.I) ▸ h2
  have hσd_eq : σ_a ⊔ d_inv = Γ.I ⊔ d_inv :=
    (hcov_d.eq_or_eq hd_lt_σd.le hσd_le_Id).resolve_left (ne_of_gt hd_lt_σd)
  -- Step 4: combine — the goal is (σ_a ⊔ d_inv) ⊓ l = I.
  show (σ_a ⊔ d_inv) ⊓ (Γ.O ⊔ Γ.U) = Γ.I
  rw [hσd_eq, show Γ.I ⊔ d_inv = d_inv ⊔ Γ.I from sup_comm _ _]
  exact line_direction hd_inv_atom hd_inv_not_l Γ.hI_on

end Foam.FTPGExplore
