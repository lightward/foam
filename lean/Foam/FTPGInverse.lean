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

/-- `σ' ≠ C` when `a ≠ I`. If `σ' = C`, then `C ≤ I⊔d_a`, so `I⊔C = I⊔d_a`
    by covering at `I`. Hence `d_a ≤ I⊔C`; combined with `d_a ≤ a⊔C` and
    `(a⊔C)⊓(I⊔C) = C` (lines through `C` meet at `C`, since `a ≠ I`),
    `d_a ≤ C`, contradicting `hC_not_m`.

    Used as **`hob₃ : C ≠ σ'`** in `coord_first_desargues_mul`'s
    `desargues_planar` call (center-vs-vertex distinctness). -/
private theorem sigma'_ne_C (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_I : a ≠ Γ.I) :
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≠ Γ.C := by
  intro h
  have hC_le_Id : Γ.C ≤ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := h.symm.le.trans inf_le_right
  have hd_atom := d_a_atom Γ ha ha_on
  have hI_ne_C : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hI_ne_d := I_ne_d_a Γ ha ha_on
  have hcov_IC : Γ.I ⋖ Γ.I ⊔ Γ.C := atom_covBy_join Γ.hI Γ.hC hI_ne_C
  have hcov_Id : Γ.I ⋖ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    atom_covBy_join Γ.hI hd_atom hI_ne_d
  have hIC_le_Id : Γ.I ⊔ Γ.C ≤ Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    sup_le le_sup_left hC_le_Id
  have hIC_eq : Γ.I ⊔ Γ.C = Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    (hcov_Id.eq_or_eq hcov_IC.lt.le hIC_le_Id).resolve_left (ne_of_gt hcov_IC.lt)
  have hd_le_IC : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.I ⊔ Γ.C :=
    (le_sup_right : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤
      Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)).trans hIC_eq.symm.le
  have hmeet : (a ⊔ Γ.C) ⊓ (Γ.I ⊔ Γ.C) = Γ.C :=
    Γ.lines_through_C_meet ha Γ.hI ha_ne_I ha_on Γ.hI_on
  have hd_le_aC : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ a ⊔ Γ.C := inf_le_left
  have hd_le_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.C :=
    (le_inf hd_le_aC hd_le_IC).trans hmeet.le
  have hd_eq_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.C :=
    (Γ.hC.le_iff.mp hd_le_C).resolve_left hd_atom.1
  exact Γ.hC_not_m
    (hd_eq_C ▸ (inf_le_right : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V))

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

/-- **`coord_inv` fixes I:** `coord_inv Γ I = I`. (`I` is its own multiplicative
    inverse — the multiplicative identity is self-inverse.)

    Computes through:
    * `d_I = (I⊔C)⊓m = E_I` (by definition of E_I)
    * `I⊔E_I = I⊔C` (covering at `I`; `E_I ≤ I⊔C`, `E_I ≠ I`)
    * `σ'_I = (O⊔C)⊓(I⊔C) = C` (`modular_intersection`: lines through the
      shared atom `C`, with `I` non-collinear via `hI_not_OC`)
    * `C⊔E_I = I⊔C` (covering at `C`)
    * `(I⊔C)⊓l = I` (`line_direction`: `C ∉ l`, `I ∈ l`)

    This lemma also confirms that `a = I` falls into the **char-2** case of
    `sigma_a_le_I_sup_d_inv` (since `coord_inv I = I` makes `a = coord_inv a`),
    which means the eventual `sigma_a_le_I_sup_d_inv_distinct` proof can
    safely assume `a ≠ I` — eliminating the σ_a = C / Desargues-center
    collision sub-case. -/
theorem coord_inv_I_eq_I (Γ : CoordSystem L) : coord_inv Γ Γ.I = Γ.I := by
  unfold coord_inv
  -- d_I = E_I (by def of E_I)
  have hd_I : (Γ.I ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I := rfl
  rw [hd_I]
  -- distinctness
  have hI_ne_C : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hI_ne_EI : Γ.I ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ Γ.hI_on)
  have hC_ne_EI : Γ.C ≠ Γ.E_I := fun h => Γ.hC_not_m (h ▸ Γ.hE_I_on_m)
  have hOC_ne : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  -- I⊔E_I = I⊔C (covering at I)
  have hcov_I_IC : Γ.I ⋖ Γ.I ⊔ Γ.C := atom_covBy_join Γ.hI Γ.hC hI_ne_C
  have hI_lt_IE : Γ.I < Γ.I ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
    (fun h => hI_ne_EI ((Γ.hI.le_iff.mp
      (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_I_atom.1).symm)
  have hIE_eq_IC : Γ.I ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
    (hcov_I_IC.eq_or_eq hI_lt_IE.le (sup_le le_sup_left Γ.hE_I_le_IC)).resolve_left
      (ne_of_gt hI_lt_IE)
  rw [hIE_eq_IC]
  -- (O⊔C)⊓(I⊔C) = C (modular_intersection: shared atom C, non-collinear I ≰ O⊔C)
  have hOC_inf_IC : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ Γ.C) = Γ.C := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _,
        show Γ.I ⊔ Γ.C = Γ.C ⊔ Γ.I from sup_comm _ _]
    exact modular_intersection Γ.hC Γ.hO Γ.hI hOC_ne.symm hI_ne_C.symm Γ.hOI
      (sup_comm Γ.O Γ.C ▸ hI_not_OC Γ)
  rw [hOC_inf_IC]
  -- C⊔E_I = I⊔C (covering at C)
  have hC_lt_CE : Γ.C < Γ.C ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
    (fun h => hC_ne_EI ((Γ.hC.le_iff.mp
      (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_I_atom.1).symm)
  have hcov_C_IC : Γ.C ⋖ Γ.I ⊔ Γ.C := by
    have := atom_covBy_join Γ.hC Γ.hI hI_ne_C.symm
    rwa [sup_comm] at this
  have hCE_eq_IC : Γ.C ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
    (hcov_C_IC.eq_or_eq hC_lt_CE.le (sup_le le_sup_right Γ.hE_I_le_IC)).resolve_left
      (ne_of_gt hC_lt_CE)
  rw [hCE_eq_IC]
  -- (I⊔C)⊓l = I (line_direction: C ∉ l, I ∈ l)
  rw [show Γ.I ⊔ Γ.C = Γ.C ⊔ Γ.I from sup_comm _ _]
  exact line_direction Γ.hC Γ.hC_not_l Γ.hI_on

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

/-- `d_a ≠ d_{a⁻¹}` when `a ≠ a⁻¹`. The C-perspectivity `x ↦ (x⊔C)⊓m` from
    `l` to `m` is injective on atoms: lines `a⊔C` and `a⁻¹⊔C` meet only at
    `C` (by `lines_through_C_meet`), and `C ∉ m`, so any common atom on `m`
    is forced to equal `C`, contradiction. This is the **X₁₂ distinctness
    condition** in the Desargues setup of `sigma_a_le_I_sup_d_inv_distinct`
    — the case hypothesis `a ≠ coord_inv a` carries directly to the
    triangle T₂'s vertices. -/
private theorem d_a_ne_d_inv (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U)
    (ha_ne_inv : a ≠ coord_inv Γ a) :
    (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≠ (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  intro h
  set d_a := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
  have hd_atom : IsAtom d_a := d_a_atom Γ ha ha_on
  have hinv_atom : IsAtom (coord_inv Γ a) := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_on : coord_inv Γ a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a
  -- d_a ≤ a⊔C (left projection); d_a = d_{a⁻¹} so d_a ≤ a⁻¹⊔C as well.
  have hd_le_aC : d_a ≤ a ⊔ Γ.C := inf_le_left
  have hd_le_invC : d_a ≤ coord_inv Γ a ⊔ Γ.C := h.le.trans inf_le_left
  -- The two C-lines meet at C.
  have hmeet : (a ⊔ Γ.C) ⊓ (coord_inv Γ a ⊔ Γ.C) = Γ.C :=
    Γ.lines_through_C_meet ha hinv_atom ha_ne_inv ha_on hinv_on
  have hd_le_C : d_a ≤ Γ.C := hmeet ▸ le_inf hd_le_aC hd_le_invC
  have hd_eq_C : d_a = Γ.C :=
    (Γ.hC.le_iff.mp hd_le_C).resolve_left hd_atom.1
  exact Γ.hC_not_m (hd_eq_C ▸ (inf_le_right : d_a ≤ Γ.U ⊔ Γ.V))

/-- `a ≠ I` in the generic-`a` (i.e., `a ≠ coord_inv a`) branch.
    By `coord_inv_I_eq_I`, `a = I` would force `a = coord_inv a`. -/
private theorem ha_ne_I_of_distinct (Γ : CoordSystem L)
    {a : L} (_ha : IsAtom a) (ha_ne_inv : a ≠ coord_inv Γ a) :
    a ≠ Γ.I := by
  intro h
  exact ha_ne_inv (h.trans (coord_inv_I_eq_I Γ).symm |>.trans (h ▸ rfl))

/-- **σ_a ≠ C** when `a ≠ I`. `σ_a = C` would force `C ≤ a⊔E_I`, hence
    `a⊔C ≤ a⊔E_I` (covering at `a`), and since both have height 2 we get
    `a⊔C = a⊔E_I`. Then `E_I ≤ a⊔C`, and via `(a⊔C)⊓m = d_a`, `E_I ≤ d_a`,
    so `E_I = d_a` (atoms). But `d_a` is the projection of `a` from `C`,
    while `E_I` is the projection of `I` from `C`; `d_a = E_I` then forces
    `a = I` by injectivity of C-perspectivity from `l`. -/
private theorem sigma_a_ne_C (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_I : a ≠ Γ.I) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ Γ.C := by
  intro h
  -- C ≤ a ⊔ E_I.
  have hC_le_aEI : Γ.C ≤ a ⊔ Γ.E_I := h.symm.le.trans inf_le_right
  -- a⊔C ≤ a⊔E_I, and a⊔C ⋖ a (well, a ⋖ a⊔C) so a⊔C = a⊔E_I.
  have ha_ne_C : a ≠ Γ.C := fun he => Γ.hC_not_l (he ▸ ha_on)
  have ha_ne_EI : a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ ha_on)
  have h_aC_le : a ⊔ Γ.C ≤ a ⊔ Γ.E_I := sup_le le_sup_left hC_le_aEI
  have hcov_a_aC : a ⋖ a ⊔ Γ.C := atom_covBy_join ha Γ.hC ha_ne_C
  have hcov_a_aEI : a ⋖ a ⊔ Γ.E_I := atom_covBy_join ha Γ.hE_I_atom ha_ne_EI
  have h_aC_lt : a < a ⊔ Γ.C := hcov_a_aC.lt
  have h_aC_eq_aEI : a ⊔ Γ.C = a ⊔ Γ.E_I :=
    (hcov_a_aEI.eq_or_eq h_aC_lt.le h_aC_le).resolve_left (ne_of_gt h_aC_lt)
  -- E_I ≤ a⊔C, and E_I ≤ m, so E_I ≤ (a⊔C)⊓m = d_a.
  have hEI_le_aC : Γ.E_I ≤ a ⊔ Γ.C := h_aC_eq_aEI.symm ▸ (le_sup_right : Γ.E_I ≤ a ⊔ Γ.E_I)
  have hEI_le_d : Γ.E_I ≤ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
    le_inf hEI_le_aC Γ.hE_I_on_m
  -- So E_I ≤ d_a (atoms): E_I = d_a.
  have hd_atom : IsAtom ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := d_a_atom Γ ha ha_on
  have hd_eq_EI : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I :=
    ((hd_atom.le_iff.mp hEI_le_d).resolve_left Γ.hE_I_atom.1).symm
  -- d_a = E_I means E_I ≤ a⊔C, and (a⊔C)⊓l = a, but also E_I = d_I = (I⊔C)⊓m,
  -- so d_a = d_I, hence a = I (perspectivity injection).
  -- Concretely: d_a ≤ a⊔C and d_a = E_I = d_I ≤ I⊔C; both lines through C meet at C
  -- iff a ≠ I; if a ≠ I, then d_a ≤ C (= meet), so d_a = C, contradicting hC_not_m.
  have hd_le_IC : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.I ⊔ Γ.C := by
    rw [hd_eq_EI]; exact Γ.hE_I_le_IC
  have hd_le_aC : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ a ⊔ Γ.C := inf_le_left
  have hmeet : (a ⊔ Γ.C) ⊓ (Γ.I ⊔ Γ.C) = Γ.C :=
    Γ.lines_through_C_meet ha Γ.hI ha_ne_I ha_on Γ.hI_on
  have hd_le_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.C :=
    (le_inf hd_le_aC hd_le_IC).trans hmeet.le
  have hd_eq_C : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.C :=
    (Γ.hC.le_iff.mp hd_le_C).resolve_left hd_atom.1
  exact Γ.hC_not_m (hd_eq_C ▸ (inf_le_right : (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V))

/-- **σ_a ≠ O** when `a ≠ O`. `σ_a = O` forces `O ≤ a⊔E_I` (covering: `a⊔E_I = a⊔O`),
    so `E_I ≤ a⊔O ≤ l`, contradicting `hE_I_not_l`. -/
private theorem sigma_a_ne_O (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_O : a ≠ Γ.O) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ Γ.O := by
  intro h
  have hO_le_aEI : Γ.O ≤ a ⊔ Γ.E_I := h.symm.le.trans inf_le_right
  have ha_ne_EI : a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ ha_on)
  have hcov_a_aEI : a ⋖ a ⊔ Γ.E_I := atom_covBy_join ha Γ.hE_I_atom ha_ne_EI
  have hcov_a_aO : a ⋖ a ⊔ Γ.O := atom_covBy_join ha Γ.hO ha_ne_O
  have hOa_le : a ⊔ Γ.O ≤ a ⊔ Γ.E_I := sup_le le_sup_left hO_le_aEI
  have h_aO_eq : a ⊔ Γ.O = a ⊔ Γ.E_I :=
    (hcov_a_aEI.eq_or_eq hcov_a_aO.lt.le hOa_le).resolve_left (ne_of_gt hcov_a_aO.lt)
  have hEI_le_aO : Γ.E_I ≤ a ⊔ Γ.O :=
    h_aO_eq.symm ▸ (le_sup_right : Γ.E_I ≤ a ⊔ Γ.E_I)
  have haO_le_l : a ⊔ Γ.O ≤ Γ.O ⊔ Γ.U := sup_le ha_on le_sup_left
  exact Γ.hE_I_not_l (hEI_le_aO.trans haO_le_l)

/-- **σ_a ≠ U** (always). `σ_a = U` would put `U` on `O⊔C`, but `U ≤ l ⊓ (O⊔C) = O`,
    so `U = O`, contradicting `hOU`. -/
private theorem sigma_a_ne_U (Γ : CoordSystem L)
    {a : L} (_ha : IsAtom a) (_ha_on : a ≤ Γ.O ⊔ Γ.U) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ Γ.U := by
  intro h
  have hU_le_OC : Γ.U ≤ Γ.O ⊔ Γ.C := h.symm.le.trans inf_le_left
  have hOC_inf_l : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
  have hU_le_O : Γ.U ≤ Γ.O := hOC_inf_l ▸ le_inf le_sup_right hU_le_OC
  exact Γ.hOU.symm ((Γ.hO.le_iff.mp hU_le_O).resolve_left Γ.hU.1)

/-- **σ_a ≠ a** when `a ≠ O`. `σ_a = a` puts `a` on `O⊔C`, so `a ≤ l⊓(O⊔C) = O`. -/
private theorem sigma_a_ne_a (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_O : a ≠ Γ.O) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ a := by
  intro h
  have ha_le_OC : a ≤ Γ.O ⊔ Γ.C := h.symm.le.trans inf_le_left
  have hl_inf_OC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
  have ha_le_O : a ≤ Γ.O := hl_inf_OC ▸ le_inf ha_on ha_le_OC
  exact ha_ne_O ((Γ.hO.le_iff.mp ha_le_O).resolve_left ha.1)

/-- **σ_a ≠ d_a**. `σ_a` is on `O⊔C`, `d_a` on `m`; common atom = `E`, so `σ_a = d_a`
    forces `σ_a = E`, contradicting `sigma_a_ne_E`. -/
private theorem sigma_a_ne_d_a (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  intro h
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have hσa_le_OC : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσa_le_m : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.U ⊔ Γ.V := h.le.trans inf_le_right
  have hσa_le_E : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.E := by
    show (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)
    exact le_inf hσa_le_OC hσa_le_m
  have hσa_eq_E : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) = Γ.E :=
    (Γ.hE_atom.le_iff.mp hσa_le_E).resolve_left hσa_atom.1
  exact sigma_a_ne_E Γ ha ha_on ha_ne_U hσa_eq_E

/-- **`coord_inv a ∉ O⊔C`** when `a ≠ U` (so `coord_inv a ≠ O`). `inv_a` is on
    `l = O⊔U`; if also `inv_a ≤ O⊔C`, then `inv_a ≤ l ⊓ (O⊔C) = O`, hence
    `inv_a = O`, contradicting `coord_inv_ne_O`. -/
private theorem inv_a_not_OC (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    ¬ coord_inv Γ a ≤ Γ.O ⊔ Γ.C := by
  intro h
  have hinv_atom : IsAtom (coord_inv Γ a) := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_on : coord_inv Γ a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a
  have hl_inf_OC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
  have hinv_le_O : coord_inv Γ a ≤ Γ.O := hl_inf_OC ▸ le_inf hinv_on h
  have hinv_eq_O : coord_inv Γ a = Γ.O :=
    (Γ.hO.le_iff.mp hinv_le_O).resolve_left hinv_atom.1
  exact coord_inv_ne_O Γ ha ha_on ha_ne_U hinv_eq_O

/-- **`σ_a ≠ coord_inv a`**. `σ_a` is on `O⊔C` (and not on `l` unless `σ_a = O`),
    while `coord_inv a` is on `l`. Equality would force `σ_a ≤ l ⊓ (O⊔C) = O`,
    so `σ_a = O`, contradicting `sigma_a_ne_O`.

    Used as **vertex distinctness `inv_a ≠ σ_a`** in `coord_first_desargues_mul`'s
    `desargues_planar` call. -/
private theorem sigma_a_ne_inv_a (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠ coord_inv Γ a := by
  intro h
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have hinv_on : coord_inv Γ a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a
  have hσa_le_OC : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσa_le_l : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.U := h.symm ▸ hinv_on
  have hl_inf_OC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
    rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
    exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
  have hσa_le_O : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O :=
    (le_inf hσa_le_l hσa_le_OC).trans hl_inf_OC.le
  have hσa_eq_O : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) = Γ.O :=
    (Γ.hO.le_iff.mp hσa_le_O).resolve_left hσa_atom.1
  exact sigma_a_ne_O Γ ha ha_on ha_ne_O hσa_eq_O

/-- **σ_a ≠ σ'** when `a ≠ coord_inv a`. The E_I-perspectivity from `l` to
    `O⊔C` is injective on atoms: `σ_a = σ_{a⁻¹}` (via `sigma_inv_eq_sigma_prime`,
    `σ' = σ_{a⁻¹}`) would force `σ_a` ≤ `(a⊔E_I) ⊓ (a⁻¹⊔E_I) = E_I` (modular
    intersection at shared atom `E_I`, with `a ≠ a⁻¹` guaranteeing
    non-collinearity). But `σ_a ≤ O⊔C` and `E_I ∉ O⊔C` (`hE_I_not_OC`),
    contradiction.

    This is the **`σ_a ≠ σ'`** distinctness condition for the X₂₃ side
    in `coord_first_desargues_mul`'s `desargues_planar` call. -/
private theorem sigma_a_ne_sigma' (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) (ha_ne_U : a ≠ Γ.U)
    (ha_ne_inv : a ≠ coord_inv Γ a) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠
    (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by
  intro h
  -- σ_{a⁻¹} = σ' via sigma_inv_eq_sigma_prime, so σ_a = σ' ⇒ σ_a = σ_{a⁻¹}
  have hσ_inv_eq := sigma_inv_eq_sigma_prime Γ ha ha_on ha_ne_U
  rw [← hσ_inv_eq] at h
  -- h : (O⊔C)⊓(a⊔E_I) = (O⊔C)⊓(coord_inv a ⊔ E_I)
  have hinv_atom : IsAtom (coord_inv Γ a) := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_on : coord_inv Γ a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have ha_ne_E_I : a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ ha_on)
  have hinv_ne_E_I : coord_inv Γ a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ hinv_on)
  -- σ_a ≤ a⊔E_I trivially; via h, σ_a ≤ inv_a⊔E_I
  have hσa_le_aEI : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ a ⊔ Γ.E_I := inf_le_right
  have hσa_le_invEI : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ coord_inv Γ a ⊔ Γ.E_I :=
    h.le.trans inf_le_right
  -- inv_a ∉ a⊔E_I: else inv_a ≤ (a⊔E_I)⊓l = a, so inv_a = a, contradicting ha_ne_inv
  have hinv_not_aEI : ¬ coord_inv Γ a ≤ a ⊔ Γ.E_I := by
    intro hle
    have hl_inf : (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.E_I) = a := by
      rw [show a ⊔ Γ.E_I = Γ.E_I ⊔ a from sup_comm _ _]
      exact inf_sup_of_atom_not_le Γ.hE_I_atom Γ.hE_I_not_l ha_on
    have hinv_le_a : coord_inv Γ a ≤ a := (le_inf hinv_on hle).trans hl_inf.le
    exact ha_ne_inv ((ha.le_iff.mp hinv_le_a).resolve_left hinv_atom.1).symm
  -- modular_intersection: shared E_I, atoms a, inv_a, with inv_a ∉ E_I⊔a
  have h_inter : (Γ.E_I ⊔ a) ⊓ (Γ.E_I ⊔ coord_inv Γ a) = Γ.E_I :=
    modular_intersection Γ.hE_I_atom ha hinv_atom
      ha_ne_E_I.symm hinv_ne_E_I.symm ha_ne_inv
      (by rw [sup_comm]; exact hinv_not_aEI)
  have hσa_le_E_I : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.E_I :=
    (le_inf
      (hσa_le_aEI.trans (sup_comm a Γ.E_I).le)
      (hσa_le_invEI.trans (sup_comm (coord_inv Γ a) Γ.E_I).le)).trans h_inter.le
  have hσa_eq_E_I : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) = Γ.E_I :=
    (Γ.hE_I_atom.le_iff.mp hσa_le_E_I).resolve_left hσa_atom.1
  exact Γ.hE_I_not_OC
    (hσa_eq_E_I ▸ (inf_le_left : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C))

/-- **Side distinctness `inv_a⊔σ_a ≠ d_inv⊔σ'`** for the X₂₃ side of the
    `coord_first_desargues_mul` Desargues call. If equal, `σ' ≤ d_inv⊔σ' =
    inv_a⊔σ_a`; combined with `σ' ≤ O⊔C` and `inv_a ∉ O⊔C` (from
    `inv_a_not_OC`), `inf_sup_of_atom_not_le` gives
    `(O⊔C)⊓(σ_a⊔inv_a) = σ_a`, hence `σ' ≤ σ_a`. Atoms force `σ' = σ_a`,
    contradicting `sigma_a_ne_sigma'`. -/
private theorem h_sides_X23_mul (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_U : a ≠ Γ.U) (ha_ne_inv : a ≠ coord_inv Γ a) :
    coord_inv Γ a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠
    (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
      (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by
  intro h
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have hinv_atom : IsAtom (coord_inv Γ a) := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_not_OC : ¬ coord_inv Γ a ≤ Γ.O ⊔ Γ.C := inv_a_not_OC Γ ha ha_on ha_ne_U
  have hσa_le_OC : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσ'_le_OC : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤ Γ.O ⊔ Γ.C :=
    inf_le_left
  -- σ' ≤ inv_a ⊔ σ_a (from h, swapping σ' to LHS via le_sup_right of RHS).
  have hσ'_le_RHS : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := le_sup_right
  have hσ'_le_LHS : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      coord_inv Γ a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    hσ'_le_RHS.trans h.symm.le
  -- (O⊔C) ⊓ (inv_a ⊔ σ_a) = σ_a (inf_sup_of_atom_not_le with R=inv_a, s=σ_a)
  have hOC_inf : (Γ.O ⊔ Γ.C) ⊓ (coord_inv Γ a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I)) =
      (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    inf_sup_of_atom_not_le hinv_atom hinv_not_OC hσa_le_OC
  -- σ' ≤ σ_a
  have hσ'_le_σa : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    (le_inf hσ'_le_OC hσ'_le_LHS).trans hOC_inf.le
  -- σ' = σ_a (atoms), contradicts sigma_a_ne_sigma'
  have hσ'_eq_σa := IsAtom.eq_of_le hσ'_atom hσa_atom hσ'_le_σa
  exact sigma_a_ne_sigma' Γ ha ha_on ha_ne_U ha_ne_inv hσ'_eq_σa.symm

/-- **Side distinctness `a⊔σ_a ≠ d_a⊔σ'`** for the X₁₃ side of the
    `coord_first_desargues_mul` Desargues call. Symmetric to `h_sides_X23_mul`,
    swapping `inv_a` for `a`: equality forces `σ' ≤ a⊔σ_a`, modular
    intersection at `O⊔C` (with `a ∉ O⊔C` from `ha_ne_O` + `l⊓(O⊔C)=O`)
    gives `σ' ≤ σ_a`, atoms force `σ'=σ_a`, contradicts
    `sigma_a_ne_sigma'`. -/
private theorem h_sides_X13_mul (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (ha_ne_inv : a ≠ coord_inv Γ a) :
    a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≠
    (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
      (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by
  intro h
  have hσa_atom := sigma_a_atom Γ ha ha_on
  have hσ'_atom := sigma'_atom Γ ha ha_on
  have ha_not_OC : ¬ a ≤ Γ.O ⊔ Γ.C := by
    intro hle
    have hl_inf_OC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
    exact ha_ne_O ((Γ.hO.le_iff.mp (hl_inf_OC ▸ le_inf ha_on hle)).resolve_left ha.1)
  have hσa_le_OC : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσ'_le_OC : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤ Γ.O ⊔ Γ.C :=
    inf_le_left
  -- σ' ≤ a ⊔ σ_a (from h, via le_sup_right of RHS).
  have hσ'_le_RHS : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
        (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := le_sup_right
  have hσ'_le_LHS : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    hσ'_le_RHS.trans h.symm.le
  -- (O⊔C) ⊓ (a ⊔ σ_a) = σ_a (inf_sup_of_atom_not_le with R=a, s=σ_a)
  have hOC_inf : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I)) =
      (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    inf_sup_of_atom_not_le ha ha_not_OC hσa_le_OC
  have hσ'_le_σa : (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ≤
      (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) :=
    (le_inf hσ'_le_OC hσ'_le_LHS).trans hOC_inf.le
  have hσ'_eq_σa := IsAtom.eq_of_le hσ'_atom hσa_atom hσ'_le_σa
  exact sigma_a_ne_sigma' Γ ha ha_on ha_ne_U ha_ne_inv hσ'_eq_σa.symm

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

**Architecture (session 125):** Split into two named sub-lemmas:

* `coord_first_desargues_mul` — the single Desargues call producing axis
  collinearity `X₂₃ ≤ U ⊔ X₁₃`. Realistic ~350–500 lines (parallel to
  FTPGAddComm.coord_first_desargues at ~600 lines, but ~7 distinctness
  helpers already factored out in this file).
* `axis_to_sigma_a_le` — the bridge: from `X₂₃ ≤ U ⊔ X₁₃`, derive the
  target `σ_a ≤ I ⊔ d_{a⁻¹}`. Likely a second Desargues call (parallel
  to FTPGAddComm.coord_second_desargues at ~800 lines), or a clever
  covering argument.

Both are sorry'd here; the headline `sigma_a_le_I_sup_d_inv_distinct`
trivially composes them.

**Distinctness audit (sessions 124–125, all PROVEN as private helpers):**
`d_a_ne_d_inv` (X₁₂), `ha_ne_I_of_distinct`, `sigma_a_ne_C` (Desargues
center collision), `sigma_a_ne_O`, `sigma_a_ne_U`, `sigma_a_ne_a`,
`sigma_a_ne_d_a`, `sigma_a_ne_sigma'` (X₂₃ side distinctness — uses
`modular_intersection` at `E_I` with `a ≠ inv_a`).

**Geometry notes for the X₂₃ side** (`inv_a⊔σ_a ≠ d_inv⊔σ'`): σ' is
defined via `a` (not `inv_a`), so `d_inv⊔σ'` does NOT have a clean
`I⊔d_inv` form. The clean argument: assume `inv_a⊔σ_a = d_inv⊔σ'`,
then `σ' ≤ inv_a⊔σ_a`; with `inv_a ∉ O⊔C` (since `coord_inv_ne_O`),
modular intersection gives `(inv_a⊔σ_a)⊓(O⊔C) = σ_a`, forcing
`σ' = σ_a`, contradicting `sigma_a_ne_sigma'`. The matching
`d_a⊔σ' = I⊔d_a` and `a⊔σ_a = a⊔E_I` upgrades (h_sides₁₃) ARE clean
via covering at `d_a` and `a` respectively.

**Watch-out for the proof:** `line_direction` produces
`(d_a ⊔ Γ.I) ⊓ ...`, NOT `(Γ.I ⊔ d_a) ⊓ ...`; pre-rewrite with
`sup_comm` (the precedent `coord_mul_right_inv` does this on line 416).
And `IsAtom.le_iff` is owned by the **target** atom (CLAUDE.md note);
two-atom inequalities flip direction freely. -/
private theorem coord_first_desargues_mul (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (ha_ne_inv : a ≠ coord_inv Γ a)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    (coord_inv Γ a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I)) ⊓
    ((coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
       (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V))) ≤
    Γ.U ⊔ (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) := by
  -- Variable bindings
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ_def
  set inv_a := coord_inv Γ a with hinv_def
  set σ_a := (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) with hσa_def
  set σ' := (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) with hσ'_def
  set d_a := (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) with hda_def
  set d_inv := (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) with hdinv_def
  -- Atomicity (from existing helpers)
  have hσa_atom : IsAtom σ_a := sigma_a_atom Γ ha ha_on
  have hσ'_atom : IsAtom σ' := sigma'_atom Γ ha ha_on
  have hd_atom : IsAtom d_a := d_a_atom Γ ha ha_on
  have hinv_atom : IsAtom inv_a := coord_inv_atom Γ ha ha_on ha_ne_U
  have hinv_on : inv_a ≤ Γ.O ⊔ Γ.U := coord_inv_on_l Γ a
  have hinv_ne_O : inv_a ≠ Γ.O := coord_inv_ne_O Γ ha ha_on ha_ne_U
  have hinv_ne_U : inv_a ≠ Γ.U := coord_inv_ne_U Γ ha ha_on ha_ne_O
  have hd_inv_atom : IsAtom d_inv := d_a_atom Γ hinv_atom hinv_on
  -- ha_ne_I from ha_ne_inv via coord_inv_I_eq_I
  have ha_ne_I : a ≠ Γ.I := ha_ne_I_of_distinct Γ ha ha_ne_inv
  -- Distinctness facts via existing helpers
  have hσa_ne_C : σ_a ≠ Γ.C := sigma_a_ne_C Γ ha ha_on ha_ne_I
  have hσa_ne_O : σ_a ≠ Γ.O := sigma_a_ne_O Γ ha ha_on ha_ne_O
  have hσa_ne_U : σ_a ≠ Γ.U := sigma_a_ne_U Γ ha ha_on
  have hσa_ne_E : σ_a ≠ Γ.E := sigma_a_ne_E Γ ha ha_on ha_ne_U
  have hσa_ne_a : σ_a ≠ a := sigma_a_ne_a Γ ha ha_on ha_ne_O
  have hσa_ne_d : σ_a ≠ d_a := sigma_a_ne_d_a Γ ha ha_on ha_ne_U
  have hσa_ne_inv : σ_a ≠ inv_a := sigma_a_ne_inv_a Γ ha ha_on ha_ne_O
  have hσa_ne_σ' : σ_a ≠ σ' := sigma_a_ne_sigma' Γ ha ha_on ha_ne_U ha_ne_inv
  have hσ'_ne_C : σ' ≠ Γ.C := sigma'_ne_C Γ ha ha_on ha_ne_I
  have hσ'_ne_O : σ' ≠ Γ.O := sigma'_ne_O Γ ha ha_on ha_ne_U
  have hσ'_ne_E : σ' ≠ Γ.E := sigma'_ne_E Γ ha ha_on ha_ne_O
  have hd_ne_d_inv : d_a ≠ d_inv := d_a_ne_d_inv Γ ha ha_on ha_ne_U ha_ne_inv
  -- Plane memberships
  have hC_le_π : Γ.C ≤ π := Γ.hC_plane
  have ha_le_π : a ≤ π := ha_on.trans le_sup_left
  have hinv_le_π : inv_a ≤ π := hinv_on.trans le_sup_left
  have hm_le_π : Γ.U ⊔ Γ.V ≤ π :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hd_le_π : d_a ≤ π := (inf_le_right : d_a ≤ Γ.U ⊔ Γ.V).trans hm_le_π
  have hd_inv_le_π : d_inv ≤ π := (inf_le_right : d_inv ≤ Γ.U ⊔ Γ.V).trans hm_le_π
  have hσa_le_OC : σ_a ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hσ'_le_OC : σ' ≤ Γ.O ⊔ Γ.C := inf_le_left
  have hOC_le_π : Γ.O ⊔ Γ.C ≤ π :=
    sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane
  have hσa_le_π : σ_a ≤ π := hσa_le_OC.trans hOC_le_π
  have hσ'_le_π : σ' ≤ π := hσ'_le_OC.trans hOC_le_π
  -- Center C distinct from each vertex
  have hC_ne_a : Γ.C ≠ a := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hC_ne_inv : Γ.C ≠ inv_a := fun h => Γ.hC_not_l (h ▸ hinv_on)
  have hC_ne_σa : Γ.C ≠ σ_a := fun h => hσa_ne_C h.symm
  have hC_ne_d : Γ.C ≠ d_a := fun h =>
    Γ.hC_not_m (h ▸ (inf_le_right : d_a ≤ Γ.U ⊔ Γ.V))
  have hC_ne_d_inv : Γ.C ≠ d_inv := fun h =>
    Γ.hC_not_m (h ▸ (inf_le_right : d_inv ≤ Γ.U ⊔ Γ.V))
  have hC_ne_σ' : Γ.C ≠ σ' := fun h => hσ'_ne_C h.symm
  -- Corresponding vertices distinct (a ≠ d_a, inv_a ≠ d_inv; σ_a ≠ σ' have)
  have ha_ne_d : a ≠ d_a := by
    intro h
    exact d_a_not_l Γ ha ha_on ha_ne_U (h ▸ ha_on : d_a ≤ Γ.O ⊔ Γ.U)
  have hinv_ne_d_inv : inv_a ≠ d_inv := by
    intro h
    exact d_a_not_l Γ hinv_atom hinv_on hinv_ne_U
      (h ▸ hinv_on : d_inv ≤ Γ.O ⊔ Γ.U)
  -- σ' ≠ d_a, σ' ≠ d_inv (both: σ' on O⊔C; d on m; common atom = E; would force σ' = E)
  have hσ'_ne_d : σ' ≠ d_a := by
    intro h
    have hσ'_le_m : σ' ≤ Γ.U ⊔ Γ.V := h ▸ inf_le_right
    have hσ'_le_E : σ' ≤ Γ.E := by
      show σ' ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V); exact le_inf hσ'_le_OC hσ'_le_m
    exact hσ'_ne_E ((Γ.hE_atom.le_iff.mp hσ'_le_E).resolve_left hσ'_atom.1)
  have hσ'_ne_d_inv : σ' ≠ d_inv := by
    intro h
    have hσ'_le_m : σ' ≤ Γ.U ⊔ Γ.V := h ▸ inf_le_right
    have hσ'_le_E : σ' ≤ Γ.E := by
      show σ' ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V); exact le_inf hσ'_le_OC hσ'_le_m
    exact hσ'_ne_E ((Γ.hE_atom.le_iff.mp hσ'_le_E).resolve_left hσ'_atom.1)
  -- Perspectivity from center C: b_i ≤ C ⊔ a_i
  have hd_perspect : d_a ≤ Γ.C ⊔ a := by
    rw [show Γ.C ⊔ a = a ⊔ Γ.C from sup_comm _ _]; exact inf_le_left
  have hd_inv_perspect : d_inv ≤ Γ.C ⊔ inv_a := by
    rw [show Γ.C ⊔ inv_a = inv_a ⊔ Γ.C from sup_comm _ _]; exact inf_le_left
  have hσ'_perspect : σ' ≤ Γ.C ⊔ σ_a := by
    -- σ_a, C distinct atoms on O⊔C ⇒ C⊔σ_a = O⊔C; σ' ≤ O⊔C ⇒ σ' ≤ C⊔σ_a
    have hC_lt_Cσa : Γ.C < Γ.C ⊔ σ_a := lt_of_le_of_ne le_sup_left
      (fun h => hσa_ne_C ((Γ.hC.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left hσa_atom.1))
    have hCσa_le_OC : Γ.C ⊔ σ_a ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right hσa_le_OC
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have hC_cov_OC : Γ.C ⋖ Γ.O ⊔ Γ.C := by
      have := atom_covBy_join Γ.hC Γ.hO hOC.symm
      rwa [sup_comm] at this
    have hCσa_eq_OC : Γ.C ⊔ σ_a = Γ.O ⊔ Γ.C :=
      (hC_cov_OC.eq_or_eq hC_lt_Cσa.le hCσa_le_OC).resolve_left (ne_of_gt hC_lt_Cσa)
    exact hCσa_eq_OC ▸ hσ'_le_OC
  -- Line upgrades: a⊔inv_a = l (both atoms on l, distinct) and d_a⊔d_inv = m
  have ha_inv_eq_l : a ⊔ inv_a = Γ.O ⊔ Γ.U := by
    have h_le : a ⊔ inv_a ≤ Γ.O ⊔ Γ.U := sup_le ha_on hinv_on
    have h_lt : a < a ⊔ inv_a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_inv ((ha.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left hinv_atom.1).symm)
    have hcov : a ⋖ Γ.O ⊔ Γ.U := line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on
    exact (hcov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hd_d_inv_eq_m : d_a ⊔ d_inv = Γ.U ⊔ Γ.V := by
    have h_le : d_a ⊔ d_inv ≤ Γ.U ⊔ Γ.V := sup_le inf_le_right inf_le_right
    have h_lt : d_a < d_a ⊔ d_inv := lt_of_le_of_ne le_sup_left
      (fun h => hd_ne_d_inv ((hd_atom.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left hd_inv_atom.1).symm)
    have hcov : d_a ⋖ Γ.U ⊔ Γ.V :=
      line_covers_its_atoms Γ.hU Γ.hV hUV hd_atom inf_le_right
    exact (hcov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  -- Side distinctness X₁₂: a⊔inv_a ≠ d_a⊔d_inv (= l ≠ m)
  have hs12 : a ⊔ inv_a ≠ d_a ⊔ d_inv := by
    rw [ha_inv_eq_l, hd_d_inv_eq_m]
    intro h
    exact Γ.hO_not_m (h ▸ (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U))
  -- σ_a ∉ l, σ' ∉ m (used for triangle plane equalities + side coverings)
  have hσa_not_l : ¬ σ_a ≤ Γ.O ⊔ Γ.U := by
    intro h
    have hl_inf_OC : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O := by
      rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
      exact inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ Γ.O ⊔ Γ.U)
    have hσa_le_O : σ_a ≤ Γ.O := hl_inf_OC ▸ le_inf h hσa_le_OC
    exact hσa_ne_O ((Γ.hO.le_iff.mp hσa_le_O).resolve_left hσa_atom.1)
  have hσ'_not_m : ¬ σ' ≤ Γ.U ⊔ Γ.V := by
    intro h
    have hσ'_le_E : σ' ≤ Γ.E := by
      show σ' ≤ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V); exact le_inf hσ'_le_OC h
    exact hσ'_ne_E ((Γ.hE_atom.le_iff.mp hσ'_le_E).resolve_left hσ'_atom.1)
  -- Triangle plane equalities: l⊔σ_a = π and m⊔σ' = π
  have hπA : a ⊔ inv_a ⊔ σ_a = π := by
    rw [ha_inv_eq_l]
    have h_lt : (Γ.O ⊔ Γ.U) < Γ.O ⊔ Γ.U ⊔ σ_a := lt_of_le_of_ne le_sup_left
      (fun heq => hσa_not_l (le_sup_right.trans heq.symm.le))
    have h_le : Γ.O ⊔ Γ.U ⊔ σ_a ≤ π := sup_le le_sup_left hσa_le_π
    exact ((l_covBy_π_inv Γ).eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  have hπB : d_a ⊔ d_inv ⊔ σ' = π := by
    rw [hd_d_inv_eq_m]
    have h_lt : Γ.U ⊔ Γ.V < Γ.U ⊔ Γ.V ⊔ σ' := lt_of_le_of_ne le_sup_left
      (fun heq => hσ'_not_m (le_sup_right.trans heq.symm.le))
    have h_le : Γ.U ⊔ Γ.V ⊔ σ' ≤ π := sup_le hm_le_π hσ'_le_π
    exact (Γ.m_covBy_π.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  -- Side coverings for the three T₁ sides.
  have hcov12 : a ⊔ inv_a ⋖ π := ha_inv_eq_l ▸ l_covBy_π_inv Γ
  -- For h_cov_13 and h_cov_23 we use line_covBy_plane.
  -- a < l (since a ≠ O, atom in l would force a = O):
  have h_a_lt_l : a < Γ.O ⊔ Γ.U := lt_of_le_of_ne ha_on
    (fun heq => ha_ne_O ((ha.le_iff.mp
      (le_sup_left.trans heq.symm.le)).resolve_left Γ.hO.1).symm)
  have h_inv_lt_l : inv_a < Γ.O ⊔ Γ.U := lt_of_le_of_ne hinv_on
    (fun heq => hinv_ne_O ((hinv_atom.le_iff.mp
      (le_sup_left.trans heq.symm.le)).resolve_left Γ.hO.1).symm)
  -- ¬ inv_a ≤ a⊔σ_a: if so, l = a⊔σ_a (covering at a), forcing σ_a ≤ l
  have h_not_collinear_13 : ¬ inv_a ≤ a ⊔ σ_a := by
    intro h
    have hl_le : Γ.O ⊔ Γ.U ≤ a ⊔ σ_a := ha_inv_eq_l ▸ sup_le le_sup_left h
    have h_cov_aσa : a ⋖ a ⊔ σ_a := atom_covBy_join ha hσa_atom (Ne.symm hσa_ne_a)
    have hl_eq_aσa : Γ.O ⊔ Γ.U = a ⊔ σ_a :=
      (h_cov_aσa.eq_or_eq h_a_lt_l.le hl_le).resolve_left (ne_of_gt h_a_lt_l)
    exact hσa_not_l (hl_eq_aσa.symm ▸ (le_sup_right : σ_a ≤ a ⊔ σ_a))
  have h_not_collinear_23 : ¬ a ≤ inv_a ⊔ σ_a := by
    intro h
    have hl_le : Γ.O ⊔ Γ.U ≤ inv_a ⊔ σ_a := ha_inv_eq_l ▸ sup_le h le_sup_left
    have h_cov_invσa : inv_a ⋖ inv_a ⊔ σ_a :=
      atom_covBy_join hinv_atom hσa_atom hσa_ne_inv.symm
    have hl_eq_invσa : Γ.O ⊔ Γ.U = inv_a ⊔ σ_a :=
      (h_cov_invσa.eq_or_eq h_inv_lt_l.le hl_le).resolve_left (ne_of_gt h_inv_lt_l)
    exact hσa_not_l (hl_eq_invσa.symm ▸ (le_sup_right : σ_a ≤ inv_a ⊔ σ_a))
  have hcov13 : a ⊔ σ_a ⋖ π := by
    have hπ_eq : a ⊔ σ_a ⊔ inv_a = π := by
      rw [sup_assoc, sup_comm σ_a inv_a, ← sup_assoc]; exact hπA
    exact hπ_eq ▸ line_covBy_plane ha hσa_atom hinv_atom
      (Ne.symm hσa_ne_a) ha_ne_inv hσa_ne_inv h_not_collinear_13
  have hcov23 : inv_a ⊔ σ_a ⋖ π := by
    have hπ_eq : inv_a ⊔ σ_a ⊔ a = π := by
      rw [show inv_a ⊔ σ_a ⊔ a = a ⊔ inv_a ⊔ σ_a from by
        rw [sup_assoc, sup_comm (σ_a) a, ← sup_assoc, sup_comm inv_a a]]
      exact hπA
    exact hπ_eq ▸ line_covBy_plane hinv_atom hσa_atom ha
      hσa_ne_inv.symm ha_ne_inv.symm hσa_ne_a h_not_collinear_23
  -- Side distinctness for X₁₃ and X₂₃ via dedicated helpers
  have hs13 : a ⊔ σ_a ≠ d_a ⊔ σ' :=
    h_sides_X13_mul Γ ha ha_on ha_ne_O ha_ne_U ha_ne_inv
  have hs23 : inv_a ⊔ σ_a ≠ d_inv ⊔ σ' :=
    h_sides_X23_mul Γ ha ha_on ha_ne_U ha_ne_inv
  -- Apply desargues_planar with center C, T₁ = (a, inv_a, σ_a), T₂ = (d_a, d_inv, σ').
  obtain ⟨axis, h_axis_le, h_axis_ne, h₁₂, h₁₃, h₂₃⟩ := desargues_planar
    Γ.hC ha hinv_atom hσa_atom hd_atom hd_inv_atom hσ'_atom
    hC_le_π ha_le_π hinv_le_π hσa_le_π hd_le_π hd_inv_le_π hσ'_le_π
    hd_perspect hd_inv_perspect hσ'_perspect
    ha_ne_inv (Ne.symm hσa_ne_a) (Ne.symm hσa_ne_inv)
    hd_ne_d_inv (Ne.symm hσ'_ne_d) (Ne.symm hσ'_ne_d_inv)
    hs12 hs13 hs23
    hπA hπB
    hC_ne_a hC_ne_inv hC_ne_σa hC_ne_d hC_ne_d_inv hC_ne_σ'
    ha_ne_d hinv_ne_d_inv hσa_ne_σ'
    R hR hR_not h_irred
    hcov12 hcov13 hcov23
  -- Upgrade X₁₂ = (a⊔inv_a) ⊓ (d_a⊔d_inv) = U via l ⊓ m
  have hX12_eq_U : (a ⊔ inv_a) ⊓ (d_a ⊔ d_inv) = Γ.U := by
    rw [ha_inv_eq_l, hd_d_inv_eq_m]; exact Γ.l_inf_m_eq_U
  have hU_le_axis : Γ.U ≤ axis := hX12_eq_U ▸ h₁₂
  -- Upgrade X₁₃: (a⊔σ_a) = (a⊔E_I) and (d_a⊔σ') = (I⊔d_a) via covering
  have ha_ne_E_I : a ≠ Γ.E_I := fun he => Γ.hE_I_not_l (he ▸ ha_on)
  have hI_ne_d := I_ne_d_a Γ ha ha_on
  have h_aσa_eq_aEI : a ⊔ σ_a = a ⊔ Γ.E_I := by
    have hσa_le_aEI : σ_a ≤ a ⊔ Γ.E_I := inf_le_right
    have h_lt : a < a ⊔ σ_a := lt_of_le_of_ne le_sup_left
      (fun h => hσa_ne_a ((ha.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left hσa_atom.1))
    have h_le : a ⊔ σ_a ≤ a ⊔ Γ.E_I := sup_le le_sup_left hσa_le_aEI
    have h_cov : a ⋖ a ⊔ Γ.E_I := atom_covBy_join ha Γ.hE_I_atom ha_ne_E_I
    exact (h_cov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  have h_dσ'_eq_Id : d_a ⊔ σ' = Γ.I ⊔ d_a := by
    have hσ'_le_Id : σ' ≤ Γ.I ⊔ d_a := inf_le_right
    have h_lt : d_a < d_a ⊔ σ' := lt_of_le_of_ne le_sup_left
      (fun h => hσ'_ne_d ((hd_atom.le_iff.mp
        (le_sup_right.trans h.symm.le)).resolve_left hσ'_atom.1))
    have h_le : d_a ⊔ σ' ≤ Γ.I ⊔ d_a := sup_le le_sup_right hσ'_le_Id
    have h_cov : d_a ⋖ Γ.I ⊔ d_a := by
      have := atom_covBy_join hd_atom Γ.hI hI_ne_d.symm
      rwa [sup_comm] at this
    exact (h_cov.eq_or_eq h_lt.le h_le).resolve_left (ne_of_gt h_lt)
  have hX13_eq : (a ⊔ σ_a) ⊓ (d_a ⊔ σ') = (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ d_a) := by
    rw [h_aσa_eq_aEI, h_dσ'_eq_Id]
  have hX13_le_axis : (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ d_a) ≤ axis := hX13_eq ▸ h₁₃
  -- Closing: U ⊔ X₁₃ ⋖ π via line_covBy_plane (c = O).
  -- Plan: (a) X₁₃ is an atom (meet of two distinct lines a⊔E_I and I⊔d_a in π);
  --       (b) core fact: X₁₃ ≤ l → False (would force a = I via line_direction);
  --       (c) span: U⊔X₁₃⊔O = π via l⊔X₁₃ = π;
  --       (d) ¬ O ≤ U⊔X₁₃ via line_eq_of_atom_le → X₁₃ ≤ l, then (b).
  set X₁₃ := (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ d_a) with hX13_def
  have hl_cov_π : Γ.O ⊔ Γ.U ⋖ π := l_covBy_π_inv Γ
  have ha_ne_E_I : a ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ ha_on)
  have hI_ne_d := I_ne_d_a Γ ha ha_on
  -- Direction projections via line_direction.
  have h_aEI_inf_l : (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = a := by
    rw [show a ⊔ Γ.E_I = Γ.E_I ⊔ a from sup_comm _ _]
    exact line_direction Γ.hE_I_atom Γ.hE_I_not_l ha_on
  have h_Id_inf_l : (Γ.I ⊔ d_a) ⊓ (Γ.O ⊔ Γ.U) = Γ.I := by
    rw [show Γ.I ⊔ d_a = d_a ⊔ Γ.I from sup_comm _ _]
    exact line_direction hd_atom (d_a_not_l Γ ha ha_on ha_ne_U) Γ.hI_on
  -- π memberships of the two lines.
  have haEI_le_π : a ⊔ Γ.E_I ≤ π :=
    sup_le ha_le_π (Γ.hE_I_on_m.trans hm_le_π)
  have hId_le_π : Γ.I ⊔ d_a ≤ π :=
    sup_le (Γ.hI_on.trans le_sup_left) hd_le_π
  -- (Step 1) a ⊔ E_I ⋖ π via line_covBy_plane(a, E_I, O), span O⊔a=l, l⊔E_I=π.
  have hO_not_aEI : ¬ Γ.O ≤ a ⊔ Γ.E_I := by
    intro hO_le
    have hO_le_inf : Γ.O ≤ (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) := le_inf hO_le le_sup_left
    rw [h_aEI_inf_l] at hO_le_inf
    exact ha_ne_O ((ha.le_iff.mp hO_le_inf).resolve_left Γ.hO.1).symm
  have hE_I_ne_O : Γ.E_I ≠ Γ.O := fun h => Γ.hE_I_not_l (h ▸ le_sup_left)
  have hOa_eq_l : Γ.O ⊔ a = Γ.O ⊔ Γ.U :=
    (line_eq_of_atom_le Γ.hO Γ.hU ha Γ.hOU ha_ne_O.symm
      ha_ne_U.symm ha_on).symm
  have h_lEI_lt : Γ.O ⊔ Γ.U < Γ.O ⊔ Γ.U ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
    (fun heq => Γ.hE_I_not_l (le_sup_right.trans heq.symm.le))
  have h_lEI_le_π : Γ.O ⊔ Γ.U ⊔ Γ.E_I ≤ π :=
    sup_le le_sup_left (Γ.hE_I_on_m.trans hm_le_π)
  have h_lEI_eq_π : Γ.O ⊔ Γ.U ⊔ Γ.E_I = π :=
    (hl_cov_π.eq_or_eq h_lEI_lt.le h_lEI_le_π).resolve_left (ne_of_gt h_lEI_lt)
  have h_aEIO_eq_π : a ⊔ Γ.E_I ⊔ Γ.O = π := by
    have h1 : a ⊔ Γ.E_I ⊔ Γ.O = Γ.O ⊔ a ⊔ Γ.E_I := by
      rw [sup_comm (a ⊔ Γ.E_I) Γ.O, sup_assoc]
    rw [h1, hOa_eq_l, h_lEI_eq_π]
  have h_aEI_cov_π : a ⊔ Γ.E_I ⋖ π := by
    rw [← h_aEIO_eq_π]
    exact line_covBy_plane ha Γ.hE_I_atom Γ.hO ha_ne_E_I ha_ne_O
      hE_I_ne_O hO_not_aEI
  -- (Step 2) ¬ a⊔E_I ≤ I⊔d_a (else intersect with l forces a = I).
  have h_not_aEI_le_Id : ¬ a ⊔ Γ.E_I ≤ Γ.I ⊔ d_a := by
    intro hle
    have ha_le_Id : a ≤ Γ.I ⊔ d_a := le_sup_left.trans hle
    have ha_le_inf : a ≤ (Γ.I ⊔ d_a) ⊓ (Γ.O ⊔ Γ.U) := le_inf ha_le_Id ha_on
    rw [h_Id_inf_l] at ha_le_inf
    exact ha_ne_I ((Γ.hI.le_iff.mp ha_le_inf).resolve_left ha.1)
  -- (Step 3) The meet (a⊔E_I) ⊓ (I⊔d_a) is non-trivial via lines_meet_if_coplanar.
  have hI_lt_Id : Γ.I < Γ.I ⊔ d_a := lt_of_le_of_ne le_sup_left
    (fun heq => hI_ne_d.symm ((Γ.hI.le_iff.mp
      (le_sup_right.trans heq.symm.le)).resolve_left hd_atom.1))
  have h_not_Id_le_aEI : ¬ Γ.I ⊔ d_a ≤ a ⊔ Γ.E_I := by
    intro hle
    have hI_le_aEI : Γ.I ≤ a ⊔ Γ.E_I := le_sup_left.trans hle
    have hI_le_inf : Γ.I ≤ (a ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) := le_inf hI_le_aEI Γ.hI_on
    rw [h_aEI_inf_l] at hI_le_inf
    exact ha_ne_I.symm ((ha.le_iff.mp hI_le_inf).resolve_left Γ.hI.1)
  have h_meet_ne : (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ d_a) ≠ ⊥ :=
    lines_meet_if_coplanar h_aEI_cov_π hId_le_π h_not_Id_le_aEI Γ.hI hI_lt_Id
  -- (Step 4) X₁₃ is an atom via meet_of_lines_is_atom.
  have hX13_atom : IsAtom X₁₃ :=
    meet_of_lines_is_atom ha Γ.hE_I_atom Γ.hI hd_atom ha_ne_E_I hI_ne_d
      h_not_aEI_le_Id h_meet_ne
  -- X₁₃ ≤ π.
  have hX13_le_π : X₁₃ ≤ π := inf_le_left.trans haEI_le_π
  -- (Step 5) Core: X₁₃ ≤ l → False.
  have h_core : ¬ X₁₃ ≤ Γ.O ⊔ Γ.U := by
    intro hX_l
    have hX_le_aEI : X₁₃ ≤ a ⊔ Γ.E_I := inf_le_left
    have hX_le_Id : X₁₃ ≤ Γ.I ⊔ d_a := inf_le_right
    have hX_le_a : X₁₃ ≤ a := by
      have := le_inf hX_le_aEI hX_l
      rwa [h_aEI_inf_l] at this
    have hX_le_I : X₁₃ ≤ Γ.I := by
      have := le_inf hX_le_Id hX_l
      rwa [h_Id_inf_l] at this
    have hX_eq_a : X₁₃ = a :=
      (ha.le_iff.mp hX_le_a).resolve_left hX13_atom.1
    have hX_eq_I : X₁₃ = Γ.I :=
      (Γ.hI.le_iff.mp hX_le_I).resolve_left hX13_atom.1
    exact ha_ne_I (hX_eq_a.symm.trans hX_eq_I)
  -- (Step 6) Distinctness for line_covBy_plane(U, X₁₃, O).
  have hU_ne_X : Γ.U ≠ X₁₃ := fun h => h_core (h ▸ le_sup_right)
  have hX_ne_O : X₁₃ ≠ Γ.O := fun h => h_core (h ▸ le_sup_left)
  have hO_not_UX : ¬ Γ.O ≤ Γ.U ⊔ X₁₃ := by
    intro hO_le
    -- U⊔X₁₃ is a line (atom join). With O ≤ U⊔X₁₃ and O ≠ U, line_eq_of_atom_le
    -- gives U⊔X₁₃ = U⊔O = O⊔U = l. So X₁₃ ≤ l, contradicting h_core.
    have hUX_eq : Γ.U ⊔ X₁₃ = Γ.U ⊔ Γ.O :=
      line_eq_of_atom_le Γ.hU hX13_atom Γ.hO hU_ne_X Γ.hOU.symm hX_ne_O hO_le
    have hUX_eq_l : Γ.U ⊔ X₁₃ = Γ.O ⊔ Γ.U := hUX_eq.trans (sup_comm _ _)
    exact h_core (le_sup_right.trans hUX_eq_l.le)
  -- (Step 7) Span: U⊔X₁₃⊔O = π via l⊔X₁₃ = π.
  have hUX_le_π : Γ.U ⊔ X₁₃ ≤ π :=
    sup_le (le_sup_right.trans le_sup_left) hX13_le_π
  have hl_lt_lX : Γ.O ⊔ Γ.U < Γ.O ⊔ Γ.U ⊔ X₁₃ := lt_of_le_of_ne le_sup_left
    (fun heq => h_core (le_sup_right.trans heq.symm.le))
  have hlX_le_π : Γ.O ⊔ Γ.U ⊔ X₁₃ ≤ π := sup_le le_sup_left hX13_le_π
  have hlX_eq_π : Γ.O ⊔ Γ.U ⊔ X₁₃ = π :=
    (hl_cov_π.eq_or_eq hl_lt_lX.le hlX_le_π).resolve_left (ne_of_gt hl_lt_lX)
  have h_UXO_eq_π : Γ.U ⊔ X₁₃ ⊔ Γ.O = π := by
    have h1 : Γ.U ⊔ X₁₃ ⊔ Γ.O = Γ.O ⊔ Γ.U ⊔ X₁₃ := by
      rw [sup_comm (Γ.U ⊔ X₁₃) Γ.O, sup_assoc]
    rw [h1, hlX_eq_π]
  -- (Step 8) Apply line_covBy_plane and rewrite.
  have hcov_UX13 : Γ.U ⊔ X₁₃ ⋖ π := by
    rw [← h_UXO_eq_π]
    exact line_covBy_plane Γ.hU hX13_atom Γ.hO hU_ne_X Γ.hOU.symm hX_ne_O hO_not_UX
  exact collinear_of_common_bound hcov_UX13 h_axis_le h_axis_ne
    hU_le_axis hX13_le_axis h₂₃

/-- **Bridge from first-Desargues axis content to `σ_a ≤ I⊔d_{a⁻¹}`.**

Given `X₂₃ ≤ U ⊔ X₁₃` (with `X₁₃ = (a⊔E_I)⊓(I⊔d_a)`), conclude the
target `σ_a ≤ I⊔d_{a⁻¹}`. The natural route is a second `desargues_planar`
call paralleling `FTPGAddComm.coord_second_desargues`, with new center
some atom (likely `X₁₃` itself) and new triangles designed so the new
axis lands on `I⊔d_{a⁻¹}` (mirror of the additive case where the new
axis was `l = O⊔U`).

Open content. ~500–800 lines anticipated. -/
private theorem axis_to_sigma_a_le (Γ : CoordSystem L)
    {a : L} (_ha : IsAtom a) (_ha_on : a ≤ Γ.O ⊔ Γ.U)
    (_ha_ne_O : a ≠ Γ.O) (_ha_ne_U : a ≠ Γ.U)
    (_ha_ne_inv : a ≠ coord_inv Γ a)
    (_R : L) (_hR : IsAtom _R) (_hR_not : ¬ _R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (_h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q)
    (_h_axis : (coord_inv Γ a ⊔ (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I)) ⊓
      ((coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔
         (Γ.O ⊔ Γ.C) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V))) ≤
      Γ.U ⊔ (a ⊔ Γ.E_I) ⊓ (Γ.I ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V))) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤
      Γ.I ⊔ (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) := by
  sorry

/-- **Generic-case content for `coord_mul_left_inv`.** Composes the two named
    sub-lemmas: first Desargues (axis collinearity) followed by the bridge
    to `σ_a ≤ I⊔d_{a⁻¹}`. Both sub-lemmas are open; this composition is
    one line. -/
private theorem sigma_a_le_I_sup_d_inv_distinct (Γ : CoordSystem L)
    {a : L} (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (ha_ne_inv : a ≠ coord_inv Γ a)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.E_I) ≤
      Γ.I ⊔ (coord_inv Γ a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) :=
  axis_to_sigma_a_le Γ ha ha_on ha_ne_O ha_ne_U ha_ne_inv R hR hR_not h_irred
    (coord_first_desargues_mul Γ ha ha_on ha_ne_O ha_ne_U ha_ne_inv R hR hR_not h_irred)

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
