import Bridges.FTPG.Space
import Bridges.FTPG.Flat

/-!
# The sheared charts — camp three of the `pointSystem_exists` ascent, fourth pitch

The space chart (`Space.lean`) reads a space-affine atom through two drops:
`baseproj` through the off-plane witness `R` onto the coordinatized plane, and
`zproj` along the horizontal directions onto the z-axis.  This pitch reads the
*other* projections a space point admits — the drops through the two transport
centers `c` (on `U ⊔ R`) and `e` (on `V ⊔ R`) — and finds each one algebraic:

* `shproj w t = (t ⊔ w) ⊓ π` — the drop through an infinity center `w` onto
  the frame plane.
* the **x-shear** (`CoordFrame.xproj_shproj_c`): the drop through `c`
  preserves the ordinate and adds the z-gauge to the abscissa —
  `xproj (shproj c t) = xproj (baseproj t) + zcoord c (zproj t)`.
* the **y-shear** (`CoordFrame.ycoord_shproj_e`): the drop through `e`
  preserves the abscissa and adds the `e`-gauge `ncoord` to the ordinate.
* the **gauge bridge** (`CoordFrame.gauge_bridge`): the two gauges reconcile
  through one constant — the slope of `d̂ = (e ⊔ c) ⊓ m`, the trace of the
  line joining the two centers.

No fresh Desargues, no new incidence: every position fact is a modular move,
and the algebra rides the standing line laws (`le_line_iff`,
`le_origin_line_iff`, the pencil iffs) at the sheared image.  Model-verified
before carving (`probe_solid.py`): every statement over all 40,320 legal
frames of `PG(3,2)` exhaustively, sampled frames at `q = 3, 5`.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

variable {Γ : CoordSystem L} {R : L}

/-! ## Position facts for the second center line `V ⊔ R` -/

theorem CoordSystem.UR_inf_π (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.U ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = Γ.U := by
  rw [sup_inf_assoc_of_le R (le_sup_right.trans le_sup_left : Γ.U ≤ _),
    CoordSystem.R_inf_π hR hR_π, sup_bot_eq]

theorem CoordSystem.VR_inf_π (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.V ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = Γ.V := by
  rw [sup_inf_assoc_of_le R (le_sup_right : Γ.V ≤ _),
    CoordSystem.R_inf_π hR hR_π, sup_bot_eq]

theorem CoordSystem.hc_not_π (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {c : L} (hc : IsAtom c) (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) :
    ¬ c ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := fun h =>
  hc_U (IsAtom.eq_of_le hc Γ.hU
    (le_of_le_of_eq (le_inf hc_UR h) (CoordSystem.UR_inf_π hR hR_π)))

theorem CoordSystem.he_not_π (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {e : L} (he : IsAtom e) (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V) :
    ¬ e ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := fun h =>
  he_V (IsAtom.eq_of_le he Γ.hV
    (le_of_le_of_eq (le_inf he_VR h) (CoordSystem.VR_inf_π hR hR_π)))

theorem CoordSystem.UR_le_σ (Γ : CoordSystem L) (R : L) :
    Γ.U ⊔ R ≤ Γ.U ⊔ Γ.V ⊔ R :=
  sup_le (le_sup_left.trans le_sup_left) le_sup_right

theorem CoordSystem.VR_le_σ (Γ : CoordSystem L) (R : L) :
    Γ.V ⊔ R ≤ Γ.U ⊔ Γ.V ⊔ R :=
  sup_le (le_sup_right.trans le_sup_left) le_sup_right

theorem CoordSystem.n_inf_VR (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.O ⊔ Γ.V) ⊓ (Γ.V ⊔ R) = Γ.V := by
  rw [sup_comm Γ.O Γ.V]
  exact modular_intersection Γ.hV Γ.hO hR Γ.hOV.symm
    (CoordSystem.ne_R_of_le_π hR_π le_sup_right)
    (CoordSystem.ne_R_of_le_π hR_π (le_sup_left.trans le_sup_left))
    (fun h => hR_π (h.trans (sup_le le_sup_right (le_sup_left.trans le_sup_left))))

theorem CoordSystem.hV_not_ζ (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    ¬ Γ.V ≤ Γ.O ⊔ R := fun h =>
  Γ.hOV ((IsAtom.eq_of_le Γ.hV Γ.hO (le_of_le_of_eq
    (le_inf h (le_sup_right : Γ.V ≤ Γ.O ⊔ Γ.U ⊔ Γ.V))
    (CoordSystem.ζ_inf_π hR hR_π))).symm)

theorem CoordSystem.ζ_inf_VR (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.O ⊔ R) ⊓ (Γ.V ⊔ R) = R := by
  rw [sup_comm Γ.O R, sup_comm Γ.V R]
  exact modular_intersection hR Γ.hO Γ.hV
    (CoordSystem.ne_R_of_le_π hR_π (le_sup_left.trans le_sup_left)).symm
    (CoordSystem.ne_R_of_le_π hR_π le_sup_right).symm Γ.hOV
    (fun h => CoordSystem.hV_not_ζ hR hR_π (h.trans (sup_comm R Γ.O).le))

theorem CoordSystem.hV_not_UR (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    ¬ Γ.V ≤ Γ.U ⊔ R := fun h =>
  Γ.hUV ((IsAtom.eq_of_le Γ.hV Γ.hU (le_of_le_of_eq
    (le_inf h (le_sup_right : Γ.V ≤ Γ.O ⊔ Γ.U ⊔ Γ.V))
    (CoordSystem.UR_inf_π hR hR_π))).symm)

theorem CoordSystem.UR_inf_VR (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.U ⊔ R) ⊓ (Γ.V ⊔ R) = R := by
  rw [sup_comm Γ.U R, sup_comm Γ.V R]
  exact modular_intersection hR Γ.hU Γ.hV
    (CoordSystem.hU_ne_R hR_π).symm
    (CoordSystem.ne_R_of_le_π hR_π le_sup_right).symm Γ.hUV
    (fun h => CoordSystem.hV_not_UR hR hR_π (h.trans (sup_comm R Γ.U).le))

theorem CoordSystem.m_inf_VR (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.U ⊔ Γ.V) ⊓ (Γ.V ⊔ R) = Γ.V := by
  rw [sup_comm Γ.U Γ.V]
  exact modular_intersection Γ.hV Γ.hU hR Γ.hUV.symm
    (CoordSystem.ne_R_of_le_π hR_π le_sup_right)
    (CoordSystem.hU_ne_R hR_π)
    (fun h => CoordSystem.hR_not_m hR_π (le_of_le_of_eq h (sup_comm Γ.V Γ.U)))

theorem CoordSystem.e_not_m (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {e : L} (he : IsAtom e) (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V) :
    ¬ e ≤ Γ.U ⊔ Γ.V := fun h =>
  he_V (IsAtom.eq_of_le he Γ.hV
    (le_of_le_of_eq (le_inf h he_VR) (CoordSystem.m_inf_VR hR hR_π)))

theorem CoordSystem.e_not_n (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {e : L} (he : IsAtom e) (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V) :
    ¬ e ≤ Γ.O ⊔ Γ.V := fun h =>
  he_V (IsAtom.eq_of_le he Γ.hV
    (le_of_le_of_eq (le_inf h he_VR) (CoordSystem.n_inf_VR hR hR_π)))

theorem CoordSystem.e_not_ζ (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {e : L} (he : IsAtom e) (he_VR : e ≤ Γ.V ⊔ R) (he_R : e ≠ R) :
    ¬ e ≤ Γ.O ⊔ R := fun h =>
  he_R (IsAtom.eq_of_le he hR
    (le_of_le_of_eq (le_inf h he_VR) (CoordSystem.ζ_inf_VR hR hR_π)))

theorem CoordSystem.VR_eq_Ve (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {e : L} (he : IsAtom e) (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V) (he_R : e ≠ R) :
    Γ.V ⊔ R = Γ.V ⊔ e :=
  line_eq_of_atom_le Γ.hV hR he (CoordSystem.ne_R_of_le_π hR_π le_sup_right)
    (Ne.symm he_V) (Ne.symm he_R) he_VR

theorem CoordSystem.RV_eq_Re (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {e : L} (he : IsAtom e) (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V) (he_R : e ≠ R) :
    R ⊔ Γ.V = R ⊔ e :=
  line_eq_of_atom_le hR Γ.hV he (CoordSystem.ne_R_of_le_π hR_π le_sup_right).symm
    (Ne.symm he_R) (Ne.symm he_V) (he_VR.trans (sup_comm Γ.V R).le)

theorem CoordSystem.ζ_sup_e (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {e : L} (he : IsAtom e) (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V) (he_R : e ≠ R) :
    Γ.O ⊔ R ⊔ e = Γ.O ⊔ Γ.V ⊔ e := by
  rw [sup_assoc, sup_assoc, ← CoordSystem.RV_eq_Re hR hR_π he he_VR he_V he_R,
    ← CoordSystem.VR_eq_Ve hR hR_π he he_VR he_V he_R, sup_comm R Γ.V]

theorem CoordSystem.ne_e_of_on_ζ (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {e : L} (he : IsAtom e) (he_VR : e ≤ Γ.V ⊔ R) (he_R : e ≠ R)
    {z : L} (hz_ζ : z ≤ Γ.O ⊔ R) : z ≠ e :=
  fun h => CoordSystem.e_not_ζ hR hR_π he he_VR he_R (h ▸ hz_ζ)

theorem CoordSystem.ne_e_of_on_n (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {e : L} (he : IsAtom e) (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V)
    {y : L} (hy_n : y ≤ Γ.O ⊔ Γ.V) : y ≠ e :=
  fun h => CoordSystem.e_not_n hR hR_π he he_VR he_V (h ▸ hy_n)

/-! ## The `e`-gauge: the z-axis read onto the ordinate axis through `e` -/

def CoordSystem.ncoord (Γ : CoordSystem L) (e z : L) : L :=
  (z ⊔ e) ⊓ (Γ.O ⊔ Γ.V)

theorem CoordSystem.ncoord_is_atom (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {e : L} (he : IsAtom e)
    (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V) (he_R : e ≠ R)
    {z : L} (hz : IsAtom z) (hz_ζ : z ≤ Γ.O ⊔ R) :
    IsAtom (Γ.ncoord e z) :=
  perspect_atom he hz
    (CoordSystem.ne_e_of_on_ζ hR hR_π he he_VR he_R hz_ζ)
    Γ.hO Γ.hV Γ.hOV (CoordSystem.e_not_n hR hR_π he he_VR he_V)
    (CoordSystem.ζ_sup_e hR hR_π he he_VR he_V he_R ▸
      (sup_le (hz_ζ.trans le_sup_left) le_sup_right))

theorem CoordSystem.ncoord_le_n (Γ : CoordSystem L) (e z : L) :
    Γ.ncoord e z ≤ Γ.O ⊔ Γ.V :=
  inf_le_right

theorem CoordSystem.ncoord_ne_V (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {e : L} (he : IsAtom e)
    (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V) (he_R : e ≠ R)
    {z : L} (hz : IsAtom z) (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    Γ.ncoord e z ≠ Γ.V := by
  intro h
  have hV_le : Γ.V ≤ z ⊔ e := h ▸ (inf_le_left : Γ.ncoord e z ≤ z ⊔ e)
  have h_line : e ⊔ z = e ⊔ Γ.V :=
    line_eq_of_atom_le' he hz Γ.hV
      (Ne.symm (CoordSystem.ne_e_of_on_ζ hR hR_π he he_VR he_R hz_ζ))
      he_V (hV_le.trans (sup_comm z e).le)
  have hz_le : z ≤ Γ.V ⊔ R := by
    calc z ≤ e ⊔ z := le_sup_right
      _ = e ⊔ Γ.V := h_line
      _ = Γ.V ⊔ e := sup_comm _ _
      _ = Γ.V ⊔ R := (CoordSystem.VR_eq_Ve hR hR_π he he_VR he_V he_R).symm
  exact hz_R (IsAtom.eq_of_le hz hR
    (le_of_le_of_eq (le_inf hz_ζ hz_le) (CoordSystem.ζ_inf_VR hR hR_π)))

theorem CoordSystem.ncoord_O (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {e : L} (he : IsAtom e)
    (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V) :
    Γ.ncoord e Γ.O = Γ.O :=
  perspect_fixes_intersection he Γ.hO
    (CoordSystem.ne_e_of_on_n hR hR_π he he_VR he_V le_sup_left)
    Γ.hO Γ.hV Γ.hOV (CoordSystem.e_not_n hR hR_π he he_VR he_V)
    (le_sup_left : Γ.O ≤ Γ.O ⊔ R) le_sup_left
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right)

theorem CoordSystem.ncoord_R (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {e : L} (he : IsAtom e)
    (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V) (he_R : e ≠ R) :
    Γ.ncoord e R = Γ.V := by
  show (R ⊔ e) ⊓ (Γ.O ⊔ Γ.V) = Γ.V
  rw [← CoordSystem.RV_eq_Re hR hR_π he he_VR he_V he_R, sup_comm R Γ.V,
    inf_comm]
  exact CoordSystem.n_inf_VR hR hR_π

/-! ## The shear projection: the drop through an infinity center onto `π` -/

def CoordSystem.shproj (Γ : CoordSystem L) (w t : L) : L :=
  (t ⊔ w) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V)

theorem CoordSystem.ne_center_of_off_σ {w t : L}
    (hw_σ : w ≤ Γ.U ⊔ Γ.V ⊔ R) (ht_σ : ¬ t ≤ Γ.U ⊔ Γ.V ⊔ R) : t ≠ w :=
  fun h => ht_σ (h ▸ hw_σ)

theorem CoordSystem.shproj_is_atom (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {w : L} (hw : IsAtom w)
    (hw_σ : w ≤ Γ.U ⊔ Γ.V ⊔ R) (hw_π : ¬ w ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {t : L} (ht : IsAtom t) (ht_τ : t ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R)
    (ht_σ : ¬ t ≤ Γ.U ⊔ Γ.V ⊔ R) :
    IsAtom (Γ.shproj w t) :=
  line_meets_hyperplane (CoordSystem.π_covBy_τ hR hR_π) ht hw
    (CoordSystem.ne_center_of_off_σ hw_σ ht_σ)
    (sup_le ht_τ (hw_σ.trans (sup_le (Γ.m_le_π.trans le_sup_left) le_sup_right)))
    (fun h => hw_π (le_sup_right.trans h))

theorem CoordSystem.shproj_le_π (Γ : CoordSystem L) (w t : L) :
    Γ.shproj w t ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
  inf_le_right

theorem CoordSystem.sup_center_shproj (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {w : L} (hw : IsAtom w)
    (hw_σ : w ≤ Γ.U ⊔ Γ.V ⊔ R) (hw_π : ¬ w ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {t : L} (ht : IsAtom t) (ht_τ : t ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R)
    (ht_σ : ¬ t ≤ Γ.U ⊔ Γ.V ⊔ R) :
    t ⊔ w = Γ.shproj w t ⊔ w := by
  have hs_atom := CoordSystem.shproj_is_atom hR hR_π hw hw_σ hw_π ht ht_τ ht_σ
  have h := line_eq_of_atom_le' hw ht hs_atom
    (Ne.symm (CoordSystem.ne_center_of_off_σ hw_σ ht_σ))
    (fun h' => hw_π (h' ▸ Γ.shproj_le_π w t))
    (le_of_le_of_eq (inf_le_left : Γ.shproj w t ≤ t ⊔ w) (sup_comm t w))
  rw [sup_comm t w, sup_comm (Γ.shproj w t) w]
  exact h

theorem CoordSystem.shproj_affine (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {w : L} (hw : IsAtom w)
    (hw_σ : w ≤ Γ.U ⊔ Γ.V ⊔ R) (hw_π : ¬ w ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {t : L} (ht : IsAtom t) (ht_τ : t ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R)
    (ht_σ : ¬ t ≤ Γ.U ⊔ Γ.V ⊔ R) :
    ¬ Γ.shproj w t ≤ Γ.U ⊔ Γ.V := by
  intro h
  apply ht_σ
  calc t ≤ t ⊔ w := le_sup_left
    _ = Γ.shproj w t ⊔ w :=
        CoordSystem.sup_center_shproj hR hR_π hw hw_σ hw_π ht ht_τ ht_σ
    _ ≤ Γ.U ⊔ Γ.V ⊔ R := sup_le (h.trans le_sup_left) hw_σ

theorem CoordSystem.shproj_le_base_sup {x w : L}
    (hx_π : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hw_le : w ≤ x ⊔ R) (t : L) :
    Γ.shproj w t ≤ Γ.baseproj R t ⊔ x := by
  have h1 : Γ.shproj w t ≤ (x ⊔ (t ⊔ R)) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) :=
    le_inf (inf_le_left.trans (sup_le (le_sup_left.trans le_sup_right)
      (hw_le.trans (sup_le le_sup_left (le_sup_right.trans le_sup_right)))))
      inf_le_right
  rw [sup_inf_assoc_of_le (t ⊔ R) hx_π] at h1
  exact h1.trans (sup_comm x _).le

/-! ## The two preservation halves: `c` keeps the ordinate, `e` the abscissa -/

theorem CoordSystem.ycoord_shproj_c (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U)
    {t : L} (ht : IsAtom t) (ht_τ : t ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R)
    (ht_σ : ¬ t ≤ Γ.U ⊔ Γ.V ⊔ R) :
    Γ.ycoord (Γ.shproj c t) = Γ.ycoord (Γ.baseproj R t) := by
  have hc_σ : c ≤ Γ.U ⊔ Γ.V ⊔ R := hc_UR.trans (Γ.UR_le_σ R)
  have hc_π := CoordSystem.hc_not_π hR hR_π hc hc_UR hc_U
  have hb_atom := CoordSystem.baseproj_is_atom hR hR_π ht ht_τ ht_σ
  have hb_π := Γ.baseproj_le_π R t
  have hb_aff := CoordSystem.baseproj_affine hR hR_π ht ht_τ ht_σ
  have hs_atom := CoordSystem.shproj_is_atom hR hR_π hc hc_σ hc_π ht ht_τ ht_σ
  have hs_aff := CoordSystem.shproj_affine hR hR_π hc hc_σ hc_π ht ht_τ ht_σ
  exact (Γ.le_horizontal_iff hs_atom (Γ.shproj_le_π c t) hs_aff
      hb_atom hb_π hb_aff).mp
    (CoordSystem.shproj_le_base_sup
      (le_sup_right.trans le_sup_left : Γ.U ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) hc_UR t)

theorem CoordSystem.xproj_shproj_e (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {e : L} (he : IsAtom e)
    (he_VR : e ≤ Γ.V ⊔ R) (he_V : e ≠ Γ.V)
    {t : L} (ht : IsAtom t) (ht_τ : t ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R)
    (ht_σ : ¬ t ≤ Γ.U ⊔ Γ.V ⊔ R) :
    Γ.xproj (Γ.shproj e t) = Γ.xproj (Γ.baseproj R t) := by
  have he_σ : e ≤ Γ.U ⊔ Γ.V ⊔ R := he_VR.trans (Γ.VR_le_σ R)
  have he_π := CoordSystem.he_not_π hR hR_π he he_VR he_V
  have hb_atom := CoordSystem.baseproj_is_atom hR hR_π ht ht_τ ht_σ
  have hb_aff := CoordSystem.baseproj_affine hR hR_π ht ht_τ ht_σ
  have hs_atom := CoordSystem.shproj_is_atom hR hR_π he he_σ he_π ht ht_τ ht_σ
  have hs_aff := CoordSystem.shproj_affine hR hR_π he he_σ he_π ht ht_τ ht_σ
  have hle : Γ.shproj e t ≤ Γ.baseproj R t ⊔ Γ.V :=
    CoordSystem.shproj_le_base_sup
      (le_sup_right : Γ.V ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) he_VR t
  have h_line : Γ.V ⊔ Γ.baseproj R t = Γ.V ⊔ Γ.shproj e t :=
    line_eq_of_atom_le' Γ.hV hb_atom hs_atom
      (Ne.symm (Γ.ne_V_of_affine hb_aff)) (Ne.symm (Γ.ne_V_of_affine hs_aff))
      (hle.trans (sup_comm _ Γ.V).le)
  exact (Γ.xproj_eq_of_sup_V (by
    rw [sup_comm (Γ.shproj e t) Γ.V, sup_comm (Γ.baseproj R t) Γ.V]
    exact h_line.symm))

/-! ## The z-attachment: a space point rides its height's horizontal ray -/

theorem CoordSystem.le_zproj_sup_dir (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {t : L} (ht : IsAtom t) (ht_τ : t ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R)
    (ht_σ : ¬ t ≤ Γ.U ⊔ Γ.V ⊔ R) (hb_ne_O : Γ.baseproj R t ≠ Γ.O) :
    t ≤ Γ.zproj R t ⊔ ((Γ.O ⊔ Γ.baseproj R t) ⊓ (Γ.U ⊔ Γ.V)) := by
  have hb_atom := CoordSystem.baseproj_is_atom hR hR_π ht ht_τ ht_σ
  have hb_π := Γ.baseproj_le_π R t
  have hz_ζ := Γ.zproj_le_ζ R t
  have hO_ne_b : Γ.O ≠ Γ.baseproj R t := fun h => hb_ne_O h.symm
  have hOb_π : Γ.O ⊔ Γ.baseproj R t ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_left.trans le_sup_left) hb_π
  have hΞ_le_τ : Γ.O ⊔ Γ.baseproj R t ⊔ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
    sup_le (hOb_π.trans le_sup_left) le_sup_right
  have hΞπ : (Γ.O ⊔ Γ.baseproj R t ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) =
      Γ.O ⊔ Γ.baseproj R t := by
    rw [sup_inf_assoc_of_le R hOb_π, CoordSystem.R_inf_π hR hR_π, sup_bot_eq]
  have hΞ_cov : Γ.O ⊔ Γ.baseproj R t ⊔ R ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R := by
    have h1 : (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊓ (Γ.O ⊔ Γ.baseproj R t ⊔ R) ⋖
        Γ.O ⊔ Γ.U ⊔ Γ.V := by
      rw [inf_comm, hΞπ]
      exact Γ.line_covBy_π Γ.hO hb_atom hO_ne_b
        (le_sup_left.trans le_sup_left) hb_π
    have h2 := covBy_sup_of_inf_covBy_left h1
    have h3 : (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊔ (Γ.O ⊔ Γ.baseproj R t ⊔ R) =
        Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R := by
      apply le_antisymm
      · exact sup_le le_sup_left hΞ_le_τ
      · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
    rwa [h3] at h2
  have h_m_not_Ξ : ¬ Γ.U ⊔ Γ.V ≤ Γ.O ⊔ Γ.baseproj R t ⊔ R := by
    intro h
    have hπΞ : Γ.O ⊔ Γ.U ⊔ Γ.V ≤ Γ.O ⊔ Γ.baseproj R t ⊔ R := by
      have h' : Γ.O ⊔ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.baseproj R t ⊔ R :=
        sup_le (le_sup_left.trans le_sup_left) h
      rwa [← sup_assoc] at h'
    have hπ_eq : Γ.O ⊔ Γ.U ⊔ Γ.V = Γ.O ⊔ Γ.baseproj R t := by
      rw [← hΞπ]
      exact le_antisymm (le_inf hπΞ le_rfl) inf_le_right
    have hV_le : Γ.V ≤ Γ.O ⊔ Γ.baseproj R t := hπ_eq ▸ le_sup_right
    have hU_le : Γ.U ≤ Γ.O ⊔ Γ.baseproj R t :=
      hπ_eq ▸ (le_sup_right.trans le_sup_left)
    have h_line : Γ.O ⊔ Γ.baseproj R t = Γ.O ⊔ Γ.V :=
      line_eq_of_atom_le' Γ.hO hb_atom Γ.hV hO_ne_b Γ.hOV hV_le
    exact Γ.hU_not_n (h_line ▸ hU_le)
  have h_mΞ_atom : IsAtom ((Γ.U ⊔ Γ.V) ⊓ (Γ.O ⊔ Γ.baseproj R t ⊔ R)) :=
    line_meets_hyperplane hΞ_cov Γ.hU Γ.hV Γ.hUV
      (Γ.m_le_π.trans le_sup_left) h_m_not_Ξ
  have hd_atom : IsAtom ((Γ.O ⊔ Γ.baseproj R t) ⊓ (Γ.U ⊔ Γ.V)) :=
    trace_atom Γ.hO hb_atom hO_ne_b Γ.m_covBy_π hOb_π
      (fun h => Γ.hO_not_m (le_sup_left.trans h))
  have h_d_eq : (Γ.U ⊔ Γ.V) ⊓ (Γ.O ⊔ Γ.baseproj R t ⊔ R) =
      (Γ.O ⊔ Γ.baseproj R t) ⊓ (Γ.U ⊔ Γ.V) :=
    (IsAtom.eq_of_le hd_atom h_mΞ_atom
      (le_inf inf_le_right (inf_le_left.trans le_sup_left))).symm
  have ht_le : t ≤ (Γ.zproj R t ⊔ (Γ.U ⊔ Γ.V)) ⊓
      (Γ.O ⊔ Γ.baseproj R t ⊔ R) := by
    refine le_inf ?_ ?_
    · exact le_sup_left.trans
        (CoordSystem.sup_m_zproj hR hR_π ht ht_τ ht_σ).le
    · have h1 : t ≤ Γ.baseproj R t ⊔ R :=
        le_sup_left.trans (CoordSystem.sup_R_baseproj hR hR_π ht ht_τ ht_σ).le
      exact h1.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hz_Ξ : Γ.zproj R t ≤ Γ.O ⊔ Γ.baseproj R t ⊔ R :=
    hz_ζ.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have h_meet : (Γ.zproj R t ⊔ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ Γ.baseproj R t ⊔ R) =
      Γ.zproj R t ⊔ ((Γ.O ⊔ Γ.baseproj R t) ⊓ (Γ.U ⊔ Γ.V)) := by
    rw [sup_inf_assoc_of_le (Γ.U ⊔ Γ.V) hz_Ξ, h_d_eq]
  rw [← h_meet]
  exact ht_le

/-! ## The gauge rays: the sheared image rides the gauge point's direction ray -/

theorem CoordSystem.shproj_le_gauge_sup_c (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc_UR : c ≤ Γ.U ⊔ R)
    {t : L} (ht : IsAtom t) (ht_τ : t ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R)
    (ht_σ : ¬ t ≤ Γ.U ⊔ Γ.V ⊔ R) (hb_ne_O : Γ.baseproj R t ≠ Γ.O) :
    Γ.shproj c t ≤ Γ.zcoord c (Γ.zproj R t) ⊔
      ((Γ.O ⊔ Γ.baseproj R t) ⊓ (Γ.U ⊔ Γ.V)) := by
  have hd_π : (Γ.O ⊔ Γ.baseproj R t) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    inf_le_right.trans Γ.m_le_π
  have h1 : Γ.shproj c t ≤
      (((Γ.O ⊔ Γ.baseproj R t) ⊓ (Γ.U ⊔ Γ.V)) ⊔ (Γ.zproj R t ⊔ c)) ⊓
        (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
    refine le_inf (inf_le_left.trans (sup_le ?_ ?_)) inf_le_right
    · exact (CoordSystem.le_zproj_sup_dir hR hR_π ht ht_τ ht_σ hb_ne_O).trans
        (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
    · exact le_sup_right.trans le_sup_right
  rw [sup_inf_assoc_of_le (Γ.zproj R t ⊔ c) hd_π] at h1
  have h2 : (Γ.zproj R t ⊔ c) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) =
      Γ.zcoord c (Γ.zproj R t) := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      have h3 : Γ.zproj R t ⊔ c ≤ (Γ.O ⊔ Γ.U) ⊔ R :=
        sup_le ((Γ.zproj_le_ζ R t).trans
          (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
          (hc_UR.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
      calc (Γ.zproj R t ⊔ c) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) ≤
            ((Γ.O ⊔ Γ.U) ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) := inf_le_inf_right _ h3
        _ = Γ.O ⊔ Γ.U := by
            rw [sup_inf_assoc_of_le R (le_sup_left : Γ.O ⊔ Γ.U ≤ _),
              CoordSystem.R_inf_π hR hR_π, sup_bot_eq]
    · exact le_inf inf_le_left (inf_le_right.trans le_sup_left)
  rw [h2] at h1
  exact h1.trans (sup_comm _ _).le

theorem CoordSystem.shproj_le_gauge_sup_e (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {e : L} (he_VR : e ≤ Γ.V ⊔ R)
    {t : L} (ht : IsAtom t) (ht_τ : t ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R)
    (ht_σ : ¬ t ≤ Γ.U ⊔ Γ.V ⊔ R) (hb_ne_O : Γ.baseproj R t ≠ Γ.O) :
    Γ.shproj e t ≤ Γ.ncoord e (Γ.zproj R t) ⊔
      ((Γ.O ⊔ Γ.baseproj R t) ⊓ (Γ.U ⊔ Γ.V)) := by
  have hd_π : (Γ.O ⊔ Γ.baseproj R t) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    inf_le_right.trans Γ.m_le_π
  have h1 : Γ.shproj e t ≤
      (((Γ.O ⊔ Γ.baseproj R t) ⊓ (Γ.U ⊔ Γ.V)) ⊔ (Γ.zproj R t ⊔ e)) ⊓
        (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
    refine le_inf (inf_le_left.trans (sup_le ?_ ?_)) inf_le_right
    · exact (CoordSystem.le_zproj_sup_dir hR hR_π ht ht_τ ht_σ hb_ne_O).trans
        (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
    · exact le_sup_right.trans le_sup_right
  rw [sup_inf_assoc_of_le (Γ.zproj R t ⊔ e) hd_π] at h1
  have h2 : (Γ.zproj R t ⊔ e) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) =
      Γ.ncoord e (Γ.zproj R t) := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      have h3 : Γ.zproj R t ⊔ e ≤ (Γ.O ⊔ Γ.V) ⊔ R :=
        sup_le ((Γ.zproj_le_ζ R t).trans
          (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
          (he_VR.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
      calc (Γ.zproj R t ⊔ e) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) ≤
            ((Γ.O ⊔ Γ.V) ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) := inf_le_inf_right _ h3
        _ = Γ.O ⊔ Γ.V := by
            rw [sup_inf_assoc_of_le R
                (sup_le (le_sup_left.trans le_sup_left) le_sup_right :
                  Γ.O ⊔ Γ.V ≤ _),
              CoordSystem.R_inf_π hR hR_π, sup_bot_eq]
    · exact le_inf inf_le_left
        (inf_le_right.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  rw [h2] at h1
  exact h1.trans (sup_comm _ _).le

/-! ## The drops of the z-axis itself -/

theorem CoordSystem.shproj_c_eq_zcoord (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc_UR : c ≤ Γ.U ⊔ R)
    {z : L} (hz_ζ : z ≤ Γ.O ⊔ R) :
    Γ.shproj c z = Γ.zcoord c z := by
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    have h3 : z ⊔ c ≤ (Γ.O ⊔ Γ.U) ⊔ R :=
      sup_le (hz_ζ.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
        (hc_UR.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
    calc Γ.shproj c z ≤ ((Γ.O ⊔ Γ.U) ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) :=
          le_inf (inf_le_left.trans h3) inf_le_right
      _ = Γ.O ⊔ Γ.U := by
          rw [sup_inf_assoc_of_le R (le_sup_left : Γ.O ⊔ Γ.U ≤ _),
            CoordSystem.R_inf_π hR hR_π, sup_bot_eq]
  · exact le_inf inf_le_left (inf_le_right.trans le_sup_left)

theorem CoordSystem.shproj_e_eq_ncoord (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {e : L} (he_VR : e ≤ Γ.V ⊔ R)
    {z : L} (hz_ζ : z ≤ Γ.O ⊔ R) :
    Γ.shproj e z = Γ.ncoord e z := by
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    have h3 : z ⊔ e ≤ (Γ.O ⊔ Γ.V) ⊔ R :=
      sup_le (hz_ζ.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
        (he_VR.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
    calc Γ.shproj e z ≤ ((Γ.O ⊔ Γ.V) ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) :=
          le_inf (inf_le_left.trans h3) inf_le_right
      _ = Γ.O ⊔ Γ.V := by
          rw [sup_inf_assoc_of_le R
              (sup_le (le_sup_left.trans le_sup_left) le_sup_right :
                Γ.O ⊔ Γ.V ≤ Γ.O ⊔ Γ.U ⊔ Γ.V),
            CoordSystem.R_inf_π hR hR_π, sup_bot_eq]
  · exact le_inf inf_le_left
      (inf_le_right.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))


/-! ## The base direction: the ray from the origin through the base point -/

theorem CoordSystem.base_dir_facts {b : L} (hb : IsAtom b)
    (hb_π : b ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hb_ne_O : b ≠ Γ.O)
    (hb_not_l : ¬ b ≤ Γ.O ⊔ Γ.U) (hb_not_n : ¬ b ≤ Γ.O ⊔ Γ.V) :
    IsAtom ((Γ.O ⊔ b) ⊓ (Γ.U ⊔ Γ.V)) ∧
    (Γ.O ⊔ b) ⊓ (Γ.U ⊔ Γ.V) ≠ Γ.U ∧
    (Γ.O ⊔ b) ⊓ (Γ.U ⊔ Γ.V) ≠ Γ.V ∧
    b ≤ Γ.O ⊔ ((Γ.O ⊔ b) ⊓ (Γ.U ⊔ Γ.V)) := by
  have hO_ne_b : Γ.O ≠ b := fun h => hb_ne_O h.symm
  have hOb_π : Γ.O ⊔ b ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_left.trans le_sup_left) hb_π
  have hd_atom : IsAtom ((Γ.O ⊔ b) ⊓ (Γ.U ⊔ Γ.V)) :=
    trace_atom Γ.hO hb hO_ne_b Γ.m_covBy_π hOb_π
      (fun h => Γ.hO_not_m (le_sup_left.trans h))
  have hd_m : (Γ.O ⊔ b) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V := inf_le_right
  refine ⟨hd_atom, ?_, ?_, ?_⟩
  · intro h
    have hU_le : Γ.U ≤ Γ.O ⊔ b := le_of_eq_of_le h.symm inf_le_left
    have h_line : Γ.O ⊔ b = Γ.O ⊔ Γ.U :=
      line_eq_of_atom_le' Γ.hO hb Γ.hU hO_ne_b Γ.hOU hU_le
    exact hb_not_l (h_line ▸ (le_sup_right : b ≤ Γ.O ⊔ b))
  · intro h
    have hV_le : Γ.V ≤ Γ.O ⊔ b := le_of_eq_of_le h.symm inf_le_left
    have h_line : Γ.O ⊔ b = Γ.O ⊔ Γ.V :=
      line_eq_of_atom_le' Γ.hO hb Γ.hV hO_ne_b Γ.hOV hV_le
    exact hb_not_n (h_line ▸ (le_sup_right : b ≤ Γ.O ⊔ b))
  · have h_line : Γ.O ⊔ b = Γ.O ⊔ ((Γ.O ⊔ b) ⊓ (Γ.U ⊔ Γ.V)) :=
      line_eq_of_atom_le' Γ.hO hb hd_atom hO_ne_b
        (fun h => Γ.hO_not_m (le_of_eq_of_le h hd_m)) inf_le_left
    exact h_line ▸ (le_sup_right : b ≤ Γ.O ⊔ b)

/-! ## The affine equation solver in the coordinate ring -/

def Coordinate.mk (Γ : CoordSystem L) (a : L) (h1 : IsAtom a)
    (h2 : a ≤ Γ.O ⊔ Γ.U) (h3 : a ≠ Γ.U) : Coordinate Γ :=
  ⟨a, h1, h2, h3⟩

theorem Coordinate.mk_val (Γ : CoordSystem L) (a : L) (h1 : IsAtom a)
    (h2 : a ≤ Γ.O ⊔ Γ.U) (h3 : a ≠ Γ.U) : (Coordinate.mk Γ a h1 h2 h3).1 = a :=
  rfl

theorem CoordFrame.affine_solve (Φ : CoordFrame L)
    (s xω xb xz yB : Coordinate Φ.Γ) (hs : s ≠ 0)
    (e1 : s * xω + yB = s * xb) (e2 : s * xz + yB = 0) :
    xω = xb + xz := by
  have hY : yB = -(s * xz) := eq_neg_of_add_eq_zero_right e2
  rw [hY] at e1
  have h1 := congrArg (fun w => w + s * xz) e1
  simp only [add_assoc, neg_add_cancel, add_zero] at h1
  rw [← mul_add] at h1
  exact mul_left_cancel₀ hs h1

/-! ## The x-shear, general position -/

theorem CoordFrame.xproj_shproj_c_of_base (Φ : CoordFrame L) {c : L}
    (hc : IsAtom c) (hc_UR : c ≤ Φ.Γ.U ⊔ Φ.R) (hc_U : c ≠ Φ.Γ.U) (hc_R : c ≠ Φ.R)
    {t b : L} (ht : IsAtom t) (ht_τ : t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (ht_σ : ¬ t ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R) (hb_def : Φ.Γ.baseproj Φ.R t = b)
    (hb_ne_O : b ≠ Φ.Γ.O) (hb_not_l : ¬ b ≤ Φ.Γ.O ⊔ Φ.Γ.U)
    (hb_not_n : ¬ b ≤ Φ.Γ.O ⊔ Φ.Γ.V) :
    Φ.Γ.xproj (Φ.Γ.shproj c t) =
      coord_add Φ.Γ (Φ.Γ.xproj b) (Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t)) := by
  have hR := Φ.hR_atom
  have hR_π := Φ.hR_not
  have hc_σ : c ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := hc_UR.trans (Φ.Γ.UR_le_σ Φ.R)
  have hc_π := CoordSystem.hc_not_π hR hR_π hc hc_UR hc_U
  have hb_atom : IsAtom b :=
    hb_def ▸ CoordSystem.baseproj_is_atom hR hR_π ht ht_τ ht_σ
  have hb_π : b ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V := hb_def ▸ Φ.Γ.baseproj_le_π Φ.R t
  have hb_aff : ¬ b ≤ Φ.Γ.U ⊔ Φ.Γ.V :=
    hb_def ▸ CoordSystem.baseproj_affine hR hR_π ht ht_τ ht_σ
  have hz_atom := CoordSystem.zproj_is_atom hR hR_π ht ht_τ ht_σ
  have hz_ζ := Φ.Γ.zproj_le_ζ Φ.R t
  have hz_R := CoordSystem.zproj_ne_R hR_π ht ht_σ
  have hx_atom := CoordSystem.zcoord_is_atom hR hR_π hc hc_UR hc_U hc_R
    hz_atom hz_ζ
  have hx_l := Φ.Γ.zcoord_le_l c (Φ.Γ.zproj Φ.R t)
  have hx_U := CoordSystem.zcoord_ne_U hR hR_π hc hc_UR hc_U hc_R
    hz_atom hz_ζ hz_R
  have hx_aff := Φ.Γ.affine_of_on_l hx_atom hx_l hx_U
  have hx_π : Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V :=
    hx_l.trans le_sup_left
  have hs_atom := CoordSystem.shproj_is_atom hR hR_π hc hc_σ hc_π ht ht_τ ht_σ
  have hs_π := Φ.Γ.shproj_le_π c t
  have hs_aff := CoordSystem.shproj_affine hR hR_π hc hc_σ hc_π ht ht_τ ht_σ
  obtain ⟨hd_atom, hd_ne_U, hd_ne_V, hb_le_Od⟩ :=
    CoordSystem.base_dir_facts hb_atom hb_π hb_ne_O hb_not_l hb_not_n
  have hd_m : (Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) ≤ Φ.Γ.U ⊔ Φ.Γ.V := inf_le_right
  have hyb_eq : Φ.Γ.ycoord b =
      coord_mul Φ.Γ (Φ.Γ.slope ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) (Φ.Γ.xproj b) :=
    (Φ.Γ.le_origin_line_iff hd_atom hd_m hd_ne_V hb_atom hb_π hb_aff
      Φ.R hR hR_π Φ.h_irred).mp hb_le_Od
  have hxd_ne : Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ≠
      (Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) :=
    fun h => hx_aff (le_of_eq_of_le h hd_m)
  have hn_cov : Φ.Γ.O ⊔ Φ.Γ.V ⋖ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V :=
    Φ.Γ.sup_V_covBy_π Φ.Γ.hO le_sup_left Φ.Γ.hOU
  have hxd_π : Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V :=
    sup_le hx_π (hd_m.trans Φ.Γ.m_le_π)
  have hxd_not_n : ¬ Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) ≤ Φ.Γ.O ⊔ Φ.Γ.V := by
    intro h
    apply hd_ne_V
    exact IsAtom.eq_of_le hd_atom Φ.Γ.hV
      (le_of_le_of_eq (le_inf (le_sup_right.trans h) hd_m) Φ.Γ.n_inf_m_eq_V)
  have hB_atom : IsAtom ((Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V)) :=
    trace_atom hx_atom hd_atom hxd_ne hn_cov hxd_π hxd_not_n
  have hB_n : (Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V) ≤ Φ.Γ.O ⊔ Φ.Γ.V :=
    inf_le_right
  have hB_ne_V : (Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V) ≠ Φ.Γ.V := by
    intro h
    have hV_le : Φ.Γ.V ≤ Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
        ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) := le_of_eq_of_le h.symm inf_le_left
    have h1 : Φ.Γ.V ≤ (Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
        ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) :=
      le_inf hV_le le_sup_right
    rw [line_direction (m := Φ.Γ.U ⊔ Φ.Γ.V) hx_atom hx_aff hd_m] at h1
    exact hd_ne_V (IsAtom.eq_of_le Φ.Γ.hV hd_atom h1).symm
  have hB_ne_d : (Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V) ≠
      (Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) := by
    intro h
    have hd_n : (Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) ≤ Φ.Γ.O ⊔ Φ.Γ.V :=
      le_of_eq_of_le h.symm inf_le_right
    exact hd_ne_V (IsAtom.eq_of_le hd_atom Φ.Γ.hV
      (le_of_le_of_eq (le_inf hd_n hd_m) Φ.Γ.n_inf_m_eq_V))
  have hBd_line : ((Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V)) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) =
      Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔ ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) :=
    line_eq_of_two_atoms_le hx_atom hd_atom hxd_ne hB_atom hd_atom hB_ne_d
      inf_le_left le_sup_right
  have hωt_le : Φ.Γ.shproj c t ≤ ((Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V)) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) := by
    rw [hBd_line]
    have h := CoordSystem.shproj_le_gauge_sup_c hR hR_π hc_UR ht ht_τ ht_σ
      (fun h' => hb_ne_O (hb_def.symm.trans h'))
    rwa [hb_def] at h
  have hx_le : Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ≤
      ((Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V)) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) := by
    rw [hBd_line]
    exact le_sup_left
  have hB_π : (Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V) ≤
      Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V :=
    hB_n.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hB_aff := Φ.Γ.affine_of_on_n hB_atom hB_n hB_ne_V
  have heq1 := (Φ.Γ.le_line_iff hd_atom hd_m hd_ne_V hB_atom hB_n hB_ne_V
    hs_atom hs_π hs_aff Φ.P Φ.hP_atom Φ.hP_plane Φ.hP_not_l Φ.hP_not_m
    Φ.hP_not_OC Φ.hP_ne_I Φ.hP_ne_O Φ.R hR hR_π Φ.h_irred).mp hωt_le
  have heq2 := (Φ.Γ.le_line_iff hd_atom hd_m hd_ne_V hB_atom hB_n hB_ne_V
    hx_atom hx_π hx_aff Φ.P Φ.hP_atom Φ.hP_plane Φ.hP_not_l Φ.hP_not_m
    Φ.hP_not_OC Φ.hP_ne_I Φ.hP_ne_O Φ.R hR hR_π Φ.h_irred).mp hx_le
  rw [Φ.Γ.ycoord_of_on_l hx_atom hx_l hx_U,
    Φ.Γ.xproj_of_on_l hx_atom hx_l hx_U] at heq2
  have heq3 := CoordSystem.ycoord_shproj_c hR hR_π hc hc_UR hc_U ht ht_τ ht_σ
  rw [hb_def] at heq3
  obtain ⟨hsl_atom, hsl_l, hsl_ne_O, hsl_ne_U⟩ :=
    Φ.Γ.slope_facts hd_atom hd_m hd_ne_U hd_ne_V
  have hxω_atom := Φ.Γ.xproj_is_atom hs_atom hs_π hs_aff
  have hxω_l := Φ.Γ.xproj_le_l (Φ.Γ.shproj c t)
  have hxω_U := Φ.Γ.xproj_ne_U hs_atom hs_aff
  have hxb_atom := Φ.Γ.xproj_is_atom hb_atom hb_π hb_aff
  have hxb_l := Φ.Γ.xproj_le_l b
  have hxb_U := Φ.Γ.xproj_ne_U hb_atom hb_aff
  have hyB_atom := Φ.Γ.ycoord_is_atom hB_atom hB_π hB_aff
  have hyB_l := Φ.Γ.ycoord_le_l ((Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t) ⊔
      ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V))
  have hyB_U := Φ.Γ.ycoord_ne_U hB_atom hB_π hB_aff
  have hring : Coordinate.mk Φ.Γ _ hxω_atom hxω_l hxω_U =
      Coordinate.mk Φ.Γ _ hxb_atom hxb_l hxb_U +
      Coordinate.mk Φ.Γ _ hx_atom hx_l hx_U := by
    refine CoordFrame.affine_solve Φ
      (Coordinate.mk Φ.Γ _ hsl_atom hsl_l hsl_ne_U) _ _ _
      (Coordinate.mk Φ.Γ _ hyB_atom hyB_l hyB_U)
      (fun h => hsl_ne_O (congrArg Subtype.val h)) ?_ ?_
    · apply Subtype.ext
      rw [Coordinate.add_val, Coordinate.mul_val, Coordinate.mul_val]
      exact (heq1.symm.trans heq3).trans hyb_eq
    · apply Subtype.ext
      rw [Coordinate.add_val, Coordinate.mul_val]
      exact heq2.symm
  have hval := congrArg Subtype.val hring
  rw [Coordinate.add_val] at hval
  exact hval


/-! ## The x-shear, assembled -/

theorem CoordFrame.xproj_shproj_c (Φ : CoordFrame L) {c : L}
    (hc : IsAtom c) (hc_UR : c ≤ Φ.Γ.U ⊔ Φ.R) (hc_U : c ≠ Φ.Γ.U) (hc_R : c ≠ Φ.R)
    {t : L} (ht : IsAtom t) (ht_τ : t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (ht_σ : ¬ t ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R) :
    Φ.Γ.xproj (Φ.Γ.shproj c t) =
      coord_add Φ.Γ (Φ.Γ.xproj (Φ.Γ.baseproj Φ.R t))
        (Φ.Γ.zcoord c (Φ.Γ.zproj Φ.R t)) := by
  have hR := Φ.hR_atom
  have hR_π := Φ.hR_not
  have hb_atom := CoordSystem.baseproj_is_atom hR hR_π ht ht_τ ht_σ
  have hb_π := Φ.Γ.baseproj_le_π Φ.R t
  have hb_aff := CoordSystem.baseproj_affine hR hR_π ht ht_τ ht_σ
  have hz_atom := CoordSystem.zproj_is_atom hR hR_π ht ht_τ ht_σ
  have hz_ζ := Φ.Γ.zproj_le_ζ Φ.R t
  have hz_R := CoordSystem.zproj_ne_R hR_π ht ht_σ
  by_cases hbO : Φ.Γ.baseproj Φ.R t = Φ.Γ.O
  · have ht_ζ : t ≤ Φ.Γ.O ⊔ Φ.R := by
      have h1 : t ≤ Φ.Γ.baseproj Φ.R t ⊔ Φ.R :=
        le_sup_left.trans (CoordSystem.sup_R_baseproj hR hR_π ht ht_τ ht_σ).le
      rwa [hbO] at h1
    have ht_R : t ≠ Φ.R := CoordSystem.ne_R_of_off_σ ht_σ
    have hzt : Φ.Γ.zproj Φ.R t = t :=
      CoordSystem.zproj_of_on_ζ hR hR_π ht ht_ζ ht_R
    have hx_atom := CoordSystem.zcoord_is_atom hR hR_π hc hc_UR hc_U hc_R ht ht_ζ
    have hx_l := Φ.Γ.zcoord_le_l c t
    have hx_U := CoordSystem.zcoord_ne_U hR hR_π hc hc_UR hc_U hc_R ht ht_ζ ht_R
    rw [CoordSystem.shproj_c_eq_zcoord hR hR_π hc_UR ht_ζ, hzt, hbO,
      Φ.Γ.xproj_of_on_l hx_atom hx_l hx_U,
      Φ.Γ.xproj_of_on_l Φ.Γ.hO le_sup_left Φ.Γ.hOU]
    exact (coord_add_left_zero Φ.Γ _ hx_atom hx_l hx_U).symm
  · have hx_atom := CoordSystem.zcoord_is_atom hR hR_π hc hc_UR hc_U hc_R
      hz_atom hz_ζ
    have hx_l := Φ.Γ.zcoord_le_l c (Φ.Γ.zproj Φ.R t)
    have hx_U := CoordSystem.zcoord_ne_U hR hR_π hc hc_UR hc_U hc_R
      hz_atom hz_ζ hz_R
    by_cases hbn : Φ.Γ.baseproj Φ.R t ≤ Φ.Γ.O ⊔ Φ.Γ.V
    · have hc_σ : c ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := hc_UR.trans (Φ.Γ.UR_le_σ Φ.R)
      have hc_π := CoordSystem.hc_not_π hR hR_π hc hc_UR hc_U
      have hs_atom := CoordSystem.shproj_is_atom hR hR_π hc hc_σ hc_π ht ht_τ ht_σ
      have hs_aff := CoordSystem.shproj_affine hR hR_π hc hc_σ hc_π ht ht_τ ht_σ
      have hO_ne_b : Φ.Γ.O ≠ Φ.Γ.baseproj Φ.R t := fun h => hbO h.symm
      have h_line : Φ.Γ.O ⊔ Φ.Γ.V = Φ.Γ.O ⊔ Φ.Γ.baseproj Φ.R t :=
        line_eq_of_atom_le' Φ.Γ.hO Φ.Γ.hV hb_atom Φ.Γ.hOV hO_ne_b hbn
      have hd_V : (Φ.Γ.O ⊔ Φ.Γ.baseproj Φ.R t) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) = Φ.Γ.V := by
        rw [← h_line]
        exact Φ.Γ.n_inf_m_eq_V
      have hle := CoordSystem.shproj_le_gauge_sup_c hR hR_π hc_UR ht ht_τ ht_σ hbO
      rw [hd_V] at hle
      have hxs := (Φ.Γ.le_vertical_iff hs_atom hs_aff hx_atom hx_l hx_U).mp hle
      have hb_ne_V : Φ.Γ.baseproj Φ.R t ≠ Φ.Γ.V := Φ.Γ.ne_V_of_affine hb_aff
      have hbV : Φ.Γ.baseproj Φ.R t ⊔ Φ.Γ.V = Φ.Γ.O ⊔ Φ.Γ.V :=
        line_eq_of_two_atoms_le Φ.Γ.hO Φ.Γ.hV Φ.Γ.hOV hb_atom Φ.Γ.hV hb_ne_V
          hbn le_sup_right
      have hxb : Φ.Γ.xproj (Φ.Γ.baseproj Φ.R t) = Φ.Γ.O := by
        show (Φ.Γ.baseproj Φ.R t ⊔ Φ.Γ.V) ⊓ (Φ.Γ.O ⊔ Φ.Γ.U) = Φ.Γ.O
        rw [hbV, inf_comm]
        exact Φ.Γ.l_inf_n_eq_O
      rw [hxs, hxb]
      exact (coord_add_left_zero Φ.Γ _ hx_atom hx_l hx_U).symm
    · by_cases hbl : Φ.Γ.baseproj Φ.R t ≤ Φ.Γ.O ⊔ Φ.Γ.U
      · obtain ⟨b', hb'_atom, hb'_le, hb'_ne_b, hb'_ne_V, _⟩ :=
          third_atom_on_line hb_atom Φ.Γ.hV (Φ.Γ.ne_V_of_affine hb_aff) Φ.h_irred
        have hb'_π : b' ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V :=
          hb'_le.trans (sup_le hb_π le_sup_right)
        have hb'_not_m : ¬ b' ≤ Φ.Γ.U ⊔ Φ.Γ.V := by
          intro h
          have h1 : b' ≤ (Φ.Γ.baseproj Φ.R t ⊔ Φ.Γ.V) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) :=
            le_inf hb'_le h
          rw [Φ.Γ.vertical_inf_m hb_atom hbl (Φ.Γ.ne_U_of_affine hb_aff)] at h1
          exact hb'_ne_V (IsAtom.eq_of_le hb'_atom Φ.Γ.hV h1)
        have hV_l_bot : Φ.Γ.V ⊓ (Φ.Γ.O ⊔ Φ.Γ.U) = ⊥ :=
          (Φ.Γ.hV.le_iff.mp inf_le_left).resolve_right
            (fun h => Φ.Γ.hV_off (le_of_eq_of_le h.symm inf_le_right))
        have hb'_not_l : ¬ b' ≤ Φ.Γ.O ⊔ Φ.Γ.U := by
          intro h
          have h2 : (Φ.Γ.baseproj Φ.R t ⊔ Φ.Γ.V) ⊓ (Φ.Γ.O ⊔ Φ.Γ.U) =
              Φ.Γ.baseproj Φ.R t := by
            rw [sup_inf_assoc_of_le Φ.Γ.V hbl, hV_l_bot, sup_bot_eq]
          exact hb'_ne_b (IsAtom.eq_of_le hb'_atom hb_atom
            (le_of_le_of_eq (le_inf hb'_le h) h2))
        have hb'_ne_O : b' ≠ Φ.Γ.O :=
          fun h => hb'_not_l (le_of_eq_of_le h le_sup_left)
        have hb'_not_n : ¬ b' ≤ Φ.Γ.O ⊔ Φ.Γ.V := by
          intro h
          have hb_n_bot : Φ.Γ.baseproj Φ.R t ⊓ (Φ.Γ.O ⊔ Φ.Γ.V) = ⊥ :=
            (hb_atom.le_iff.mp inf_le_left).resolve_right
              (fun h' => hbn (le_of_eq_of_le h'.symm inf_le_right))
          have h2 : (Φ.Γ.baseproj Φ.R t ⊔ Φ.Γ.V) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V) = Φ.Γ.V := by
            rw [sup_comm (Φ.Γ.baseproj Φ.R t) Φ.Γ.V,
              sup_inf_assoc_of_le (Φ.Γ.baseproj Φ.R t)
                (le_sup_right : Φ.Γ.V ≤ Φ.Γ.O ⊔ Φ.Γ.V),
              hb_n_bot, sup_bot_eq]
          exact hb'_ne_V (IsAtom.eq_of_le hb'_atom Φ.Γ.hV
            (le_of_le_of_eq (le_inf hb'_le h) h2))
        have hz_σ := CoordSystem.ζ_affine_off_σ hR hR_π hz_atom hz_ζ hz_R
        have ht'_atom := CoordSystem.spoint_is_atom hR hR_π hb'_atom hb'_π
          hz_atom hz_ζ hz_R
        have ht'_τ : Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t) ≤
            Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := CoordSystem.spoint_le_τ hb'_π
        have ht'_σ := CoordSystem.spoint_off_σ hR hR_π hb'_atom hb'_π hb'_not_m
          hz_atom hz_ζ hz_R
        have ht'_base := CoordSystem.baseproj_spoint hR hR_π hb'_atom hb'_π
          hz_atom hz_ζ hz_R
        have ht'_z := CoordSystem.zproj_spoint hR hR_π hb'_atom hb'_π hb'_not_m
          hz_atom hz_ζ hz_R
        have hL1 : Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t) ≤ t ⊔ Φ.Γ.V := by
          have ht_zm : t ≤ Φ.Γ.zproj Φ.R t ⊔ (Φ.Γ.U ⊔ Φ.Γ.V) :=
            le_sup_left.trans (CoordSystem.sup_m_zproj hR hR_π ht ht_τ ht_σ).le
          have h1 : Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t) ≤
              (Φ.Γ.V ⊔ (t ⊔ Φ.R)) ⊓ (Φ.Γ.zproj Φ.R t ⊔ (Φ.Γ.U ⊔ Φ.Γ.V)) := by
            refine le_inf ?_ inf_le_right
            have h2 : b' ⊔ Φ.R ≤ Φ.Γ.V ⊔ (t ⊔ Φ.R) := by
              refine sup_le ?_ (le_sup_right.trans le_sup_right)
              refine hb'_le.trans (sup_le ?_ le_sup_left)
              exact (inf_le_left : Φ.Γ.baseproj Φ.R t ≤ t ⊔ Φ.R).trans
                le_sup_right
            exact (inf_le_left : Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t) ≤
              b' ⊔ Φ.R).trans h2
          have hR_zm : Φ.R ⊓ (Φ.Γ.zproj Φ.R t ⊔ (Φ.Γ.U ⊔ Φ.Γ.V)) = ⊥ :=
            (hR.le_iff.mp inf_le_left).resolve_right
              (fun h => CoordSystem.hR_not_sup_m hR_π hz_atom hz_σ
                (le_of_eq_of_le h.symm inf_le_right))
          have htR_zm : (t ⊔ Φ.R) ⊓ (Φ.Γ.zproj Φ.R t ⊔ (Φ.Γ.U ⊔ Φ.Γ.V)) = t := by
            rw [sup_inf_assoc_of_le Φ.R ht_zm, hR_zm, sup_bot_eq]
          have hV_zm : Φ.Γ.V ≤ Φ.Γ.zproj Φ.R t ⊔ (Φ.Γ.U ⊔ Φ.Γ.V) :=
            le_sup_right.trans le_sup_right
          rw [sup_inf_assoc_of_le (t ⊔ Φ.R) hV_zm, htR_zm,
            sup_comm Φ.Γ.V t] at h1
          exact h1
        have hc_σ : c ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := hc_UR.trans (Φ.Γ.UR_le_σ Φ.R)
        have hc_π := CoordSystem.hc_not_π hR hR_π hc hc_UR hc_U
        have hs_atom := CoordSystem.shproj_is_atom hR hR_π hc hc_σ hc_π
          ht ht_τ ht_σ
        have hs_aff := CoordSystem.shproj_affine hR hR_π hc hc_σ hc_π ht ht_τ ht_σ
        have hs'_atom := CoordSystem.shproj_is_atom hR hR_π hc hc_σ hc_π
          ht'_atom ht'_τ ht'_σ
        have hs'_aff := CoordSystem.shproj_affine hR hR_π hc hc_σ hc_π
          ht'_atom ht'_τ ht'_σ
        have hsh' : Φ.Γ.shproj c (Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t)) ≤
            Φ.Γ.shproj c t ⊔ Φ.Γ.V := by
          have h1 : Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t) ⊔ c ≤
              Φ.Γ.V ⊔ (t ⊔ c) := by
            refine sup_le (hL1.trans ?_) (le_sup_right.trans le_sup_right)
            exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
          have h2 : Φ.Γ.shproj c (Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t)) ≤
              (Φ.Γ.V ⊔ (t ⊔ c)) ⊓ (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) :=
            le_inf (inf_le_left.trans h1) inf_le_right
          rw [sup_inf_assoc_of_le (t ⊔ c)
            (le_sup_right : Φ.Γ.V ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)] at h2
          exact h2.trans (sup_comm _ _).le
        have hxeq : Φ.Γ.xproj (Φ.Γ.shproj c
            (Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t))) =
            Φ.Γ.xproj (Φ.Γ.shproj c t) := by
          have h_line : Φ.Γ.V ⊔ Φ.Γ.shproj c t =
              Φ.Γ.V ⊔ Φ.Γ.shproj c (Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t)) :=
            line_eq_of_atom_le' Φ.Γ.hV hs_atom hs'_atom
              (Ne.symm (Φ.Γ.ne_V_of_affine hs_aff))
              (Ne.symm (Φ.Γ.ne_V_of_affine hs'_aff))
              (hsh'.trans (sup_comm _ _).le)
          apply Φ.Γ.xproj_eq_of_sup_V
          rw [sup_comm (Φ.Γ.shproj c (Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t)))
            Φ.Γ.V, sup_comm (Φ.Γ.shproj c t) Φ.Γ.V]
          exact h_line.symm
        have hxb' : Φ.Γ.xproj b' = Φ.Γ.xproj (Φ.Γ.baseproj Φ.R t) := by
          have h_line : Φ.Γ.V ⊔ Φ.Γ.baseproj Φ.R t = Φ.Γ.V ⊔ b' :=
            line_eq_of_atom_le' Φ.Γ.hV hb_atom hb'_atom
              (Ne.symm (Φ.Γ.ne_V_of_affine hb_aff)) (Ne.symm hb'_ne_V)
              (hb'_le.trans (sup_comm _ _).le)
          apply Φ.Γ.xproj_eq_of_sup_V
          rw [sup_comm b' Φ.Γ.V, sup_comm (Φ.Γ.baseproj Φ.R t) Φ.Γ.V]
          exact h_line.symm
        have hmain := CoordFrame.xproj_shproj_c_of_base Φ hc hc_UR hc_U hc_R
          ht'_atom ht'_τ ht'_σ ht'_base hb'_ne_O hb'_not_l hb'_not_n
        rw [ht'_z, hxeq, hxb'] at hmain
        exact hmain
      · exact CoordFrame.xproj_shproj_c_of_base Φ hc hc_UR hc_U hc_R
          ht ht_τ ht_σ rfl hbO hbl hbn


/-! ## The y-shear, general position -/

theorem CoordFrame.ycoord_shproj_e_of_base (Φ : CoordFrame L) {e : L}
    (he : IsAtom e) (he_VR : e ≤ Φ.Γ.V ⊔ Φ.R) (he_V : e ≠ Φ.Γ.V) (he_R : e ≠ Φ.R)
    {t b : L} (ht : IsAtom t) (ht_τ : t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (ht_σ : ¬ t ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R) (hb_def : Φ.Γ.baseproj Φ.R t = b)
    (hb_ne_O : b ≠ Φ.Γ.O) (hb_not_l : ¬ b ≤ Φ.Γ.O ⊔ Φ.Γ.U)
    (hb_not_n : ¬ b ≤ Φ.Γ.O ⊔ Φ.Γ.V) :
    Φ.Γ.ycoord (Φ.Γ.shproj e t) =
      coord_add Φ.Γ (Φ.Γ.ycoord b)
        (Φ.Γ.ycoord (Φ.Γ.ncoord e (Φ.Γ.zproj Φ.R t))) := by
  have hR := Φ.hR_atom
  have hR_π := Φ.hR_not
  have he_σ : e ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := he_VR.trans (Φ.Γ.VR_le_σ Φ.R)
  have he_π := CoordSystem.he_not_π hR hR_π he he_VR he_V
  have hb_atom : IsAtom b :=
    hb_def ▸ CoordSystem.baseproj_is_atom hR hR_π ht ht_τ ht_σ
  have hb_π : b ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V := hb_def ▸ Φ.Γ.baseproj_le_π Φ.R t
  have hb_aff : ¬ b ≤ Φ.Γ.U ⊔ Φ.Γ.V :=
    hb_def ▸ CoordSystem.baseproj_affine hR hR_π ht ht_τ ht_σ
  have hz_atom := CoordSystem.zproj_is_atom hR hR_π ht ht_τ ht_σ
  have hz_ζ := Φ.Γ.zproj_le_ζ Φ.R t
  have hz_R := CoordSystem.zproj_ne_R hR_π ht ht_σ
  have hν_atom := CoordSystem.ncoord_is_atom hR hR_π he he_VR he_V he_R
    hz_atom hz_ζ
  have hν_n := Φ.Γ.ncoord_le_n e (Φ.Γ.zproj Φ.R t)
  have hν_V := CoordSystem.ncoord_ne_V hR hR_π he he_VR he_V he_R
    hz_atom hz_ζ hz_R
  have hs_atom := CoordSystem.shproj_is_atom hR hR_π he he_σ he_π ht ht_τ ht_σ
  have hs_π := Φ.Γ.shproj_le_π e t
  have hs_aff := CoordSystem.shproj_affine hR hR_π he he_σ he_π ht ht_τ ht_σ
  obtain ⟨hd_atom, _, hd_ne_V, hb_le_Od⟩ :=
    CoordSystem.base_dir_facts hb_atom hb_π hb_ne_O hb_not_l hb_not_n
  have hd_m : (Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) ≤ Φ.Γ.U ⊔ Φ.Γ.V := inf_le_right
  have hyb_eq : Φ.Γ.ycoord b =
      coord_mul Φ.Γ (Φ.Γ.slope ((Φ.Γ.O ⊔ b) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V))) (Φ.Γ.xproj b) :=
    (Φ.Γ.le_origin_line_iff hd_atom hd_m hd_ne_V hb_atom hb_π hb_aff
      Φ.R hR hR_π Φ.h_irred).mp hb_le_Od
  have hle := CoordSystem.shproj_le_gauge_sup_e hR hR_π he_VR ht ht_τ ht_σ
    (fun h' => hb_ne_O (hb_def.symm.trans h'))
  rw [hb_def] at hle
  have heq1 := (Φ.Γ.le_line_iff hd_atom hd_m hd_ne_V hν_atom hν_n hν_V
    hs_atom hs_π hs_aff Φ.P Φ.hP_atom Φ.hP_plane Φ.hP_not_l Φ.hP_not_m
    Φ.hP_not_OC Φ.hP_ne_I Φ.hP_ne_O Φ.R hR hR_π Φ.h_irred).mp hle
  have hxeq := CoordSystem.xproj_shproj_e hR hR_π he he_VR he_V ht ht_τ ht_σ
  rw [hb_def] at hxeq
  rw [heq1, hxeq, ← hyb_eq]

/-! ## The y-shear, assembled -/

theorem CoordFrame.ycoord_shproj_e (Φ : CoordFrame L) {e : L}
    (he : IsAtom e) (he_VR : e ≤ Φ.Γ.V ⊔ Φ.R) (he_V : e ≠ Φ.Γ.V) (he_R : e ≠ Φ.R)
    {t : L} (ht : IsAtom t) (ht_τ : t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (ht_σ : ¬ t ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R) :
    Φ.Γ.ycoord (Φ.Γ.shproj e t) =
      coord_add Φ.Γ (Φ.Γ.ycoord (Φ.Γ.baseproj Φ.R t))
        (Φ.Γ.ycoord (Φ.Γ.ncoord e (Φ.Γ.zproj Φ.R t))) := by
  have hR := Φ.hR_atom
  have hR_π := Φ.hR_not
  have hb_atom := CoordSystem.baseproj_is_atom hR hR_π ht ht_τ ht_σ
  have hb_π := Φ.Γ.baseproj_le_π Φ.R t
  have hb_aff := CoordSystem.baseproj_affine hR hR_π ht ht_τ ht_σ
  have hz_atom := CoordSystem.zproj_is_atom hR hR_π ht ht_τ ht_σ
  have hz_ζ := Φ.Γ.zproj_le_ζ Φ.R t
  have hz_R := CoordSystem.zproj_ne_R hR_π ht ht_σ
  have hν_atom := CoordSystem.ncoord_is_atom hR hR_π he he_VR he_V he_R
    hz_atom hz_ζ
  have hν_n := Φ.Γ.ncoord_le_n e (Φ.Γ.zproj Φ.R t)
  have hν_V := CoordSystem.ncoord_ne_V hR hR_π he he_VR he_V he_R
    hz_atom hz_ζ hz_R
  have hν_π : Φ.Γ.ncoord e (Φ.Γ.zproj Φ.R t) ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V :=
    hν_n.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hν_aff := Φ.Γ.affine_of_on_n hν_atom hν_n hν_V
  have hy_atom := Φ.Γ.ycoord_is_atom hν_atom hν_π hν_aff
  have hy_l := Φ.Γ.ycoord_le_l (Φ.Γ.ncoord e (Φ.Γ.zproj Φ.R t))
  have hy_U := Φ.Γ.ycoord_ne_U hν_atom hν_π hν_aff
  by_cases hbO : Φ.Γ.baseproj Φ.R t = Φ.Γ.O
  · have ht_ζ : t ≤ Φ.Γ.O ⊔ Φ.R := by
      have h1 : t ≤ Φ.Γ.baseproj Φ.R t ⊔ Φ.R :=
        le_sup_left.trans (CoordSystem.sup_R_baseproj hR hR_π ht ht_τ ht_σ).le
      rwa [hbO] at h1
    have ht_R : t ≠ Φ.R := CoordSystem.ne_R_of_off_σ ht_σ
    have hzt : Φ.Γ.zproj Φ.R t = t :=
      CoordSystem.zproj_of_on_ζ hR hR_π ht ht_ζ ht_R
    rw [hzt] at hy_atom hy_l hy_U
    rw [CoordSystem.shproj_e_eq_ncoord hR hR_π he_VR ht_ζ, hzt, hbO,
      Φ.Γ.ycoord_of_on_l Φ.Γ.hO le_sup_left Φ.Γ.hOU]
    exact (coord_add_left_zero Φ.Γ _ hy_atom hy_l hy_U).symm
  · by_cases hbl : Φ.Γ.baseproj Φ.R t ≤ Φ.Γ.O ⊔ Φ.Γ.U
    · have he_σ : e ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := he_VR.trans (Φ.Γ.VR_le_σ Φ.R)
      have he_π := CoordSystem.he_not_π hR hR_π he he_VR he_V
      have hs_atom := CoordSystem.shproj_is_atom hR hR_π he he_σ he_π ht ht_τ ht_σ
      have hs_π := Φ.Γ.shproj_le_π e t
      have hs_aff := CoordSystem.shproj_affine hR hR_π he he_σ he_π ht ht_τ ht_σ
      have hO_ne_b : Φ.Γ.O ≠ Φ.Γ.baseproj Φ.R t := fun h => hbO h.symm
      have h_line : Φ.Γ.O ⊔ Φ.Γ.U = Φ.Γ.O ⊔ Φ.Γ.baseproj Φ.R t :=
        line_eq_of_atom_le' Φ.Γ.hO Φ.Γ.hU hb_atom Φ.Γ.hOU hO_ne_b hbl
      have hd_U : (Φ.Γ.O ⊔ Φ.Γ.baseproj Φ.R t) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) = Φ.Γ.U := by
        rw [← h_line]
        exact line_direction (m := Φ.Γ.U ⊔ Φ.Γ.V) Φ.Γ.hO Φ.Γ.hO_not_m le_sup_left
      have hle := CoordSystem.shproj_le_gauge_sup_e hR hR_π he_VR ht ht_τ ht_σ hbO
      rw [hd_U] at hle
      have hys := (Φ.Γ.le_horizontal_iff hs_atom hs_π hs_aff hν_atom hν_π
        hν_aff).mp hle
      rw [hys, Φ.Γ.ycoord_of_on_l hb_atom hbl (Φ.Γ.ne_U_of_affine hb_aff)]
      exact (coord_add_left_zero Φ.Γ _ hy_atom hy_l hy_U).symm
    · by_cases hbn : Φ.Γ.baseproj Φ.R t ≤ Φ.Γ.O ⊔ Φ.Γ.V
      · obtain ⟨b', hb'_atom, hb'_le, hb'_ne_b, hb'_ne_U, _⟩ :=
          third_atom_on_line hb_atom Φ.Γ.hU (Φ.Γ.ne_U_of_affine hb_aff) Φ.h_irred
        have hb'_π : b' ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V :=
          hb'_le.trans (sup_le hb_π (le_sup_right.trans le_sup_left))
        have hb'_not_m : ¬ b' ≤ Φ.Γ.U ⊔ Φ.Γ.V := by
          intro h
          have h1 : b' ≤ (Φ.Γ.baseproj Φ.R t ⊔ Φ.Γ.U) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) :=
            le_inf hb'_le h
          rw [line_direction (m := Φ.Γ.U ⊔ Φ.Γ.V) hb_atom hb_aff le_sup_left]
            at h1
          exact hb'_ne_U (IsAtom.eq_of_le hb'_atom Φ.Γ.hU h1)
        have hU_n_bot : Φ.Γ.U ⊓ (Φ.Γ.O ⊔ Φ.Γ.V) = ⊥ :=
          (Φ.Γ.hU.le_iff.mp inf_le_left).resolve_right
            (fun h => Φ.Γ.hU_not_n (le_of_eq_of_le h.symm inf_le_right))
        have hb'_not_n : ¬ b' ≤ Φ.Γ.O ⊔ Φ.Γ.V := by
          intro h
          have h2 : (Φ.Γ.baseproj Φ.R t ⊔ Φ.Γ.U) ⊓ (Φ.Γ.O ⊔ Φ.Γ.V) =
              Φ.Γ.baseproj Φ.R t := by
            rw [sup_inf_assoc_of_le Φ.Γ.U hbn, hU_n_bot, sup_bot_eq]
          exact hb'_ne_b (IsAtom.eq_of_le hb'_atom hb_atom
            (le_of_le_of_eq (le_inf hb'_le h) h2))
        have hb_l_bot : Φ.Γ.baseproj Φ.R t ⊓ (Φ.Γ.O ⊔ Φ.Γ.U) = ⊥ :=
          (hb_atom.le_iff.mp inf_le_left).resolve_right
            (fun h => hbl (le_of_eq_of_le h.symm inf_le_right))
        have hb'_not_l : ¬ b' ≤ Φ.Γ.O ⊔ Φ.Γ.U := by
          intro h
          have h2 : (Φ.Γ.baseproj Φ.R t ⊔ Φ.Γ.U) ⊓ (Φ.Γ.O ⊔ Φ.Γ.U) = Φ.Γ.U := by
            rw [sup_comm (Φ.Γ.baseproj Φ.R t) Φ.Γ.U,
              sup_inf_assoc_of_le (Φ.Γ.baseproj Φ.R t)
                (le_sup_right : Φ.Γ.U ≤ Φ.Γ.O ⊔ Φ.Γ.U),
              hb_l_bot, sup_bot_eq]
          exact hb'_ne_U (IsAtom.eq_of_le hb'_atom Φ.Γ.hU
            (le_of_le_of_eq (le_inf hb'_le h) h2))
        have hb'_ne_O : b' ≠ Φ.Γ.O :=
          fun h => hb'_not_l (le_of_eq_of_le h le_sup_left)
        have hz_σ := CoordSystem.ζ_affine_off_σ hR hR_π hz_atom hz_ζ hz_R
        have ht'_atom := CoordSystem.spoint_is_atom hR hR_π hb'_atom hb'_π
          hz_atom hz_ζ hz_R
        have ht'_τ : Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t) ≤
            Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := CoordSystem.spoint_le_τ hb'_π
        have ht'_σ := CoordSystem.spoint_off_σ hR hR_π hb'_atom hb'_π hb'_not_m
          hz_atom hz_ζ hz_R
        have ht'_base := CoordSystem.baseproj_spoint hR hR_π hb'_atom hb'_π
          hz_atom hz_ζ hz_R
        have ht'_z := CoordSystem.zproj_spoint hR hR_π hb'_atom hb'_π hb'_not_m
          hz_atom hz_ζ hz_R
        have hL1 : Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t) ≤ t ⊔ Φ.Γ.U := by
          have ht_zm : t ≤ Φ.Γ.zproj Φ.R t ⊔ (Φ.Γ.U ⊔ Φ.Γ.V) :=
            le_sup_left.trans (CoordSystem.sup_m_zproj hR hR_π ht ht_τ ht_σ).le
          have h1 : Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t) ≤
              (Φ.Γ.U ⊔ (t ⊔ Φ.R)) ⊓ (Φ.Γ.zproj Φ.R t ⊔ (Φ.Γ.U ⊔ Φ.Γ.V)) := by
            refine le_inf ?_ inf_le_right
            have h2 : b' ⊔ Φ.R ≤ Φ.Γ.U ⊔ (t ⊔ Φ.R) := by
              refine sup_le ?_ (le_sup_right.trans le_sup_right)
              refine hb'_le.trans (sup_le ?_ le_sup_left)
              exact (inf_le_left : Φ.Γ.baseproj Φ.R t ≤ t ⊔ Φ.R).trans
                le_sup_right
            exact (inf_le_left : Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t) ≤
              b' ⊔ Φ.R).trans h2
          have hR_zm : Φ.R ⊓ (Φ.Γ.zproj Φ.R t ⊔ (Φ.Γ.U ⊔ Φ.Γ.V)) = ⊥ :=
            (hR.le_iff.mp inf_le_left).resolve_right
              (fun h => CoordSystem.hR_not_sup_m hR_π hz_atom hz_σ
                (le_of_eq_of_le h.symm inf_le_right))
          have htR_zm : (t ⊔ Φ.R) ⊓ (Φ.Γ.zproj Φ.R t ⊔ (Φ.Γ.U ⊔ Φ.Γ.V)) = t := by
            rw [sup_inf_assoc_of_le Φ.R ht_zm, hR_zm, sup_bot_eq]
          have hU_zm : Φ.Γ.U ≤ Φ.Γ.zproj Φ.R t ⊔ (Φ.Γ.U ⊔ Φ.Γ.V) :=
            le_sup_left.trans le_sup_right
          rw [sup_inf_assoc_of_le (t ⊔ Φ.R) hU_zm, htR_zm,
            sup_comm Φ.Γ.U t] at h1
          exact h1
        have he_σ : e ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := he_VR.trans (Φ.Γ.VR_le_σ Φ.R)
        have he_π := CoordSystem.he_not_π hR hR_π he he_VR he_V
        have hs_atom := CoordSystem.shproj_is_atom hR hR_π he he_σ he_π
          ht ht_τ ht_σ
        have hs_π := Φ.Γ.shproj_le_π e t
        have hs_aff := CoordSystem.shproj_affine hR hR_π he he_σ he_π ht ht_τ ht_σ
        have hs'_atom := CoordSystem.shproj_is_atom hR hR_π he he_σ he_π
          ht'_atom ht'_τ ht'_σ
        have hs'_π := Φ.Γ.shproj_le_π e (Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t))
        have hs'_aff := CoordSystem.shproj_affine hR hR_π he he_σ he_π
          ht'_atom ht'_τ ht'_σ
        have hsh' : Φ.Γ.shproj e (Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t)) ≤
            Φ.Γ.shproj e t ⊔ Φ.Γ.U := by
          have h1 : Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t) ⊔ e ≤
              Φ.Γ.U ⊔ (t ⊔ e) := by
            refine sup_le (hL1.trans ?_) (le_sup_right.trans le_sup_right)
            exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
          have h2 : Φ.Γ.shproj e (Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t)) ≤
              (Φ.Γ.U ⊔ (t ⊔ e)) ⊓ (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) :=
            le_inf (inf_le_left.trans h1) inf_le_right
          rw [sup_inf_assoc_of_le (t ⊔ e)
            (le_sup_right.trans le_sup_left :
              Φ.Γ.U ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)] at h2
          exact h2.trans (sup_comm _ _).le
        have hyeq : Φ.Γ.ycoord (Φ.Γ.shproj e
            (Φ.Γ.spoint Φ.R b' (Φ.Γ.zproj Φ.R t))) =
            Φ.Γ.ycoord (Φ.Γ.shproj e t) :=
          (Φ.Γ.le_horizontal_iff hs'_atom hs'_π hs'_aff hs_atom hs_π hs_aff).mp
            hsh'
        have hyb' : Φ.Γ.ycoord b' = Φ.Γ.ycoord (Φ.Γ.baseproj Φ.R t) :=
          (Φ.Γ.le_horizontal_iff hb'_atom hb'_π hb'_not_m hb_atom hb_π
            hb_aff).mp hb'_le
        have hmain := CoordFrame.ycoord_shproj_e_of_base Φ he he_VR he_V he_R
          ht'_atom ht'_τ ht'_σ ht'_base hb'_ne_O hb'_not_l hb'_not_n
        rw [ht'_z, hyeq, hyb'] at hmain
        exact hmain
      · exact CoordFrame.ycoord_shproj_e_of_base Φ he he_VR he_V he_R
          ht ht_τ ht_σ rfl hbO hbl hbn

/-! ## The gauge bridge: the two gauges reconcile through one slope -/

theorem CoordFrame.gauge_bridge (Φ : CoordFrame L) {c e : L}
    (hc : IsAtom c) (hc_UR : c ≤ Φ.Γ.U ⊔ Φ.R) (hc_U : c ≠ Φ.Γ.U) (hc_R : c ≠ Φ.R)
    (he : IsAtom e) (he_VR : e ≤ Φ.Γ.V ⊔ Φ.R) (he_V : e ≠ Φ.Γ.V) (he_R : e ≠ Φ.R)
    {z : L} (hz : IsAtom z) (hz_ζ : z ≤ Φ.Γ.O ⊔ Φ.R) (hz_R : z ≠ Φ.R) :
    coord_add Φ.Γ
      (coord_mul Φ.Γ (Φ.Γ.slope ((e ⊔ c) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)))
        (Φ.Γ.zcoord c z))
      (Φ.Γ.ycoord (Φ.Γ.ncoord e z)) = Φ.Γ.O := by
  have hR := Φ.hR_atom
  have hR_π := Φ.hR_not
  have he_ne_c : e ≠ c := by
    intro h
    apply hc_R
    exact IsAtom.eq_of_le hc hR (le_of_le_of_eq (le_inf hc_UR (h ▸ he_VR))
      (CoordSystem.UR_inf_VR hR hR_π))
  have hec_σ : e ⊔ c ≤ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R :=
    sup_le (he_VR.trans (Φ.Γ.VR_le_σ Φ.R)) (hc_UR.trans (Φ.Γ.UR_le_σ Φ.R))
  have he_not_m := CoordSystem.e_not_m hR hR_π he he_VR he_V
  have hm_cov : Φ.Γ.U ⊔ Φ.Γ.V ⋖ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := by
    have h := CoordSystem.m_covBy_sup hR (CoordSystem.hR_not_m hR_π)
    rwa [sup_comm Φ.R (Φ.Γ.U ⊔ Φ.Γ.V)] at h
  have hd_atom : IsAtom ((e ⊔ c) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) :=
    trace_atom he hc he_ne_c hm_cov hec_σ
      (fun h => he_not_m (le_sup_left.trans h))
  have hd_m : (e ⊔ c) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) ≤ Φ.Γ.U ⊔ Φ.Γ.V := inf_le_right
  have hd_ec : (e ⊔ c) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) ≤ e ⊔ c := inf_le_left
  have hd_ne_U : (e ⊔ c) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) ≠ Φ.Γ.U := by
    intro h
    have hU_le : Φ.Γ.U ≤ e ⊔ c := le_of_eq_of_le h.symm inf_le_left
    have h_line : c ⊔ e = c ⊔ Φ.Γ.U :=
      line_eq_of_atom_le' hc he Φ.Γ.hU (Ne.symm he_ne_c) hc_U
        (hU_le.trans (sup_comm e c).le)
    have he_le : e ≤ Φ.Γ.U ⊔ Φ.R := by
      calc e ≤ c ⊔ e := le_sup_right
        _ = c ⊔ Φ.Γ.U := h_line
        _ = Φ.Γ.U ⊔ c := sup_comm _ _
        _ = Φ.Γ.U ⊔ Φ.R := (CoordSystem.UR_eq_Uc hR hR_π hc hc_UR hc_U hc_R).symm
    exact he_R (IsAtom.eq_of_le he hR
      (le_of_le_of_eq (le_inf he_le he_VR)
        (CoordSystem.UR_inf_VR hR hR_π)))
  have hd_ne_V : (e ⊔ c) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) ≠ Φ.Γ.V := by
    intro h
    have hV_le : Φ.Γ.V ≤ e ⊔ c := le_of_eq_of_le h.symm inf_le_left
    have h_line : e ⊔ c = e ⊔ Φ.Γ.V :=
      line_eq_of_atom_le' he hc Φ.Γ.hV he_ne_c he_V hV_le
    have hc_le : c ≤ Φ.Γ.V ⊔ Φ.R := by
      calc c ≤ e ⊔ c := le_sup_right
        _ = e ⊔ Φ.Γ.V := h_line
        _ = Φ.Γ.V ⊔ e := sup_comm _ _
        _ = Φ.Γ.V ⊔ Φ.R := (CoordSystem.VR_eq_Ve hR hR_π he he_VR he_V he_R).symm
    exact hc_R (IsAtom.eq_of_le hc hR
      (le_of_le_of_eq (le_inf hc_UR hc_le)
        (CoordSystem.UR_inf_VR hR hR_π)))
  have hν_atom := CoordSystem.ncoord_is_atom hR hR_π he he_VR he_V he_R hz hz_ζ
  have hν_n := Φ.Γ.ncoord_le_n e z
  have hν_V := CoordSystem.ncoord_ne_V hR hR_π he he_VR he_V he_R hz hz_ζ hz_R
  have hx_atom := CoordSystem.zcoord_is_atom hR hR_π hc hc_UR hc_U hc_R hz hz_ζ
  have hx_l := Φ.Γ.zcoord_le_l c z
  have hx_U := CoordSystem.zcoord_ne_U hR hR_π hc hc_UR hc_U hc_R hz hz_ζ hz_R
  have hx_aff := Φ.Γ.affine_of_on_l hx_atom hx_l hx_U
  have hx_π : Φ.Γ.zcoord c z ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V := hx_l.trans le_sup_left
  have h_ec_line : e ⊔ c = e ⊔ ((e ⊔ c) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) :=
    line_eq_of_atom_le' he hc hd_atom he_ne_c
      (fun h => he_not_m (le_of_eq_of_le h hd_m)) hd_ec
  have h_theta : z ⊔ (e ⊔ c) =
      ((e ⊔ c) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) ⊔ (z ⊔ e) := by
    apply le_antisymm
    · refine sup_le (le_sup_left.trans le_sup_right) (h_ec_line.le.trans ?_)
      exact sup_le (le_sup_right.trans le_sup_right) le_sup_left
    · exact sup_le (hd_ec.trans le_sup_right)
        (sup_le le_sup_left (le_sup_left.trans le_sup_right))
  have h_ze_π : (z ⊔ e) ⊓ (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) = Φ.Γ.ncoord e z := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      have h3 : z ⊔ e ≤ (Φ.Γ.O ⊔ Φ.Γ.V) ⊔ Φ.R :=
        sup_le (hz_ζ.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
          (he_VR.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
      calc (z ⊔ e) ⊓ (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) ≤
            ((Φ.Γ.O ⊔ Φ.Γ.V) ⊔ Φ.R) ⊓ (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) :=
          inf_le_inf_right _ h3
        _ = Φ.Γ.O ⊔ Φ.Γ.V := by
            rw [sup_inf_assoc_of_le Φ.R
                (sup_le (le_sup_left.trans le_sup_left) le_sup_right :
                  Φ.Γ.O ⊔ Φ.Γ.V ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V),
              CoordSystem.R_inf_π hR hR_π, sup_bot_eq]
    · exact le_inf inf_le_left (inf_le_right.trans
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  have hx_le : Φ.Γ.zcoord c z ≤
      Φ.Γ.ncoord e z ⊔ ((e ⊔ c) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V)) := by
    have h1 : Φ.Γ.zcoord c z ≤ (z ⊔ (e ⊔ c)) ⊓ (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) := by
      refine le_inf (inf_le_left.trans ?_) (hx_l.trans le_sup_left)
      exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
    rw [h_theta, sup_inf_assoc_of_le (z ⊔ e) (hd_m.trans Φ.Γ.m_le_π),
      h_ze_π] at h1
    exact h1.trans (sup_comm _ _).le
  have heq := (Φ.Γ.le_line_iff hd_atom hd_m hd_ne_V hν_atom hν_n hν_V
    hx_atom hx_π hx_aff Φ.P Φ.hP_atom Φ.hP_plane Φ.hP_not_l Φ.hP_not_m
    Φ.hP_not_OC Φ.hP_ne_I Φ.hP_ne_O Φ.R hR hR_π Φ.h_irred).mp hx_le
  rw [Φ.Γ.ycoord_of_on_l hx_atom hx_l hx_U,
    Φ.Γ.xproj_of_on_l hx_atom hx_l hx_U] at heq
  exact heq.symm

end Foam.Bridges

/-- info: 'Foam.Bridges.CoordSystem.UR_inf_π' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.UR_inf_π

/-- info: 'Foam.Bridges.CoordSystem.VR_inf_π' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.VR_inf_π

/-- info: 'Foam.Bridges.CoordSystem.n_inf_VR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.n_inf_VR

/-- info: 'Foam.Bridges.CoordSystem.ζ_inf_VR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ζ_inf_VR

/-- info: 'Foam.Bridges.CoordSystem.UR_inf_VR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.UR_inf_VR

/-- info: 'Foam.Bridges.CoordSystem.m_inf_VR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.m_inf_VR

/-- info: 'Foam.Bridges.CoordSystem.ζ_sup_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ζ_sup_e

/-- info: 'Foam.Bridges.CoordSystem.ncoord_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ncoord_is_atom

/-- info: 'Foam.Bridges.CoordSystem.ncoord_ne_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ncoord_ne_V

/-- info: 'Foam.Bridges.CoordSystem.ncoord_O' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ncoord_O

/-- info: 'Foam.Bridges.CoordSystem.ncoord_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ncoord_R

/-- info: 'Foam.Bridges.CoordSystem.shproj_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.shproj_is_atom

/-- info: 'Foam.Bridges.CoordSystem.sup_center_shproj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.sup_center_shproj

/-- info: 'Foam.Bridges.CoordSystem.shproj_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.shproj_affine

/-- info: 'Foam.Bridges.CoordSystem.shproj_le_base_sup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.shproj_le_base_sup

/-- info: 'Foam.Bridges.CoordSystem.ycoord_shproj_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ycoord_shproj_c

/-- info: 'Foam.Bridges.CoordSystem.xproj_shproj_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.xproj_shproj_e

/-- info: 'Foam.Bridges.CoordSystem.le_zproj_sup_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.le_zproj_sup_dir

/-- info: 'Foam.Bridges.CoordSystem.shproj_le_gauge_sup_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.shproj_le_gauge_sup_c

/-- info: 'Foam.Bridges.CoordSystem.shproj_le_gauge_sup_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.shproj_le_gauge_sup_e

/-- info: 'Foam.Bridges.CoordSystem.shproj_c_eq_zcoord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.shproj_c_eq_zcoord

/-- info: 'Foam.Bridges.CoordSystem.shproj_e_eq_ncoord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.shproj_e_eq_ncoord

/-- info: 'Foam.Bridges.CoordSystem.base_dir_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.base_dir_facts

/-- info: 'Foam.Bridges.CoordFrame.affine_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.affine_solve

/-- info: 'Foam.Bridges.CoordFrame.xproj_shproj_c_of_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.xproj_shproj_c_of_base

/-- info: 'Foam.Bridges.CoordFrame.xproj_shproj_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.xproj_shproj_c

/-- info: 'Foam.Bridges.CoordFrame.ycoord_shproj_e_of_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.ycoord_shproj_e_of_base

/-- info: 'Foam.Bridges.CoordFrame.ycoord_shproj_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.ycoord_shproj_e

/-- info: 'Foam.Bridges.CoordFrame.gauge_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.gauge_bridge
