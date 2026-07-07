import Bridges.FTPG.Chart

/-!
# The ordinate transport — camp two of the `pointSystem_exists` ascent, second pitch

`Chart.lean` split the affine plane as `Coordinate Γ × Ordinate Γ`; this
pitch seats the second factor on the division ring.  The with-the-grain
route — model-verified over `PG(2,q)`, `q = 3,5,7,11,13`, 72 frames,
before carving — is not the naive drop onto the axis `O ⊔ V` but the
**diagonal route**, the same two moves `coord_mul` already makes:

* `diagproj p = (p ⊔ U) ⊓ (O ⊔ C)` — the horizontal transport onto the
  diagonal `O ⊔ C` (the multiplication's auxiliary axis);
* `ycoord p = (diagproj p ⊔ E_I) ⊓ l` — the `E_I`-transport down to the
  coordinate line (`E_I
`-lift is `coord_mul`'s own "seat `b` on the
  diagonal as `b·C`" move, read backwards);
* `diagseat` / `yseat` — the same two perspectivities in reverse, the
  inverse transport.

Both centers' side conditions were already sealed in `Mul.lean`
(`hE_I_not_l`, `hE_I_not_OC`), so the transport is degeneracy-free for
*every* legal frame — no appeal to `h_irred`, no case on `C`'s position.
`perspect_roundtrip` closes both composites, giving
`ordinateTransport : Ordinate Γ ≃ Coordinate Γ` and hence
`planeChart : Affine Γ ≃ Coordinate Γ × Coordinate Γ` — the affine plane
is `D²`, at atom level.  The calibration receipts: the coordinate axis
is the graph of zero (`ycoord_of_on_l`), and the unit point sits at
height one (`ycoord_C : ycoord C = I`).

Next pitch: the line equation — collinearity in `π` against the
algebra's `coord_add`/`coord_mul` (`y = a·x + b`), the statement the
`PG(2,q)` probe already confirmed at this chart.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

variable {Γ : CoordSystem L}

theorem CoordSystem.hOC : Γ.O ≠ Γ.C :=
  fun h => Γ.hC_not_l (h ▸ le_sup_left)

theorem CoordSystem.hUC : Γ.U ≠ Γ.C :=
  fun h => Γ.hC_not_l (h ▸ le_sup_right)

theorem CoordSystem.hE_I_ne_U : Γ.E_I ≠ Γ.U :=
  fun h => Γ.hE_I_not_l (h ▸ le_sup_right)

theorem CoordSystem.hO_ne_E_I : Γ.O ≠ Γ.E_I :=
  fun h => Γ.hO_not_m (h ▸ Γ.hE_I_on_m)

theorem CoordSystem.l_inf_OC_eq_O : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
  modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU Γ.hOC Γ.hUC Γ.hC_not_l

theorem CoordSystem.hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := fun h =>
  Γ.hOU (IsAtom.eq_of_le Γ.hU Γ.hO
    (le_of_le_of_eq (le_inf le_sup_right h) Γ.l_inf_OC_eq_O)).symm

theorem CoordSystem.m_le_π : Γ.U ⊔ Γ.V ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
  sup_le ((le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U).trans le_sup_left) le_sup_right

theorem CoordSystem.OC_le_π : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
  sup_le (le_sup_left.trans le_sup_left) Γ.hC_plane

theorem CoordSystem.l_covBy_π : (Γ.O ⊔ Γ.U) ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V :=
  line_covBy_plane Γ.hO Γ.hU Γ.hV Γ.hOU Γ.hOV Γ.hUV Γ.hV_off

theorem CoordSystem.l_sup_C_eq_π : Γ.O ⊔ Γ.U ⊔ Γ.C = Γ.O ⊔ Γ.U ⊔ Γ.V := by
  have h_lt : Γ.O ⊔ Γ.U < Γ.O ⊔ Γ.U ⊔ Γ.C := lt_of_le_of_ne le_sup_left
    (fun h => Γ.hC_not_l (h ▸ le_sup_right))
  exact (Γ.l_covBy_π.eq_or_eq h_lt.le
    (sup_le le_sup_left Γ.hC_plane)).resolve_left (ne_of_gt h_lt)

theorem CoordSystem.l_sup_E_I_eq_π : Γ.O ⊔ Γ.U ⊔ Γ.E_I = Γ.O ⊔ Γ.U ⊔ Γ.V := by
  have h_lt : Γ.O ⊔ Γ.U < Γ.O ⊔ Γ.U ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
    (fun h => Γ.hE_I_not_l (h ▸ le_sup_right))
  exact (Γ.l_covBy_π.eq_or_eq h_lt.le
    (sup_le le_sup_left (Γ.hE_I_on_m.trans Γ.m_le_π))).resolve_left (ne_of_gt h_lt)

theorem CoordSystem.OC_sup_U_eq_π : Γ.O ⊔ Γ.C ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V := by
  rw [sup_right_comm]
  exact Γ.l_sup_C_eq_π

theorem CoordSystem.n_sup_U_eq_π : Γ.O ⊔ Γ.V ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V :=
  sup_right_comm Γ.O Γ.V Γ.U

theorem CoordSystem.OC_sup_E_I_eq_π : Γ.O ⊔ Γ.C ⊔ Γ.E_I = Γ.O ⊔ Γ.U ⊔ Γ.V := by
  have h_lt : Γ.O ⊔ Γ.C < Γ.O ⊔ Γ.C ⊔ Γ.E_I := lt_of_le_of_ne le_sup_left
    (fun h => Γ.hE_I_not_OC (h ▸ le_sup_right))
  exact (Γ.OC_covBy_π.eq_or_eq h_lt.le
    (sup_le Γ.OC_le_π (Γ.hE_I_on_m.trans Γ.m_le_π))).resolve_left (ne_of_gt h_lt)

def CoordSystem.diagproj (Γ : CoordSystem L) (p : L) : L :=
  (p ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C)

noncomputable def CoordSystem.diagseat (Γ : CoordSystem L) (x : L) : L :=
  (x ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C)

noncomputable def CoordSystem.ycoord (Γ : CoordSystem L) (p : L) : L :=
  (Γ.diagproj p ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U)

noncomputable def CoordSystem.yseat (Γ : CoordSystem L) (x : L) : L :=
  (Γ.diagseat x ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.V)

theorem CoordSystem.diagproj_of_on_OC {p : L} (hp : IsAtom p)
    (hp_oc : p ≤ Γ.O ⊔ Γ.C) (hp_ne_U : p ≠ Γ.U) : Γ.diagproj p = p :=
  perspect_fixes_intersection Γ.hU hp hp_ne_U Γ.hO Γ.hC Γ.hOC Γ.hU_not_OC
    hp_oc hp_oc (sup_le (hp_oc.trans le_sup_left) le_sup_right)

theorem CoordSystem.diagproj_is_atom {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_ne_U : p ≠ Γ.U) :
    IsAtom (Γ.diagproj p) := by
  by_cases hp_oc : p ≤ Γ.O ⊔ Γ.C
  · rw [Γ.diagproj_of_on_OC hp hp_oc hp_ne_U]
    exact hp
  · exact perspect_atom Γ.hU hp hp_ne_U Γ.hO Γ.hC Γ.hOC Γ.hU_not_OC
      (by rw [Γ.OC_sup_U_eq_π]
          exact sup_le hp_π ((le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U).trans le_sup_left))

theorem CoordSystem.diagproj_ne_E {p : L} (hp : IsAtom p) (hp_aff : ¬ p ≤ Γ.m) :
    Γ.diagproj p ≠ Γ.E := by
  intro h
  apply hp_aff
  have hE_le : Γ.E ≤ p ⊔ Γ.U := h ▸ (inf_le_left : Γ.diagproj p ≤ p ⊔ Γ.U)
  have h_line : Γ.U ⊔ p = Γ.U ⊔ Γ.E :=
    line_eq_of_atom_le' Γ.hU hp Γ.hE_atom (Γ.ne_U_of_affine hp_aff).symm Γ.hEU.symm
      (by rwa [sup_comm] at hE_le)
  calc p ≤ Γ.U ⊔ p := le_sup_right
    _ = Γ.U ⊔ Γ.E := h_line
    _ = Γ.E ⊔ Γ.U := sup_comm _ _
    _ = Γ.m := Γ.EU_eq_m

theorem CoordSystem.ycoord_is_atom {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.m) :
    IsAtom (Γ.ycoord p) := by
  have hdp_atom := Γ.diagproj_is_atom hp hp_π (Γ.ne_U_of_affine hp_aff)
  have hdp_ne_EI : Γ.diagproj p ≠ Γ.E_I :=
    fun h => Γ.hE_I_not_OC (h ▸ (inf_le_right : Γ.diagproj p ≤ Γ.O ⊔ Γ.C))
  exact perspect_atom Γ.hE_I_atom hdp_atom hdp_ne_EI Γ.hO Γ.hU Γ.hOU Γ.hE_I_not_l
    (by rw [Γ.l_sup_E_I_eq_π]
        exact sup_le ((inf_le_right : Γ.diagproj p ≤ Γ.O ⊔ Γ.C).trans Γ.OC_le_π)
          (Γ.hE_I_on_m.trans Γ.m_le_π))

theorem CoordSystem.ycoord_le_l (Γ : CoordSystem L) (p : L) :
    Γ.ycoord p ≤ Γ.O ⊔ Γ.U := inf_le_right

theorem CoordSystem.ycoord_ne_U {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.m) :
    Γ.ycoord p ≠ Γ.U := by
  intro h
  have hdp_atom := Γ.diagproj_is_atom hp hp_π (Γ.ne_U_of_affine hp_aff)
  have hU_le : Γ.U ≤ Γ.diagproj p ⊔ Γ.E_I :=
    h ▸ (inf_le_left : Γ.ycoord p ≤ Γ.diagproj p ⊔ Γ.E_I)
  have hEI_ne_dp : Γ.E_I ≠ Γ.diagproj p :=
    fun h' => Γ.hE_I_not_OC (h' ▸ (inf_le_right : Γ.diagproj p ≤ Γ.O ⊔ Γ.C))
  have h_line : Γ.E_I ⊔ Γ.diagproj p = Γ.E_I ⊔ Γ.U :=
    line_eq_of_atom_le' Γ.hE_I_atom hdp_atom Γ.hU hEI_ne_dp Γ.hE_I_ne_U
      (by rwa [sup_comm] at hU_le)
  have hdp_le_m : Γ.diagproj p ≤ Γ.m :=
    (le_sup_right.trans h_line.le).trans (sup_le Γ.hE_I_on_m Γ.hU_on_m)
  exact Γ.diagproj_ne_E hp hp_aff (IsAtom.eq_of_le hdp_atom Γ.hE_atom
    (le_inf (inf_le_right : Γ.diagproj p ≤ Γ.O ⊔ Γ.C) hdp_le_m : Γ.diagproj p ≤ Γ.E))

theorem CoordSystem.diagseat_is_atom {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (_hx_ne : x ≠ Γ.U) : IsAtom (Γ.diagseat x) := by
  have hx_ne_EI : x ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hx_l)
  exact perspect_atom Γ.hE_I_atom hx hx_ne_EI Γ.hO Γ.hC Γ.hOC Γ.hE_I_not_OC
    (by rw [Γ.OC_sup_E_I_eq_π]
        exact sup_le (hx_l.trans le_sup_left) (Γ.hE_I_on_m.trans Γ.m_le_π))

theorem CoordSystem.diagseat_ne_E {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) : Γ.diagseat x ≠ Γ.E := by
  intro h
  have hE_le : Γ.E ≤ x ⊔ Γ.E_I := h ▸ (inf_le_left : Γ.diagseat x ≤ x ⊔ Γ.E_I)
  have hEI_ne_x : Γ.E_I ≠ x := fun h' => Γ.hE_I_not_l (h' ▸ hx_l)
  have h_line : Γ.E_I ⊔ x = Γ.E_I ⊔ Γ.E :=
    line_eq_of_atom_le' Γ.hE_I_atom hx Γ.hE_atom hEI_ne_x Γ.hE_I_ne_E
      (by rwa [sup_comm] at hE_le)
  have hx_le_m : x ≤ Γ.m :=
    (le_sup_right.trans h_line.le).trans (sup_le Γ.hE_I_on_m Γ.hE_on_m)
  exact hx_ne (Γ.atom_on_both_eq_U hx hx_l hx_le_m)

theorem CoordSystem.yseat_is_atom {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) : IsAtom (Γ.yseat x) := by
  have hds_atom := Γ.diagseat_is_atom hx hx_l hx_ne
  have hds_ne_U : Γ.diagseat x ≠ Γ.U :=
    fun h => Γ.hU_not_OC (h ▸ (inf_le_right : Γ.diagseat x ≤ Γ.O ⊔ Γ.C))
  exact perspect_atom Γ.hU hds_atom hds_ne_U Γ.hO Γ.hV Γ.hOV Γ.hU_not_n
    (by rw [Γ.n_sup_U_eq_π]
        exact sup_le ((inf_le_right : Γ.diagseat x ≤ Γ.O ⊔ Γ.C).trans Γ.OC_le_π)
          ((le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U).trans le_sup_left))

theorem CoordSystem.yseat_le_n (Γ : CoordSystem L) (x : L) :
    Γ.yseat x ≤ Γ.O ⊔ Γ.V := inf_le_right

theorem CoordSystem.yseat_ne_V {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) : Γ.yseat x ≠ Γ.V := by
  intro h
  have hds_atom := Γ.diagseat_is_atom hx hx_l hx_ne
  have hV_le : Γ.V ≤ Γ.diagseat x ⊔ Γ.U :=
    h ▸ (inf_le_left : Γ.yseat x ≤ Γ.diagseat x ⊔ Γ.U)
  have hU_ne_ds : Γ.U ≠ Γ.diagseat x :=
    fun h' => Γ.hU_not_OC (h' ▸ (inf_le_right : Γ.diagseat x ≤ Γ.O ⊔ Γ.C))
  have h_line : Γ.U ⊔ Γ.diagseat x = Γ.U ⊔ Γ.V :=
    line_eq_of_atom_le' Γ.hU hds_atom Γ.hV hU_ne_ds Γ.hUV
      (by rwa [sup_comm] at hV_le)
  have hds_le_m : Γ.diagseat x ≤ Γ.m := le_sup_right.trans h_line.le
  exact Γ.diagseat_ne_E hx hx_l hx_ne (IsAtom.eq_of_le hds_atom Γ.hE_atom
    (le_inf (inf_le_right : Γ.diagseat x ≤ Γ.O ⊔ Γ.C) hds_le_m : Γ.diagseat x ≤ Γ.E))

theorem CoordSystem.yseat_ycoord {w : L} (hw : IsAtom w)
    (hw_n : w ≤ Γ.O ⊔ Γ.V) (hw_ne : w ≠ Γ.V) : Γ.yseat (Γ.ycoord w) = w := by
  have hw_aff : ¬ w ≤ Γ.m := Γ.affine_of_on_n hw hw_n hw_ne
  have hw_ne_U : w ≠ Γ.U := Γ.ne_U_of_affine hw_aff
  have hw_π : w ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    hw_n.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hdp_atom := Γ.diagproj_is_atom hw hw_π hw_ne_U
  have hdp_ne_EI : Γ.diagproj w ≠ Γ.E_I :=
    fun h => Γ.hE_I_not_OC (h ▸ (inf_le_right : Γ.diagproj w ≤ Γ.O ⊔ Γ.C))
  have h1 : (Γ.ycoord w ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) = Γ.diagproj w :=
    perspect_roundtrip Γ.hE_I_atom hdp_atom hdp_ne_EI Γ.hO Γ.hC Γ.hOC Γ.hO Γ.hU Γ.hOU
      Γ.hE_I_not_OC Γ.hE_I_not_l (Γ.OC_sup_E_I_eq_π.trans Γ.l_sup_E_I_eq_π.symm)
      inf_le_right
  show ((Γ.ycoord w ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.V) = w
  rw [h1]
  exact perspect_roundtrip Γ.hU hw hw_ne_U Γ.hO Γ.hV Γ.hOV Γ.hO Γ.hC Γ.hOC
    Γ.hU_not_n Γ.hU_not_OC (Γ.n_sup_U_eq_π.trans Γ.OC_sup_U_eq_π.symm) hw_n

theorem CoordSystem.ycoord_yseat {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) : Γ.ycoord (Γ.yseat x) = x := by
  have hds_atom := Γ.diagseat_is_atom hx hx_l hx_ne
  have hds_ne_U : Γ.diagseat x ≠ Γ.U :=
    fun h => Γ.hU_not_OC (h ▸ (inf_le_right : Γ.diagseat x ≤ Γ.O ⊔ Γ.C))
  have hx_ne_EI : x ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hx_l)
  have h1 : (Γ.yseat x ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.diagseat x :=
    perspect_roundtrip Γ.hU hds_atom hds_ne_U Γ.hO Γ.hC Γ.hOC Γ.hO Γ.hV Γ.hOV
      Γ.hU_not_OC Γ.hU_not_n (Γ.OC_sup_U_eq_π.trans Γ.n_sup_U_eq_π.symm)
      inf_le_right
  show ((Γ.yseat x ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = x
  rw [h1]
  exact perspect_roundtrip Γ.hE_I_atom hx hx_ne_EI Γ.hO Γ.hU Γ.hOU Γ.hO Γ.hC Γ.hOC
    Γ.hE_I_not_l Γ.hE_I_not_OC (Γ.l_sup_E_I_eq_π.trans Γ.OC_sup_E_I_eq_π.symm) hx_l

theorem CoordSystem.ycoord_yproj {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.m) :
    Γ.ycoord (Γ.yproj p) = Γ.ycoord p := by
  show ((Γ.yproj p ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = Γ.ycoord p
  rw [← Γ.sup_U_yproj hp hp_π hp_aff]
  rfl

theorem CoordSystem.ycoord_of_on_l {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) : Γ.ycoord x = Γ.O := by
  have h_dp : Γ.diagproj x = Γ.O := by
    show (x ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O
    have h_l : x ⊔ Γ.U = Γ.O ⊔ Γ.U := by
      rw [sup_comm x Γ.U, sup_comm Γ.O Γ.U]
      exact (line_eq_of_atom_le' Γ.hU Γ.hO hx Γ.hOU.symm hx_ne.symm
        (by rwa [sup_comm] at hx_l)).symm
    rw [h_l]
    exact Γ.l_inf_OC_eq_O
  show (Γ.diagproj x ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = Γ.O
  rw [h_dp]
  exact modular_intersection Γ.hO Γ.hE_I_atom Γ.hU Γ.hO_ne_E_I Γ.hOU Γ.hE_I_ne_U
    (fun h => Γ.hE_I_not_l ((le_sup_right : Γ.E_I ≤ Γ.O ⊔ Γ.E_I).trans
      (line_eq_of_atom_le' Γ.hO Γ.hE_I_atom Γ.hU Γ.hO_ne_E_I Γ.hOU h).le))

theorem CoordSystem.ycoord_C : Γ.ycoord Γ.C = Γ.I := by
  have h_dp : Γ.diagproj Γ.C = Γ.C :=
    Γ.diagproj_of_on_OC Γ.hC le_sup_right Γ.hUC.symm
  show (Γ.diagproj Γ.C ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = Γ.I
  rw [h_dp]
  have hCI : Γ.C ≠ Γ.I := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hC_ne_EI : Γ.C ≠ Γ.E_I := fun h => Γ.hC_not_m (h ▸ Γ.hE_I_on_m)
  have h_CE : Γ.C ⊔ Γ.E_I = Γ.C ⊔ Γ.I :=
    (line_eq_of_atom_le' Γ.hC Γ.hI Γ.hE_I_atom hCI hC_ne_EI
      (le_of_le_of_eq Γ.hE_I_le_IC (sup_comm Γ.I Γ.C))).symm
  have h_l : Γ.O ⊔ Γ.U = Γ.I ⊔ Γ.U := by
    rw [sup_comm Γ.O Γ.U, sup_comm Γ.I Γ.U]
    exact line_eq_of_atom_le' Γ.hU Γ.hO Γ.hI Γ.hOU.symm Γ.hUI
      (le_of_le_of_eq Γ.hI_on (sup_comm Γ.O Γ.U))
  rw [h_CE, h_l, sup_comm Γ.C Γ.I]
  exact modular_intersection Γ.hI Γ.hC Γ.hU hCI.symm Γ.hUI.symm Γ.hUC.symm
    (fun h => Γ.hE_I_ne_U.symm (IsAtom.eq_of_le Γ.hU Γ.hE_I_atom
      (le_inf h Γ.hU_on_m : Γ.U ≤ Γ.E_I)))

noncomputable def ordinateTransport (Γ : CoordSystem L) :
    Ordinate Γ ≃ Coordinate Γ where
  toFun w :=
    ⟨Γ.ycoord w.1,
      Γ.ycoord_is_atom w.2.1
        (w.2.2.1.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
        (Γ.affine_of_on_n w.2.1 w.2.2.1 w.2.2.2),
      Γ.ycoord_le_l w.1,
      Γ.ycoord_ne_U w.2.1
        (w.2.2.1.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
        (Γ.affine_of_on_n w.2.1 w.2.2.1 w.2.2.2)⟩
  invFun x :=
    ⟨Γ.yseat x.1, Γ.yseat_is_atom x.2.1 x.2.2.1 x.2.2.2, Γ.yseat_le_n x.1,
      Γ.yseat_ne_V x.2.1 x.2.2.1 x.2.2.2⟩
  left_inv w := Subtype.ext (Γ.yseat_ycoord w.2.1 w.2.2.1 w.2.2.2)
  right_inv x := Subtype.ext (Γ.ycoord_yseat x.2.1 x.2.2.1 x.2.2.2)

noncomputable def planeChart (Γ : CoordSystem L) :
    Affine Γ ≃ Coordinate Γ × Coordinate Γ :=
  (affineChart Γ).trans ((Equiv.refl (Coordinate Γ)).prodCongr (ordinateTransport Γ))

end Foam.Bridges

/-- info: 'Foam.Bridges.CoordSystem.diagproj_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.diagproj_is_atom

/-- info: 'Foam.Bridges.CoordSystem.ycoord_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ycoord_is_atom

/-- info: 'Foam.Bridges.CoordSystem.yseat_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.yseat_is_atom

/-- info: 'Foam.Bridges.CoordSystem.yseat_ycoord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.yseat_ycoord

/-- info: 'Foam.Bridges.CoordSystem.ycoord_yseat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ycoord_yseat

/-- info: 'Foam.Bridges.CoordSystem.ycoord_yproj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ycoord_yproj

/-- info: 'Foam.Bridges.CoordSystem.ycoord_of_on_l' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ycoord_of_on_l

/-- info: 'Foam.Bridges.CoordSystem.ycoord_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ycoord_C

/-- info: 'Foam.Bridges.ordinateTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ordinateTransport

/-- info: 'Foam.Bridges.planeChart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.planeChart
