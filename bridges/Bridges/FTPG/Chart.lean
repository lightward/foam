import Bridges.FTPG.Carrier

/-!
# The affine chart — camp two of the `pointSystem_exists` ascent, first pitch

The frame's plane `π = O ⊔ U ⊔ V` carries two pencils of reference lines:
the lines through `V` (the "verticals") and the lines through `U` (the
"horizontals").  An *affine* atom of the plane — one not on the line at
infinity `m = U ⊔ V` — is hit by exactly one line of each pencil, and the
two intersections with the axes are its coordinates:

* `xproj p = (p ⊔ V) ⊓ (O ⊔ U)` — the vertical drop onto the coordinate
  line `l` (an affine point of `l`, i.e. an element of `Coordinate Γ`);
* `yproj p = (p ⊔ U) ⊓ (O ⊔ V)` — the horizontal drop onto the second
  axis `O ⊔ V` (an affine point of it, an `Ordinate Γ`);
* `point x y = (x ⊔ V) ⊓ (y ⊔ U)` — the chart read backwards.

The recovery is one `modular_intersection` after the two line identities
(`chart_recovers`), the backward map is total on affine axis-pairs
(`point_is_atom`, `point_affine`), and each projection inverts the other
(`xproj_point`, `yproj_point`), so the affine plane splits losslessly:
`affineChart : Affine Γ ≃ Coordinate Γ × Ordinate Γ`.

This is the atom-level case of the eventual coordinate vector: the pair
`(x, y)` is `p`'s record, the plane's atoms are exactly the records plus
the line at infinity, and nothing in the middle is missing.  The next
pitch transports `Ordinate Γ` back onto `Coordinate Γ` and meets the
algebra (the line equation `y = a·x + b`); the pitch after glues charts
across basis-supports.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

omit [ComplementedLattice L] [IsAtomistic L] in
theorem line_eq_of_atom_le' {a b c : L}
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (hab : a ≠ b) (hac : a ≠ c) (hc_le : c ≤ a ⊔ b) : a ⊔ b = a ⊔ c := by
  by_cases hbc : b = c
  · rw [hbc]
  · exact line_eq_of_atom_le ha hb hc hab hac hbc hc_le

variable {Γ : CoordSystem L}

theorem CoordSystem.hUV : Γ.U ≠ Γ.V :=
  fun h => Γ.hV_off (h ▸ le_sup_right)

theorem CoordSystem.hOV : Γ.O ≠ Γ.V :=
  fun h => Γ.hV_off (h ▸ le_sup_left)

theorem CoordSystem.l_inf_n_eq_O : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.V) = Γ.O :=
  modular_intersection Γ.hO Γ.hU Γ.hV Γ.hOU Γ.hOV Γ.hUV Γ.hV_off

theorem CoordSystem.hU_not_n : ¬ Γ.U ≤ Γ.O ⊔ Γ.V := fun h =>
  Γ.hOU (IsAtom.eq_of_le Γ.hU Γ.hO
    (le_of_le_of_eq (le_inf le_sup_right h) Γ.l_inf_n_eq_O)).symm

theorem CoordSystem.n_inf_m_eq_V : (Γ.O ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.V) = Γ.V := by
  rw [sup_comm Γ.O Γ.V, sup_comm Γ.U Γ.V]
  exact modular_intersection Γ.hV Γ.hO Γ.hU Γ.hOV.symm Γ.hUV.symm Γ.hOU
    (fun h => Γ.hU_not_n (by rwa [sup_comm] at h))

theorem CoordSystem.ne_U_of_affine {p : L} (hp_aff : ¬ p ≤ Γ.m) : p ≠ Γ.U :=
  fun h => hp_aff (h ▸ Γ.hU_on_m)

theorem CoordSystem.ne_V_of_affine {p : L} (hp_aff : ¬ p ≤ Γ.m) : p ≠ Γ.V :=
  fun h => hp_aff (h ▸ (le_sup_right : Γ.V ≤ Γ.m))

theorem CoordSystem.affine_of_on_l {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) : ¬ x ≤ Γ.m :=
  fun h => hx_ne (Γ.atom_on_both_eq_U hx hx_l h)

theorem CoordSystem.affine_of_on_n {y : L} (hy : IsAtom y)
    (hy_n : y ≤ Γ.O ⊔ Γ.V) (hy_ne : y ≠ Γ.V) : ¬ y ≤ Γ.m :=
  fun h => hy_ne (IsAtom.eq_of_le hy Γ.hV
    (le_of_le_of_eq (le_inf hy_n h) Γ.n_inf_m_eq_V))

theorem CoordSystem.U_not_le_sup_V {p : L} (hp : IsAtom p) (hp_aff : ¬ p ≤ Γ.m) :
    ¬ Γ.U ≤ p ⊔ Γ.V := by
  intro h
  apply hp_aff
  have h_line : Γ.V ⊔ p = Γ.V ⊔ Γ.U :=
    line_eq_of_atom_le' Γ.hV hp Γ.hU (Γ.ne_V_of_affine hp_aff).symm Γ.hUV.symm
      (by rwa [sup_comm] at h)
  calc p ≤ Γ.V ⊔ p := le_sup_right
    _ = Γ.V ⊔ Γ.U := h_line
    _ = Γ.m := sup_comm _ _

theorem CoordSystem.V_not_le_sup_U {p : L} (hp : IsAtom p) (hp_aff : ¬ p ≤ Γ.m) :
    ¬ Γ.V ≤ p ⊔ Γ.U := by
  intro h
  apply hp_aff
  calc p ≤ Γ.U ⊔ p := le_sup_right
    _ = Γ.U ⊔ Γ.V :=
      line_eq_of_atom_le' Γ.hU hp Γ.hV (Γ.ne_U_of_affine hp_aff).symm Γ.hUV
        (by rwa [sup_comm] at h)

def CoordSystem.xproj (Γ : CoordSystem L) (p : L) : L :=
  (p ⊔ Γ.V) ⊓ (Γ.O ⊔ Γ.U)

def CoordSystem.yproj (Γ : CoordSystem L) (p : L) : L :=
  (p ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.V)

def CoordSystem.point (Γ : CoordSystem L) (x y : L) : L :=
  (x ⊔ Γ.V) ⊓ (y ⊔ Γ.U)

theorem CoordSystem.xproj_le_l (Γ : CoordSystem L) (p : L) :
    Γ.xproj p ≤ Γ.O ⊔ Γ.U := inf_le_right

theorem CoordSystem.yproj_le_n (Γ : CoordSystem L) (p : L) :
    Γ.yproj p ≤ Γ.O ⊔ Γ.V := inf_le_right

theorem CoordSystem.xproj_of_on_l {p : L} (hp : IsAtom p)
    (hp_l : p ≤ Γ.O ⊔ Γ.U) (hp_ne : p ≠ Γ.U) : Γ.xproj p = p := by
  have hp_aff : ¬ p ≤ Γ.m := Γ.affine_of_on_l hp hp_l hp_ne
  have h_l : Γ.O ⊔ Γ.U = p ⊔ Γ.U := by
    rw [sup_comm Γ.O Γ.U, sup_comm p Γ.U]
    exact line_eq_of_atom_le' Γ.hU Γ.hO hp Γ.hOU.symm hp_ne.symm
      (by rwa [sup_comm] at hp_l)
  show (p ⊔ Γ.V) ⊓ (Γ.O ⊔ Γ.U) = p
  rw [h_l]
  exact modular_intersection hp Γ.hV Γ.hU (Γ.ne_V_of_affine hp_aff)
    (Γ.ne_U_of_affine hp_aff) Γ.hUV.symm (Γ.U_not_le_sup_V hp hp_aff)

theorem CoordSystem.yproj_of_on_n {p : L} (hp : IsAtom p)
    (hp_n : p ≤ Γ.O ⊔ Γ.V) (hp_ne : p ≠ Γ.V) : Γ.yproj p = p := by
  have hp_aff : ¬ p ≤ Γ.m := Γ.affine_of_on_n hp hp_n hp_ne
  have h_n : Γ.O ⊔ Γ.V = p ⊔ Γ.V := by
    rw [sup_comm Γ.O Γ.V, sup_comm p Γ.V]
    exact line_eq_of_atom_le' Γ.hV Γ.hO hp Γ.hOV.symm hp_ne.symm
      (by rwa [sup_comm] at hp_n)
  show (p ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.V) = p
  rw [h_n]
  exact modular_intersection hp Γ.hU Γ.hV (Γ.ne_U_of_affine hp_aff)
    (Γ.ne_V_of_affine hp_aff) Γ.hUV (Γ.V_not_le_sup_U hp hp_aff)

theorem CoordSystem.xproj_is_atom {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.m) : IsAtom (Γ.xproj p) := by
  by_cases hp_l : p ≤ Γ.O ⊔ Γ.U
  · rw [Γ.xproj_of_on_l hp hp_l (Γ.ne_U_of_affine hp_aff)]
    exact hp
  · exact project_is_atom Γ.hV hp (fun h => Γ.ne_V_of_affine hp_aff h.symm)
      Γ.hO Γ.hU Γ.hOU Γ.hV_off hp_l (sup_le hp_π le_sup_right)

theorem CoordSystem.yproj_is_atom {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.m) : IsAtom (Γ.yproj p) := by
  by_cases hp_n : p ≤ Γ.O ⊔ Γ.V
  · rw [Γ.yproj_of_on_n hp hp_n (Γ.ne_V_of_affine hp_aff)]
    exact hp
  · exact project_is_atom Γ.hU hp (fun h => Γ.ne_U_of_affine hp_aff h.symm)
      Γ.hO Γ.hV Γ.hOV Γ.hU_not_n hp_n
      (sup_le (le_of_le_of_eq hp_π (sup_right_comm Γ.O Γ.U Γ.V)) le_sup_right)

theorem CoordSystem.xproj_ne_U {p : L} (hp : IsAtom p) (hp_aff : ¬ p ≤ Γ.m) :
    Γ.xproj p ≠ Γ.U :=
  fun h => Γ.U_not_le_sup_V hp hp_aff (h ▸ (inf_le_left : Γ.xproj p ≤ p ⊔ Γ.V))

theorem CoordSystem.yproj_ne_V {p : L} (hp : IsAtom p) (hp_aff : ¬ p ≤ Γ.m) :
    Γ.yproj p ≠ Γ.V :=
  fun h => Γ.V_not_le_sup_U hp hp_aff (h ▸ (inf_le_left : Γ.yproj p ≤ p ⊔ Γ.U))

theorem CoordSystem.sup_V_xproj {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.m) :
    p ⊔ Γ.V = Γ.xproj p ⊔ Γ.V := by
  have hx_atom := Γ.xproj_is_atom hp hp_π hp_aff
  have hx_ne_V : Γ.V ≠ Γ.xproj p :=
    fun h => Γ.hV_off (h ▸ (inf_le_right : Γ.xproj p ≤ Γ.O ⊔ Γ.U))
  rw [sup_comm p Γ.V, sup_comm (Γ.xproj p) Γ.V]
  exact line_eq_of_atom_le' Γ.hV hp hx_atom (Γ.ne_V_of_affine hp_aff).symm hx_ne_V
    (le_of_le_of_eq (inf_le_left : Γ.xproj p ≤ p ⊔ Γ.V) (sup_comm p Γ.V))

theorem CoordSystem.sup_U_yproj {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.m) :
    p ⊔ Γ.U = Γ.yproj p ⊔ Γ.U := by
  have hy_atom := Γ.yproj_is_atom hp hp_π hp_aff
  have hy_ne_U : Γ.U ≠ Γ.yproj p :=
    fun h => Γ.hU_not_n (h ▸ (inf_le_right : Γ.yproj p ≤ Γ.O ⊔ Γ.V))
  rw [sup_comm p Γ.U, sup_comm (Γ.yproj p) Γ.U]
  exact line_eq_of_atom_le' Γ.hU hp hy_atom (Γ.ne_U_of_affine hp_aff).symm hy_ne_U
    (le_of_le_of_eq (inf_le_left : Γ.yproj p ≤ p ⊔ Γ.U) (sup_comm p Γ.U))

theorem CoordSystem.chart_recovers {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.m) :
    Γ.point (Γ.xproj p) (Γ.yproj p) = p := by
  show (Γ.xproj p ⊔ Γ.V) ⊓ (Γ.yproj p ⊔ Γ.U) = p
  rw [← Γ.sup_V_xproj hp hp_π hp_aff, ← Γ.sup_U_yproj hp hp_π hp_aff]
  exact modular_intersection hp Γ.hV Γ.hU (Γ.ne_V_of_affine hp_aff)
    (Γ.ne_U_of_affine hp_aff) Γ.hUV.symm (Γ.U_not_le_sup_V hp hp_aff)

theorem CoordSystem.sup_V_covBy_π {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) :
    x ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
  have hx_aff : ¬ x ≤ Γ.m := Γ.affine_of_on_l hx hx_l hx_ne
  have h_cov := line_covBy_plane hx Γ.hV Γ.hU (Γ.ne_V_of_affine hx_aff)
    hx_ne Γ.hUV.symm (Γ.U_not_le_sup_V hx hx_aff)
  have h_l : Γ.U ⊔ Γ.O = Γ.U ⊔ x :=
    line_eq_of_atom_le' Γ.hU Γ.hO hx Γ.hOU.symm hx_ne.symm
      (by rwa [sup_comm] at hx_l)
  have h_plane : x ⊔ Γ.V ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    apply le_antisymm
    · exact sup_le (sup_le (hx_l.trans le_sup_left) le_sup_right)
        ((le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U).trans le_sup_left)
    · refine sup_le (sup_le ?_ le_sup_right) ?_
      · exact (le_of_le_of_eq le_sup_right h_l).trans
          (sup_le le_sup_right ((le_sup_left : x ≤ x ⊔ Γ.V).trans le_sup_left))
      · exact (le_sup_right : Γ.V ≤ x ⊔ Γ.V).trans le_sup_left
  rwa [h_plane] at h_cov

theorem CoordSystem.point_is_atom {x y : L}
    (hx : IsAtom x) (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U)
    (hy : IsAtom y) (hy_n : y ≤ Γ.O ⊔ Γ.V) (hy_ne : y ≠ Γ.V) :
    IsAtom (Γ.point x y) := by
  have hx_aff : ¬ x ≤ Γ.m := Γ.affine_of_on_l hx hx_l hx_ne
  have hy_aff : ¬ y ≤ Γ.m := Γ.affine_of_on_n hy hy_n hy_ne
  have h_not_le : ¬ x ⊔ Γ.V ≤ y ⊔ Γ.U :=
    fun h => Γ.V_not_le_sup_U hy hy_aff (le_sup_right.trans h)
  have h_not_le' : ¬ y ⊔ Γ.U ≤ x ⊔ Γ.V :=
    fun h => Γ.U_not_le_sup_V hx hx_aff (le_sup_right.trans h)
  have hy_lt : y < y ⊔ Γ.U := lt_of_le_of_ne le_sup_left
    (fun h => Γ.hU_not_n ((h.symm ▸ (le_sup_right : Γ.U ≤ y ⊔ Γ.U)).trans hy_n))
  have h_meet_ne : (x ⊔ Γ.V) ⊓ (y ⊔ Γ.U) ≠ ⊥ :=
    lines_meet_if_coplanar (Γ.sup_V_covBy_π hx hx_l hx_ne)
      (sup_le (hy_n.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
        ((le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U).trans le_sup_left))
      h_not_le' hy hy_lt
  exact meet_of_lines_is_atom hx Γ.hV hy Γ.hU (Γ.ne_V_of_affine hx_aff)
    (Γ.ne_U_of_affine hy_aff) h_not_le h_meet_ne

theorem CoordSystem.point_le_π {x y : L} (hx_l : x ≤ Γ.O ⊔ Γ.U) :
    Γ.point x y ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
  (inf_le_left : Γ.point x y ≤ x ⊔ Γ.V).trans
    (sup_le (hx_l.trans le_sup_left) le_sup_right)

theorem CoordSystem.point_affine {x y : L}
    (hx : IsAtom x) (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U)
    (hy : IsAtom y) (hy_n : y ≤ Γ.O ⊔ Γ.V) (hy_ne : y ≠ Γ.V) :
    ¬ Γ.point x y ≤ Γ.m := by
  intro h
  have hx_aff : ¬ x ≤ Γ.m := Γ.affine_of_on_l hx hx_l hx_ne
  have hy_aff : ¬ y ≤ Γ.m := Γ.affine_of_on_n hy hy_n hy_ne
  have hp_atom := Γ.point_is_atom hx hx_l hx_ne hy hy_n hy_ne
  have h_meet : (Γ.V ⊔ x) ⊓ (Γ.V ⊔ Γ.U) = Γ.V :=
    modular_intersection Γ.hV hx Γ.hU (Γ.ne_V_of_affine hx_aff).symm
      Γ.hUV.symm hx_ne (fun hle => Γ.U_not_le_sup_V hx hx_aff (by rwa [sup_comm] at hle))
  have h_le_V : Γ.point x y ≤ Γ.V :=
    le_of_le_of_eq (le_inf
      ((inf_le_left : Γ.point x y ≤ x ⊔ Γ.V).trans (le_of_eq (sup_comm x Γ.V)))
      (h.trans (le_of_eq (sup_comm Γ.U Γ.V)))) h_meet
  exact Γ.V_not_le_sup_U hy hy_aff
    ((IsAtom.eq_of_le hp_atom Γ.hV h_le_V) ▸ (inf_le_right : Γ.point x y ≤ y ⊔ Γ.U))

theorem CoordSystem.xproj_point {x y : L}
    (hx : IsAtom x) (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U)
    (hy : IsAtom y) (hy_n : y ≤ Γ.O ⊔ Γ.V) (hy_ne : y ≠ Γ.V) :
    Γ.xproj (Γ.point x y) = x := by
  have hx_aff : ¬ x ≤ Γ.m := Γ.affine_of_on_l hx hx_l hx_ne
  have hp_atom := Γ.point_is_atom hx hx_l hx_ne hy hy_n hy_ne
  have hp_aff := Γ.point_affine hx hx_l hx_ne hy hy_n hy_ne
  have h_line : Γ.V ⊔ x = Γ.V ⊔ Γ.point x y :=
    line_eq_of_atom_le' Γ.hV hx hp_atom (Γ.ne_V_of_affine hx_aff).symm
      (Γ.ne_V_of_affine hp_aff).symm
      (le_of_le_of_eq (inf_le_left : Γ.point x y ≤ x ⊔ Γ.V) (sup_comm x Γ.V))
  show (Γ.point x y ⊔ Γ.V) ⊓ (Γ.O ⊔ Γ.U) = x
  rw [sup_comm (Γ.point x y) Γ.V, ← h_line, sup_comm Γ.V x]
  exact Γ.xproj_of_on_l hx hx_l hx_ne

theorem CoordSystem.yproj_point {x y : L}
    (hx : IsAtom x) (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U)
    (hy : IsAtom y) (hy_n : y ≤ Γ.O ⊔ Γ.V) (hy_ne : y ≠ Γ.V) :
    Γ.yproj (Γ.point x y) = y := by
  have hy_aff : ¬ y ≤ Γ.m := Γ.affine_of_on_n hy hy_n hy_ne
  have hp_atom := Γ.point_is_atom hx hx_l hx_ne hy hy_n hy_ne
  have hp_aff := Γ.point_affine hx hx_l hx_ne hy hy_n hy_ne
  have h_line : Γ.U ⊔ y = Γ.U ⊔ Γ.point x y :=
    line_eq_of_atom_le' Γ.hU hy hp_atom (Γ.ne_U_of_affine hy_aff).symm
      (Γ.ne_U_of_affine hp_aff).symm
      (le_of_le_of_eq (inf_le_right : Γ.point x y ≤ y ⊔ Γ.U) (sup_comm y Γ.U))
  show (Γ.point x y ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.V) = y
  rw [sup_comm (Γ.point x y) Γ.U, ← h_line, sup_comm Γ.U y]
  exact Γ.yproj_of_on_n hy hy_n hy_ne

def Affine (Γ : CoordSystem L) : Type u :=
  {p : L // IsAtom p ∧ p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ∧ ¬ p ≤ Γ.U ⊔ Γ.V}

def Ordinate (Γ : CoordSystem L) : Type u :=
  {a : L // IsAtom a ∧ a ≤ Γ.O ⊔ Γ.V ∧ a ≠ Γ.V}

def affineChart (Γ : CoordSystem L) : Affine Γ ≃ Coordinate Γ × Ordinate Γ where
  toFun p :=
    (⟨Γ.xproj p.1, Γ.xproj_is_atom p.2.1 p.2.2.1 p.2.2.2, Γ.xproj_le_l p.1,
        Γ.xproj_ne_U p.2.1 p.2.2.2⟩,
     ⟨Γ.yproj p.1, Γ.yproj_is_atom p.2.1 p.2.2.1 p.2.2.2, Γ.yproj_le_n p.1,
        Γ.yproj_ne_V p.2.1 p.2.2.2⟩)
  invFun xy :=
    ⟨Γ.point xy.1.1 xy.2.1,
      Γ.point_is_atom xy.1.2.1 xy.1.2.2.1 xy.1.2.2.2 xy.2.2.1 xy.2.2.2.1 xy.2.2.2.2,
      Γ.point_le_π xy.1.2.2.1,
      Γ.point_affine xy.1.2.1 xy.1.2.2.1 xy.1.2.2.2 xy.2.2.1 xy.2.2.2.1 xy.2.2.2.2⟩
  left_inv p := Subtype.ext (Γ.chart_recovers p.2.1 p.2.2.1 p.2.2.2)
  right_inv xy := Prod.ext
    (Subtype.ext (Γ.xproj_point xy.1.2.1 xy.1.2.2.1 xy.1.2.2.2
      xy.2.2.1 xy.2.2.2.1 xy.2.2.2.2))
    (Subtype.ext (Γ.yproj_point xy.1.2.1 xy.1.2.2.1 xy.1.2.2.2
      xy.2.2.1 xy.2.2.2.1 xy.2.2.2.2))

end Foam.Bridges

/-- info: 'Foam.Bridges.CoordSystem.xproj_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.xproj_is_atom

/-- info: 'Foam.Bridges.CoordSystem.yproj_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.yproj_is_atom

/-- info: 'Foam.Bridges.CoordSystem.chart_recovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.chart_recovers

/-- info: 'Foam.Bridges.CoordSystem.point_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.point_is_atom

/-- info: 'Foam.Bridges.CoordSystem.point_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.point_affine

/-- info: 'Foam.Bridges.CoordSystem.xproj_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.xproj_point

/-- info: 'Foam.Bridges.CoordSystem.yproj_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.yproj_point

/-- info: 'Foam.Bridges.affineChart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.affineChart
