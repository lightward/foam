import Bridges.FTPG.Ycoord
import Bridges.FTPG.CoordinateAlgebra

/-!
# The origin pencil law — camp two of the `pointSystem_exists` ascent, fourth pitch

The multiplicative row of the line equation: a line through the origin is
the graph of a left-multiplication.  For a direction `S` on the infinity
line `m` other than the vertical (`S ≠ V`), the *slope* of the pencil line
`O ⊔ S` is the height of its point over the unit abscissa,

  `slope S := ycoord ((O ⊔ S) ⊓ (I ⊔ V))`,

and for every affine atom `p` of the plane

  `p ≤ O ⊔ S  ↔  ycoord p = coord_mul (slope S) (xproj p)`
  (`le_origin_line_iff`).

The route is the dilation machinery riding the multiplication's own
cocycle — no fresh Desargues configuration is carved:

* `p = dilation_ext x M` for `M` the slope seat and `x = xproj p`
  (line identities only);
* the horizontal through `M` transports to the horizontal through `p`
  under the dilation (`dilation_preserves_direction` on the pair
  `(M, diagproj M)`), so `diagproj p = dilation_ext x (diagproj M)`;
* `diagproj M = diagseat (slope S) = dilation_ext (slope S) C`
  (`diagseat_ycoord` + `dilation_ext_C`), and the dilation cocycle at `C`
  (`crux_at_C`, the associativity crux) rewrites
  `dilation_ext x (dilation_ext a C) = dilation_ext (coord_mul a x) C`;
* one `perspect_roundtrip` drops the seat back to the coordinate line.

The statement was model-verified over `PG(2,q)` before carving — every
legal frame of every `q ∈ {2,3,5,7,11}` (all 336 frames of `PG(2,2)`
exhaustively), including both degenerate frame families (`C ≤ O ⊔ V` and
the anti-diagonal frames) — the route is frame-uniform; the only case
splits are the four trivial ones (`S = U`, `x = O`, `x = I`,
`slope = I`) plus the self-dissolving `M ≤ O ⊔ C`.

With the vertical pencil (`le_vertical_iff`) and the horizontal pencil
(`le_horizontal_iff`) this seals three of the line equation's four rows;
the remaining row is the additive one — the intercept translation
`y = a·x + b` for lines missing the origin — the summit-remainder of the
camp.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

variable {Γ : CoordSystem L}

noncomputable def CoordSystem.slope (Γ : CoordSystem L) (S : L) : L :=
  Γ.ycoord ((Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V))

theorem CoordSystem.hI_ne_V : Γ.I ≠ Γ.V :=
  fun h => Γ.hV_off (h ▸ Γ.hI_on)

theorem CoordSystem.l_eq_I_sup_U : Γ.O ⊔ Γ.U = Γ.I ⊔ Γ.U := by
  rw [sup_comm Γ.O Γ.U, sup_comm Γ.I Γ.U]
  exact line_eq_of_atom_le' Γ.hU Γ.hO Γ.hI Γ.hOU.symm Γ.hUI
    (by have h := Γ.hI_on; rwa [sup_comm] at h)

theorem CoordSystem.l_inf_IV_eq_I : (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.V) = Γ.I := by
  rw [Γ.l_eq_I_sup_U]
  exact modular_intersection Γ.hI Γ.hU Γ.hV Γ.hUI.symm Γ.hI_ne_V Γ.hUV
    (fun h => Γ.hV_off (Γ.l_eq_I_sup_U ▸ h))

theorem CoordSystem.IV_inf_m_eq_V : (Γ.I ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.V) = Γ.V := by
  rw [sup_comm Γ.I Γ.V, sup_comm Γ.U Γ.V]
  refine modular_intersection Γ.hV Γ.hI Γ.hU Γ.hI_ne_V.symm Γ.hUV.symm Γ.hUI.symm ?_
  intro h
  have h_line : Γ.V ⊔ Γ.I = Γ.V ⊔ Γ.U :=
    line_eq_of_atom_le' Γ.hV Γ.hI Γ.hU Γ.hI_ne_V.symm Γ.hUV.symm h
  have hO_le_IV : Γ.O ⊔ Γ.U ≤ Γ.I ⊔ Γ.V := by
    rw [Γ.l_eq_I_sup_U]
    refine sup_le le_sup_left ?_
    calc Γ.U ≤ Γ.V ⊔ Γ.U := le_sup_right
      _ = Γ.V ⊔ Γ.I := h_line.symm
      _ ≤ Γ.I ⊔ Γ.V := (sup_comm Γ.V Γ.I).le
  have hO_le : Γ.O ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.V) :=
    le_inf le_sup_left (le_sup_left.trans hO_le_IV)
  rw [Γ.l_inf_IV_eq_I] at hO_le
  exact Γ.hOI ((Γ.hI.le_iff.mp hO_le).resolve_left Γ.hO.1)

theorem CoordSystem.vertical_inf_m {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) :
    (x ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.V) = Γ.V := by
  have hVx : Γ.V ≠ x := fun h => Γ.hV_off (h ▸ hx_l)
  rw [sup_comm x Γ.V, sup_comm Γ.U Γ.V]
  refine modular_intersection Γ.hV hx Γ.hU hVx Γ.hUV.symm hx_ne ?_
  intro h
  have h_line : Γ.V ⊔ x = Γ.V ⊔ Γ.U :=
    line_eq_of_atom_le' Γ.hV hx Γ.hU hVx Γ.hUV.symm h
  exact hx_ne (Γ.atom_on_both_eq_U hx hx_l
    ((le_sup_right.trans h_line.le).trans (sup_comm Γ.V Γ.U).le))

theorem CoordSystem.diagseat_I : Γ.diagseat Γ.I = Γ.C := by
  have hIC : Γ.I ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
  have hI_ne_EI : Γ.I ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ Γ.hI_on)
  have hIEI_eq : Γ.I ⊔ Γ.E_I = Γ.I ⊔ Γ.C :=
    (line_eq_of_atom_le' Γ.hI Γ.hC Γ.hE_I_atom hIC hI_ne_EI Γ.hE_I_le_IC).symm
  show (Γ.I ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) = Γ.C
  rw [hIEI_eq, sup_comm Γ.I Γ.C, sup_comm Γ.O Γ.C]
  refine modular_intersection Γ.hC Γ.hI Γ.hO hIC.symm Γ.hOC.symm Γ.hOI.symm ?_
  intro h
  have h_line : Γ.C ⊔ Γ.I = Γ.C ⊔ Γ.O :=
    line_eq_of_atom_le' Γ.hC Γ.hI Γ.hO hIC.symm Γ.hOC.symm h
  have hI_le_diag : Γ.I ≤ Γ.O ⊔ Γ.C :=
    (le_sup_right.trans h_line.le).trans (sup_comm Γ.C Γ.O).le
  have hI_le_O : Γ.I ≤ Γ.O :=
    le_of_le_of_eq (le_inf Γ.hI_on hI_le_diag) Γ.l_inf_OC_eq_O
  exact Γ.hOI ((Γ.hO.le_iff.mp hI_le_O).resolve_left Γ.hI.1).symm

theorem CoordSystem.drop_diagseat {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) :
    ((x ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.C) ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = x := by
  have hx_ne_EI : x ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hx_l)
  exact perspect_roundtrip Γ.hE_I_atom hx hx_ne_EI Γ.hO Γ.hU Γ.hOU Γ.hO Γ.hC Γ.hOC
    Γ.hE_I_not_l Γ.hE_I_not_OC (Γ.l_sup_E_I_eq_π.trans Γ.OC_sup_E_I_eq_π.symm) hx_l

theorem CoordSystem.slope_U : Γ.slope Γ.U = Γ.O := by
  show Γ.ycoord ((Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.V)) = Γ.O
  rw [Γ.l_inf_IV_eq_I]
  exact Γ.ycoord_of_on_l Γ.hI Γ.hI_on Γ.hUI.symm

theorem CoordSystem.ycoord_of_le_origin_line (Γ : CoordSystem L) {S p : L}
    (hS : IsAtom S) (hS_m : S ≤ Γ.U ⊔ Γ.V) (hS_ne_V : S ≠ Γ.V)
    (hp : IsAtom p) (hp_aff : ¬ p ≤ Γ.U ⊔ Γ.V)
    (hp_le : p ≤ Γ.O ⊔ S)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    Γ.ycoord p = coord_mul Γ (Γ.slope S) (Γ.xproj p) := by
  by_cases hSU : S = Γ.U
  · subst hSU
    have hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hp_le.trans le_sup_left
    have hx_atom : IsAtom (Γ.xproj p) := Γ.xproj_is_atom hp hp_π hp_aff
    rw [Γ.slope_U, coord_mul_left_zero Γ (Γ.xproj p) hx_atom (Γ.xproj_le_l p)
      (Γ.xproj_ne_U hp hp_aff)]
    exact Γ.ycoord_of_on_l hp hp_le (Γ.ne_U_of_affine hp_aff)
  have hS_ne_O : S ≠ Γ.O := fun h => Γ.hO_not_m (h ▸ hS_m)
  have hOS : Γ.O ≠ S := hS_ne_O.symm
  have hS_not_n : ¬ S ≤ Γ.O ⊔ Γ.V := fun h =>
    hS_ne_V ((Γ.hV.le_iff.mp (le_of_le_of_eq (le_inf h hS_m)
      Γ.n_inf_m_eq_V)).resolve_left hS.1)
  have hV_not_lam : ¬ Γ.V ≤ Γ.O ⊔ S := by
    intro h
    have h_eq : Γ.O ⊔ S = Γ.O ⊔ Γ.V := line_eq_of_atom_le' Γ.hO hS Γ.hV hOS Γ.hOV h
    exact hS_not_n (h_eq ▸ le_sup_right)
  have hlam_le_π : Γ.O ⊔ S ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_left.trans le_sup_left) (hS_m.trans Γ.m_le_π)
  have hVS_eq_m : Γ.V ⊔ Γ.U = Γ.V ⊔ S :=
    line_eq_of_atom_le' Γ.hV Γ.hU hS Γ.hUV.symm hS_ne_V.symm
      (by rwa [sup_comm] at hS_m)
  have hlam_sup_V : Γ.O ⊔ S ⊔ Γ.V = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    apply le_antisymm (sup_le hlam_le_π le_sup_right)
    refine sup_le (sup_le (le_sup_left.trans le_sup_left) ?_) le_sup_right
    calc Γ.U ≤ Γ.V ⊔ Γ.U := le_sup_right
      _ = Γ.V ⊔ S := hVS_eq_m
      _ ≤ Γ.O ⊔ S ⊔ Γ.V := sup_le le_sup_right (le_sup_right.trans le_sup_left)
  have hlam_covBy : Γ.O ⊔ S ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h := line_covBy_plane Γ.hO hS Γ.hV hOS Γ.hOV hS_ne_V hV_not_lam
    rwa [hlam_sup_V] at h
  have hIV_le_π : Γ.I ⊔ Γ.V ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (Γ.hI_on.trans le_sup_left) le_sup_right
  have hO_not_IV : ¬ Γ.O ≤ Γ.I ⊔ Γ.V := by
    intro h
    have hO_le : Γ.O ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.I ⊔ Γ.V) := le_inf le_sup_left h
    rw [Γ.l_inf_IV_eq_I] at hO_le
    exact Γ.hOI ((Γ.hI.le_iff.mp hO_le).resolve_left Γ.hO.1)
  have hIV_not_lam : ¬ Γ.I ⊔ Γ.V ≤ Γ.O ⊔ S := fun h => hV_not_lam (le_sup_right.trans h)
  have hV_lt_IV : Γ.V < Γ.I ⊔ Γ.V := lt_of_le_of_ne le_sup_right
    (fun h => Γ.hI_ne_V ((Γ.hV.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left
      Γ.hI.1))
  set M := (Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) with hM_def
  have hM_ne_bot : M ≠ ⊥ :=
    lines_meet_if_coplanar hlam_covBy hIV_le_π hIV_not_lam Γ.hV hV_lt_IV
  have hM_lt : M < Γ.O ⊔ S := by
    apply lt_of_le_of_ne inf_le_left
    intro h
    have hlam_le_IV : Γ.O ⊔ S ≤ Γ.I ⊔ Γ.V := inf_eq_left.mp h
    exact hO_not_IV (le_sup_left.trans hlam_le_IV)
  have hM_atom : IsAtom M :=
    line_height_two Γ.hO hS hOS (bot_lt_iff_ne_bot.mpr hM_ne_bot) hM_lt
  have hM_le_lam : M ≤ Γ.O ⊔ S := inf_le_left
  have hM_le_IV : M ≤ Γ.I ⊔ Γ.V := inf_le_right
  have hM_ne_I : M ≠ Γ.I := by
    intro h
    have hI_le_lam : Γ.I ≤ Γ.O ⊔ S := h ▸ hM_le_lam
    have h_eq : Γ.O ⊔ S = Γ.O ⊔ Γ.I := line_eq_of_atom_le' Γ.hO hS Γ.hI hOS Γ.hOI hI_le_lam
    have h_eq2 : Γ.O ⊔ Γ.U = Γ.O ⊔ Γ.I :=
      line_eq_of_atom_le' Γ.hO Γ.hU Γ.hI Γ.hOU Γ.hOI Γ.hI_on
    have hS_le_l : S ≤ Γ.O ⊔ Γ.U := by
      rw [h_eq2, ← h_eq]; exact le_sup_right
    exact hSU (Γ.atom_on_both_eq_U hS hS_le_l hS_m)
  have hM_ne_V : M ≠ Γ.V := fun h => hV_not_lam (h ▸ hM_le_lam)
  have hM_aff : ¬ M ≤ Γ.U ⊔ Γ.V := fun h =>
    hM_ne_V (IsAtom.eq_of_le hM_atom Γ.hV
      (le_of_le_of_eq (le_inf hM_le_IV h) Γ.IV_inf_m_eq_V))
  have hM_ne_O : M ≠ Γ.O := fun h => hO_not_IV (h ▸ hM_le_IV)
  have hM_not_l : ¬ M ≤ Γ.O ⊔ Γ.U := fun h =>
    hM_ne_I (IsAtom.eq_of_le hM_atom Γ.hI
      (le_of_le_of_eq (le_inf h hM_le_IV) Γ.l_inf_IV_eq_I))
  have hM_π : M ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hM_le_IV.trans hIV_le_π
  have hM_ne_U : M ≠ Γ.U := Γ.ne_U_of_affine hM_aff
  have hIM_eq_IV : Γ.I ⊔ M = Γ.I ⊔ Γ.V :=
    (line_eq_of_atom_le' Γ.hI Γ.hV hM_atom Γ.hI_ne_V hM_ne_I.symm hM_le_IV).symm
  have hOM_eq_lam : Γ.O ⊔ M = Γ.O ⊔ S :=
    (line_eq_of_atom_le' Γ.hO hS hM_atom hOS hM_ne_O.symm hM_le_lam).symm
  have ha_def : Γ.slope S = Γ.ycoord M := rfl
  have ha_atom : IsAtom (Γ.ycoord M) := Γ.ycoord_is_atom hM_atom hM_π hM_aff
  have ha_on : Γ.ycoord M ≤ Γ.O ⊔ Γ.U := Γ.ycoord_le_l M
  have ha_ne_U : Γ.ycoord M ≠ Γ.U := Γ.ycoord_ne_U hM_atom hM_π hM_aff
  have ha_ne_O : Γ.ycoord M ≠ Γ.O := by
    intro h
    have hyO : Γ.ycoord Γ.O = Γ.O := Γ.ycoord_of_on_l Γ.hO le_sup_left Γ.hOU
    have h_supU : M ⊔ Γ.U = Γ.O ⊔ Γ.U :=
      Γ.sup_U_eq_of_ycoord_eq hM_atom hM_π hM_aff Γ.hO
        (le_sup_left.trans le_sup_left) Γ.hO_not_m (h.trans hyO.symm)
    exact hM_not_l (le_sup_left.trans h_supU.le)
  have hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hp_le.trans hlam_le_π
  have hx_atom : IsAtom (Γ.xproj p) := Γ.xproj_is_atom hp hp_π hp_aff
  have hx_l : Γ.xproj p ≤ Γ.O ⊔ Γ.U := Γ.xproj_le_l p
  have hx_ne_U : Γ.xproj p ≠ Γ.U := Γ.xproj_ne_U hp hp_aff
  by_cases hxO : Γ.xproj p = Γ.O
  · -- p is the origin
    have hp_le_OV : p ≤ Γ.O ⊔ Γ.V :=
      (Γ.le_vertical_iff hp hp_aff Γ.hO le_sup_left Γ.hOU).mpr hxO
    have h_meet : (Γ.O ⊔ Γ.V) ⊓ (Γ.O ⊔ S) = Γ.O :=
      modular_intersection Γ.hO Γ.hV hS Γ.hOV hOS hS_ne_V.symm hS_not_n
    have hp_eq_O : p = Γ.O :=
      IsAtom.eq_of_le hp Γ.hO (le_of_le_of_eq (le_inf hp_le_OV hp_le) h_meet)
    rw [hxO, hp_eq_O, ha_def,
      coord_mul_right_zero Γ (Γ.ycoord M) ha_atom ha_on ha_ne_U]
    exact Γ.ycoord_of_on_l Γ.hO le_sup_left Γ.hOU
  by_cases hxI : Γ.xproj p = Γ.I
  · -- p is the slope seat itself
    have hp_le_IV : p ≤ Γ.I ⊔ Γ.V :=
      (Γ.le_vertical_iff hp hp_aff Γ.hI Γ.hI_on Γ.hUI.symm).mpr hxI
    have hp_eq_M : p = M := IsAtom.eq_of_le hp hM_atom (le_inf hp_le hp_le_IV)
    rw [hxI, hp_eq_M, ha_def, coord_mul_right_one Γ (Γ.ycoord M) ha_atom ha_on]
  have hδM_eq_p : dilation_ext Γ (Γ.xproj p) M = p := by
    have hIM_inf_m : (Γ.I ⊔ M) ⊓ (Γ.U ⊔ Γ.V) = Γ.V := by
      rw [hIM_eq_IV]; exact Γ.IV_inf_m_eq_V
    show (Γ.O ⊔ M) ⊓ (Γ.xproj p ⊔ (Γ.I ⊔ M) ⊓ (Γ.U ⊔ Γ.V)) = p
    rw [hIM_inf_m, hOM_eq_lam]
    have hp_le_xV : p ≤ Γ.xproj p ⊔ Γ.V :=
      (Γ.le_vertical_iff hp hp_aff hx_atom hx_l hx_ne_U).mpr rfl
    have h_lt : (Γ.O ⊔ S) ⊓ (Γ.xproj p ⊔ Γ.V) < Γ.O ⊔ S := by
      apply lt_of_le_of_ne inf_le_left
      intro h
      have hlam_le_xV : Γ.O ⊔ S ≤ Γ.xproj p ⊔ Γ.V := inf_eq_left.mp h
      have hS_le_V : S ≤ Γ.V := by
        have := le_inf (le_sup_right.trans hlam_le_xV) hS_m
        rwa [Γ.vertical_inf_m hx_atom hx_l hx_ne_U] at this
      exact hS_ne_V ((Γ.hV.le_iff.mp hS_le_V).resolve_left hS.1)
    have h_pos : ⊥ < (Γ.O ⊔ S) ⊓ (Γ.xproj p ⊔ Γ.V) :=
      lt_of_lt_of_le hp.bot_lt (le_inf hp_le hp_le_xV)
    exact (IsAtom.eq_of_le hp (line_height_two Γ.hO hS hOS h_pos h_lt)
      (le_inf hp_le hp_le_xV)).symm
  set dM := Γ.diagproj M with hdM_def
  have hdM_atom : IsAtom dM := Γ.diagproj_is_atom hM_atom hM_π hM_ne_U
  have hdM_le_diag : dM ≤ Γ.O ⊔ Γ.C := inf_le_right
  have hdM_ne_O : dM ≠ Γ.O := by
    intro h
    have hO_le : Γ.O ≤ M ⊔ Γ.U := h ▸ (inf_le_left : Γ.diagproj M ≤ M ⊔ Γ.U)
    have h_line : Γ.U ⊔ M = Γ.U ⊔ Γ.O :=
      line_eq_of_atom_le' Γ.hU hM_atom Γ.hO hM_ne_U.symm Γ.hOU.symm
        (by rwa [sup_comm] at hO_le)
    exact hM_not_l (by
      calc M ≤ Γ.U ⊔ M := le_sup_right
        _ = Γ.U ⊔ Γ.O := h_line
        _ = Γ.O ⊔ Γ.U := sup_comm _ _)
  have hdM_not_l : ¬ dM ≤ Γ.O ⊔ Γ.U := fun h =>
    hdM_ne_O (IsAtom.eq_of_le hdM_atom Γ.hO
      (le_of_le_of_eq (le_inf h hdM_le_diag) Γ.l_inf_OC_eq_O))
  have hdM_not_m : ¬ dM ≤ Γ.U ⊔ Γ.V := fun h =>
    Γ.diagproj_ne_E hM_atom hM_aff (IsAtom.eq_of_le hdM_atom Γ.hE_atom
      (le_inf hdM_le_diag h : dM ≤ Γ.E))
  have hdM_ne_I : dM ≠ Γ.I := fun h => hdM_not_l (h ▸ Γ.hI_on)
  have hW : Γ.diagproj p = dilation_ext Γ (Γ.xproj p) dM := by
    by_cases hMdM : M = dM
    · -- the pencil line is the diagonal itself
      have hlam_eq_diag : Γ.O ⊔ S = Γ.O ⊔ Γ.C := by
        have hM_le_diag : M ≤ Γ.O ⊔ Γ.C := hMdM ▸ hdM_le_diag
        have hO_lt : Γ.O < Γ.O ⊔ S := lt_of_le_of_ne le_sup_left
          (fun h => hS_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans
            h.symm.le)).resolve_left hS.1))
        have hlam_le_diag : Γ.O ⊔ S ≤ Γ.O ⊔ Γ.C := by
          rw [← hOM_eq_lam]; exact sup_le le_sup_left hM_le_diag
        exact ((atom_covBy_join Γ.hO Γ.hC Γ.hOC).eq_or_eq
          hO_lt.le hlam_le_diag).resolve_left (ne_of_gt hO_lt)
      have hp_le_diag : p ≤ Γ.O ⊔ Γ.C := hp_le.trans hlam_eq_diag.le
      rw [Γ.diagproj_of_on_OC hp hp_le_diag (Γ.ne_U_of_affine hp_aff), ← hMdM,
        hδM_eq_p]
    · -- the generic transport, one dilation_preserves_direction
      have hlam_ne_diag : Γ.O ⊔ S ≠ Γ.O ⊔ Γ.C := by
        intro h
        have hM_le_diag : M ≤ Γ.O ⊔ Γ.C := h ▸ hM_le_lam
        exact hMdM (Γ.diagproj_of_on_OC hM_atom hM_le_diag hM_ne_U).symm
      have hC_not_lam : ¬ Γ.C ≤ Γ.O ⊔ S := fun h =>
        hlam_ne_diag (line_eq_of_atom_le' Γ.hO hS Γ.hC hOS Γ.hOC h)
      have hlam_inf_diag : (Γ.O ⊔ S) ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
        modular_intersection Γ.hO hS Γ.hC hOS Γ.hOC
          (fun h => Γ.hC_not_m (h ▸ hS_m)) hC_not_lam
      have hO_diag_eq : Γ.O ⊔ Γ.C = Γ.O ⊔ dM :=
        line_eq_of_atom_le' Γ.hO Γ.hC hdM_atom Γ.hOC hdM_ne_O.symm hdM_le_diag
      have h_images_ne : dilation_ext Γ (Γ.xproj p) M ≠
          dilation_ext Γ (Γ.xproj p) dM := by
        rw [hδM_eq_p]
        intro h
        have hδ_le_diag : dilation_ext Γ (Γ.xproj p) dM ≤ Γ.O ⊔ Γ.C :=
          hO_diag_eq ▸ (inf_le_left : dilation_ext Γ (Γ.xproj p) dM ≤ Γ.O ⊔ dM)
        have hp_le_O : p ≤ Γ.O :=
          le_of_le_of_eq (le_inf hp_le (h ▸ hδ_le_diag)) hlam_inf_diag
        have hp_eq_O : p = Γ.O := IsAtom.eq_of_le hp Γ.hO hp_le_O
        exact hxO (by rw [hp_eq_O]; exact Γ.xproj_of_on_l Γ.hO le_sup_left Γ.hOU)
      have h_dir := dilation_preserves_direction Γ hM_atom hdM_atom
        (Γ.xproj p) hx_atom hx_l hxO hx_ne_U hM_π (hdM_le_diag.trans Γ.OC_le_π)
        hM_aff hdM_not_m hM_not_l hdM_not_l hM_ne_O hdM_ne_O hMdM hM_ne_I hdM_ne_I
        h_images_ne R hR hR_not h_irred
      have hMdM_eq_MU : M ⊔ dM = M ⊔ Γ.U :=
        (line_eq_of_atom_le' hM_atom Γ.hU hdM_atom hM_ne_U hMdM
          (inf_le_left : Γ.diagproj M ≤ M ⊔ Γ.U)).symm
      have hMU_inf_m : (M ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
        rw [sup_comm M Γ.U]
        refine modular_intersection Γ.hU hM_atom Γ.hV hM_ne_U.symm Γ.hUV
          hM_ne_V ?_
        intro h
        have h_line : Γ.U ⊔ M = Γ.U ⊔ Γ.V :=
          line_eq_of_atom_le' Γ.hU hM_atom Γ.hV hM_ne_U.symm Γ.hUV h
        exact hM_aff (le_sup_right.trans h_line.le)
      rw [hδM_eq_p, hMdM_eq_MU, hMU_inf_m] at h_dir
      have hU_le : Γ.U ≤ p ⊔ dilation_ext Γ (Γ.xproj p) dM :=
        h_dir.le.trans inf_le_left
      have hp_ne_δ : p ≠ dilation_ext Γ (Γ.xproj p) dM :=
        fun h => h_images_ne (hδM_eq_p.trans h)
      have h_line : p ⊔ dilation_ext Γ (Γ.xproj p) dM = p ⊔ Γ.U :=
        line_eq_of_atom_le' hp
          (dilation_ext_atom Γ hdM_atom hx_atom hx_l hxO hx_ne_U
            (hdM_le_diag.trans Γ.OC_le_π) hdM_not_l hdM_ne_O hdM_ne_I hdM_not_m)
          Γ.hU hp_ne_δ (Γ.ne_U_of_affine hp_aff) hU_le
      have hδ_le : dilation_ext Γ (Γ.xproj p) dM ≤ (p ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) :=
        le_inf (h_line ▸ le_sup_right)
          (hO_diag_eq ▸ (inf_le_left : dilation_ext Γ (Γ.xproj p) dM ≤ Γ.O ⊔ dM))
      exact (IsAtom.eq_of_le
        (dilation_ext_atom Γ hdM_atom hx_atom hx_l hxO hx_ne_U
          (hdM_le_diag.trans Γ.OC_le_π) hdM_not_l hdM_ne_O hdM_ne_I hdM_not_m)
        (Γ.diagproj_is_atom hp hp_π (Γ.ne_U_of_affine hp_aff)) hδ_le).symm
  have hdM_eq_seat : dM = dilation_ext Γ (Γ.ycoord M) Γ.C := by
    rw [dilation_ext_C Γ (Γ.ycoord M) ha_atom ha_on ha_ne_O ha_ne_U,
      inf_comm (Γ.O ⊔ Γ.C) (Γ.ycoord M ⊔ Γ.E_I), hdM_def]
    exact (Γ.diagseat_ycoord hM_atom hM_π hM_aff).symm
  by_cases haI : Γ.ycoord M = Γ.I
  · -- slope one: the identity dilation
    have hdM_eq_C : dM = Γ.C := by
      rw [hdM_eq_seat, haI]
      exact dilation_ext_identity Γ Γ.hC Γ.hC_plane Γ.hC_not_l
    show (Γ.diagproj p ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = coord_mul Γ (Γ.slope S) (Γ.xproj p)
    rw [ha_def, haI,
      coord_mul_left_one Γ (Γ.xproj p) hx_atom hx_l hx_ne_U, hW, hdM_eq_C,
      dilation_ext_C Γ (Γ.xproj p) hx_atom hx_l hxO hx_ne_U,
      inf_comm (Γ.O ⊔ Γ.C) (Γ.xproj p ⊔ Γ.E_I)]
    exact Γ.drop_diagseat hx_atom hx_l
  · -- the generic slope: the dilation cocycle at C
    have h_ax_ne_O : coord_mul Γ (Γ.ycoord M) (Γ.xproj p) ≠ Γ.O :=
      coord_mul_ne_O' Γ (Γ.ycoord M) (Γ.xproj p) ha_atom hx_atom ha_on hx_l
        ha_ne_O hxO ha_ne_U hx_ne_U
    have h_ax_ne_U : coord_mul Γ (Γ.ycoord M) (Γ.xproj p) ≠ Γ.U :=
      coord_mul_ne_U' Γ (Γ.ycoord M) (Γ.xproj p) ha_atom hx_atom ha_on hx_l
        ha_ne_O ha_ne_U hx_ne_U
    have h_ax_atom : IsAtom (coord_mul Γ (Γ.ycoord M) (Γ.xproj p)) :=
      coord_mul_atom Γ (Γ.ycoord M) (Γ.xproj p) ha_atom hx_atom ha_on hx_l
        ha_ne_O hxO ha_ne_U hx_ne_U
    have h_ax_on : coord_mul Γ (Γ.ycoord M) (Γ.xproj p) ≤ Γ.O ⊔ Γ.U := inf_le_right
    have h_crux := crux_at_C Γ (Γ.ycoord M) (Γ.xproj p) ha_atom hx_atom ha_on hx_l
      ha_ne_O hxO ha_ne_U hx_ne_U haI hxI h_ax_ne_O h_ax_ne_U R hR hR_not h_irred
    show (Γ.diagproj p ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = coord_mul Γ (Γ.slope S) (Γ.xproj p)
    rw [ha_def, hW, hdM_eq_seat, h_crux,
      dilation_ext_C Γ (coord_mul Γ (Γ.ycoord M) (Γ.xproj p)) h_ax_atom h_ax_on
        h_ax_ne_O h_ax_ne_U,
      inf_comm (Γ.O ⊔ Γ.C) (coord_mul Γ (Γ.ycoord M) (Γ.xproj p) ⊔ Γ.E_I)]
    exact Γ.drop_diagseat h_ax_atom h_ax_on

theorem CoordSystem.le_origin_line_of_ycoord (Γ : CoordSystem L) {S p : L}
    (hS : IsAtom S) (hS_m : S ≤ Γ.U ⊔ Γ.V) (hS_ne_V : S ≠ Γ.V)
    (hp : IsAtom p) (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.U ⊔ Γ.V)
    (h_eq : Γ.ycoord p = coord_mul Γ (Γ.slope S) (Γ.xproj p))
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    p ≤ Γ.O ⊔ S := by
  have hx_atom : IsAtom (Γ.xproj p) := Γ.xproj_is_atom hp hp_π hp_aff
  have hx_l : Γ.xproj p ≤ Γ.O ⊔ Γ.U := Γ.xproj_le_l p
  have hx_ne_U : Γ.xproj p ≠ Γ.U := Γ.xproj_ne_U hp hp_aff
  by_cases hSU : S = Γ.U
  · subst hSU
    rw [Γ.slope_U, coord_mul_left_zero Γ (Γ.xproj p) hx_atom hx_l hx_ne_U] at h_eq
    have hyO : Γ.ycoord Γ.O = Γ.O := Γ.ycoord_of_on_l Γ.hO le_sup_left Γ.hOU
    have h_supU : p ⊔ Γ.U = Γ.O ⊔ Γ.U :=
      Γ.sup_U_eq_of_ycoord_eq hp hp_π hp_aff Γ.hO (le_sup_left.trans le_sup_left)
        Γ.hO_not_m (h_eq.trans hyO.symm)
    exact le_sup_left.trans h_supU.le
  have hS_ne_O : S ≠ Γ.O := fun h => Γ.hO_not_m (h ▸ hS_m)
  have hOS : Γ.O ≠ S := hS_ne_O.symm
  have hS_not_n : ¬ S ≤ Γ.O ⊔ Γ.V := fun h =>
    hS_ne_V ((Γ.hV.le_iff.mp (le_of_le_of_eq (le_inf h hS_m)
      Γ.n_inf_m_eq_V)).resolve_left hS.1)
  have hV_not_lam : ¬ Γ.V ≤ Γ.O ⊔ S := by
    intro h
    have h_eq' : Γ.O ⊔ S = Γ.O ⊔ Γ.V := line_eq_of_atom_le' Γ.hO hS Γ.hV hOS Γ.hOV h
    exact hS_not_n (h_eq' ▸ le_sup_right)
  have hlam_le_π : Γ.O ⊔ S ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_left.trans le_sup_left) (hS_m.trans Γ.m_le_π)
  have hVS_eq_m : Γ.V ⊔ Γ.U = Γ.V ⊔ S :=
    line_eq_of_atom_le' Γ.hV Γ.hU hS Γ.hUV.symm hS_ne_V.symm
      (by rwa [sup_comm] at hS_m)
  have hlam_sup_V : Γ.O ⊔ S ⊔ Γ.V = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    apply le_antisymm (sup_le hlam_le_π le_sup_right)
    refine sup_le (sup_le (le_sup_left.trans le_sup_left) ?_) le_sup_right
    calc Γ.U ≤ Γ.V ⊔ Γ.U := le_sup_right
      _ = Γ.V ⊔ S := hVS_eq_m
      _ ≤ Γ.O ⊔ S ⊔ Γ.V := sup_le le_sup_right (le_sup_right.trans le_sup_left)
  have hlam_covBy : Γ.O ⊔ S ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h := line_covBy_plane Γ.hO hS Γ.hV hOS Γ.hOV hS_ne_V hV_not_lam
    rwa [hlam_sup_V] at h
  set p' := (Γ.O ⊔ S) ⊓ (Γ.xproj p ⊔ Γ.V) with hp'_def
  have hxV_le_π : Γ.xproj p ⊔ Γ.V ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (hx_l.trans le_sup_left) le_sup_right
  have hxV_not_lam : ¬ Γ.xproj p ⊔ Γ.V ≤ Γ.O ⊔ S := fun h =>
    hV_not_lam (le_sup_right.trans h)
  have hx_lt_xV : Γ.xproj p < Γ.xproj p ⊔ Γ.V := lt_of_le_of_ne le_sup_left
    (fun h => Γ.hV_off ((le_sup_right.trans h.symm.le).trans hx_l))
  have hp'_ne_bot : p' ≠ ⊥ :=
    lines_meet_if_coplanar hlam_covBy hxV_le_π hxV_not_lam hx_atom hx_lt_xV
  have hp'_lt : p' < Γ.O ⊔ S := by
    apply lt_of_le_of_ne inf_le_left
    intro h
    have hlam_le_xV : Γ.O ⊔ S ≤ Γ.xproj p ⊔ Γ.V := inf_eq_left.mp h
    have hS_le_V : S ≤ Γ.V := by
      have := le_inf (le_sup_right.trans hlam_le_xV) hS_m
      rwa [Γ.vertical_inf_m hx_atom hx_l hx_ne_U] at this
    exact hS_ne_V ((Γ.hV.le_iff.mp hS_le_V).resolve_left hS.1)
  have hp'_atom : IsAtom p' :=
    line_height_two Γ.hO hS hOS (bot_lt_iff_ne_bot.mpr hp'_ne_bot) hp'_lt
  have hp'_le_lam : p' ≤ Γ.O ⊔ S := inf_le_left
  have hp'_le_xV : p' ≤ Γ.xproj p ⊔ Γ.V := inf_le_right
  have hp'_aff : ¬ p' ≤ Γ.U ⊔ Γ.V := by
    intro h
    have hp'_le_V : p' ≤ Γ.V :=
      le_of_le_of_eq (le_inf hp'_le_xV h) (Γ.vertical_inf_m hx_atom hx_l hx_ne_U)
    exact hV_not_lam ((IsAtom.eq_of_le hp'_atom Γ.hV hp'_le_V) ▸ hp'_le_lam)
  have hp'_π : p' ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hp'_le_lam.trans hlam_le_π
  have hx_eq' : Γ.xproj p' = Γ.xproj p :=
    (Γ.le_vertical_iff hp'_atom hp'_aff hx_atom hx_l hx_ne_U).mp hp'_le_xV
  have h_fwd : Γ.ycoord p' = coord_mul Γ (Γ.slope S) (Γ.xproj p') :=
    Γ.ycoord_of_le_origin_line hS hS_m hS_ne_V hp'_atom hp'_aff hp'_le_lam
      R hR hR_not h_irred
  rw [hx_eq'] at h_fwd
  have h_y_eq : Γ.ycoord p = Γ.ycoord p' := h_eq.trans h_fwd.symm
  have h_supU : p ⊔ Γ.U = p' ⊔ Γ.U :=
    Γ.sup_U_eq_of_ycoord_eq hp hp_π hp_aff hp'_atom hp'_π hp'_aff h_y_eq
  have h_supV : p ⊔ Γ.V = p' ⊔ Γ.V :=
    Γ.sup_V_eq_of_xproj_eq hp hp_π hp_aff hp'_atom hp'_π hp'_aff hx_eq'.symm
  have h_meet : (p' ⊔ Γ.V) ⊓ (p' ⊔ Γ.U) = p' :=
    modular_intersection hp'_atom Γ.hV Γ.hU (Γ.ne_V_of_affine hp'_aff)
      (Γ.ne_U_of_affine hp'_aff) Γ.hUV.symm (Γ.U_not_le_sup_V hp'_atom hp'_aff)
  have hp_le_p' : p ≤ p' := by
    rw [← h_meet]
    exact le_inf (h_supV ▸ (le_sup_left : p ≤ p ⊔ Γ.V))
      (h_supU ▸ (le_sup_left : p ≤ p ⊔ Γ.U))
  exact (IsAtom.eq_of_le hp hp'_atom hp_le_p') ▸ hp'_le_lam

theorem CoordSystem.le_origin_line_iff (Γ : CoordSystem L) {S p : L}
    (hS : IsAtom S) (hS_m : S ≤ Γ.U ⊔ Γ.V) (hS_ne_V : S ≠ Γ.V)
    (hp : IsAtom p) (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.U ⊔ Γ.V)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    p ≤ Γ.O ⊔ S ↔ Γ.ycoord p = coord_mul Γ (Γ.slope S) (Γ.xproj p) :=
  ⟨fun h => Γ.ycoord_of_le_origin_line hS hS_m hS_ne_V hp hp_aff h R hR hR_not
      h_irred,
   fun h => Γ.le_origin_line_of_ycoord hS hS_m hS_ne_V hp hp_π hp_aff h R hR
      hR_not h_irred⟩

end Foam.Bridges

/-- info: 'Foam.Bridges.CoordSystem.slope_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.slope_U

/-- info: 'Foam.Bridges.CoordSystem.diagseat_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.diagseat_I

/-- info: 'Foam.Bridges.CoordSystem.ycoord_of_le_origin_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ycoord_of_le_origin_line

/-- info: 'Foam.Bridges.CoordSystem.le_origin_line_of_ycoord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.le_origin_line_of_ycoord

/-- info: 'Foam.Bridges.CoordSystem.le_origin_line_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.le_origin_line_iff
