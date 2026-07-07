import Bridges.FTPG.Slope
import Bridges.FTPG.Assoc
import Bridges.FTPG.Additive

/-!
# The translation lemma — camp two of the `pointSystem_exists` ascent, fifth pitch

The additive row's engine: **translation adds ordinates**.  For an affine
vector atom `A` (off `l`) and an affine base atom `z` (off `l`, off the ray
`O ⊔ A`), with the vector in general position — off the diagonal `O ⊔ C`
(`G1`) and with the perspectivity center `E` off the line `ycoord A ⊔ A`
(`G3`) —

  `ycoord (pg O A z) = coord_add (ycoord z) (ycoord A)`
  (`ycoord_translate`).

The route, model-verified over `PG(2,q)` for `q ∈ {2,3,4,5,7}` (all 336
frames of `PG(2,2)`, family spreads at the rest, every step checked in
place) before carving:

* `D := diagproj z` (= `diagseat (ycoord z)`), `dA := diagproj A`
  (= `diagseat (ycoord A)`), `z' := pg O A z`, `d' := diagproj z'`,
  `W := pg O A D`, and the tower point
  `T := (D ⊔ U) ⊓ (ycoord A ⊔ E)` (= `pg O D (ycoord A)`);
* **KEY** (`E_I ≤ T ⊔ d'`) by one `desargues_planar` with center `E` on the
  axis `m`: triangles `(ycoord A, dA, A)` / `(T, d', W)`, centrally
  perspective definitionally (all three rays are `E`-lines), the `U`-side
  from `cross_parallelism (O, A; z, D)` plus `d' ≤ z' ⊔ U`, the ζ-side
  from `cross_parallelism (O, D; ycoord A, A)`;
* the drop: `ycoord z' = (T ⊔ E_I) ⊓ l` (line identities on KEY);
* the second half (`coord_add_eq_seat_drop`):
  `(T ⊔ E_I) ⊓ l = coord_add y yA` via `coord_add_comm` +
  `coord_add_eq_translation` (the waypoint `C_yA := pg O yA C`) + one
  `parallelogram_completion_well_defined` transfer `(C, C_yA, D, y)` —
  whose lone degenerate branch `D = C ⟺ y = I` closes syntactically
  (`T = C_yA` there, and the translation formula for `coord_add yA I`
  ends at the `E_I`-drop of `C_yA` by definition of `E_I`).

The two degenerate frame families of the previous descent's search
(`C ≤ O ⊔ V` and the anti-diagonal frames) are exactly the failures of
`G1`/`G3` for the *vertical* vector; they dissolve at the next pitch by
the horizontal-offset tower (`X := pg x_h O A` has `ycoord X = ycoord A`
definitionally, and the composition coherence needs only
`reverse_completion` + two standing `cross_parallelism`s) plus the
intercept-dodge (the equation determines the `l`-crossing algebraically;
the off-`l` rows force the constructed point onto `l`, and fibers
collapse) — both probe-sealed over the same fields, no fresh Desargues.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

variable {Γ : CoordSystem L}

theorem CoordSystem.sup_U_eq_l {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) : x ⊔ Γ.U = Γ.O ⊔ Γ.U := by
  rw [sup_comm x Γ.U, sup_comm Γ.O Γ.U]
  exact (line_eq_of_atom_le' Γ.hU Γ.hO hx Γ.hOU.symm hx_ne.symm
    (by rwa [sup_comm] at hx_l)).symm

theorem CoordSystem.sup_O_eq_l {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.O) : Γ.O ⊔ x = Γ.O ⊔ Γ.U :=
  (line_eq_of_atom_le' Γ.hO Γ.hU hx Γ.hOU hx_ne.symm hx_l).symm

theorem CoordSystem.sup_O_eq_diag {x : L} (hx : IsAtom x)
    (hx_d : x ≤ Γ.O ⊔ Γ.C) (hx_ne : x ≠ Γ.O) : Γ.O ⊔ x = Γ.O ⊔ Γ.C :=
  (line_eq_of_atom_le' Γ.hO Γ.hC hx Γ.hOC hx_ne.symm hx_d).symm

theorem CoordSystem.sup_C_eq_diag {x : L} (hx : IsAtom x)
    (hx_d : x ≤ Γ.O ⊔ Γ.C) (hx_ne : x ≠ Γ.C) : Γ.C ⊔ x = Γ.O ⊔ Γ.C :=
  calc Γ.C ⊔ x = Γ.C ⊔ Γ.O := (line_eq_of_atom_le' Γ.hC Γ.hO hx Γ.hOC.symm
        hx_ne.symm (by rwa [sup_comm] at hx_d)).symm
    _ = Γ.O ⊔ Γ.C := sup_comm _ _

theorem CoordSystem.E_line_inf_m {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) :
    (x ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.V) = Γ.E :=
  line_direction hx (Γ.affine_of_on_l hx hx_l hx_ne) CoordSystem.hE_on_m

theorem CoordSystem.U_not_E_line {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U) : ¬ Γ.U ≤ x ⊔ Γ.E := by
  intro h
  have hU_le_E : Γ.U ≤ Γ.E :=
    le_of_le_of_eq (le_inf h Γ.hU_on_m) (Γ.E_line_inf_m hx hx_l hx_ne)
  exact CoordSystem.hEU (IsAtom.eq_of_le Γ.hU Γ.hE_atom hU_le_E).symm

theorem CoordSystem.E_line_inf_diag {x : L} (hx : IsAtom x)
    (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne_O : x ≠ Γ.O) :
    (x ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.C) = Γ.E := by
  have hxE : x ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hx_l)
  have hO_not : ¬ Γ.O ≤ x ⊔ Γ.E := by
    intro h
    have h_line : x ⊔ Γ.E = x ⊔ Γ.O :=
      line_eq_of_atom_le' hx Γ.hE_atom Γ.hO hxE hx_ne_O h
    exact Γ.hE_not_l ((h_line ▸ le_sup_right : Γ.E ≤ x ⊔ Γ.O).trans
      (sup_le hx_l le_sup_left))
  rw [sup_comm x Γ.E, ← CoordSystem.OE_eq_OC, sup_comm Γ.O Γ.E]
  exact modular_intersection Γ.hE_atom hx Γ.hO hxE.symm CoordSystem.hOE.symm
    hx_ne_O (by rw [sup_comm]; exact hO_not)

theorem CoordSystem.C_sup_U_inf_m : (Γ.C ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U :=
  line_direction Γ.hC Γ.hC_not_m Γ.hU_on_m

theorem CoordSystem.C_sup_U_inf_l : (Γ.C ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.U) = Γ.U := by
  rw [sup_comm Γ.C Γ.U, sup_comm Γ.O Γ.U]
  exact modular_intersection Γ.hU Γ.hC Γ.hO Γ.hUC Γ.hOU.symm Γ.hOC.symm
    Γ.hO_not_UC

theorem CoordSystem.C_sup_U_inf_diag : (Γ.C ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.C := by
  rw [show Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O from sup_comm _ _]
  exact modular_intersection Γ.hC Γ.hU Γ.hO Γ.hUC.symm Γ.hOC.symm Γ.hOU.symm
    (fun h => Γ.hO_not_UC (by rwa [sup_comm] at h))

theorem CoordSystem.coord_add_eq_seat_drop (Γ : CoordSystem L) {y yA : L}
    (hy : IsAtom y) (hy_l : y ≤ Γ.O ⊔ Γ.U) (hy_ne_O : y ≠ Γ.O) (hy_ne_U : y ≠ Γ.U)
    (hyA : IsAtom yA) (hyA_l : yA ≤ Γ.O ⊔ Γ.U) (hyA_ne_O : yA ≠ Γ.O)
    (hyA_ne_U : yA ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    ((Γ.diagseat y ⊔ Γ.U) ⊓ (yA ⊔ Γ.E) ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) =
      coord_add Γ y yA := by
  have hy_not_m : ¬ y ≤ Γ.U ⊔ Γ.V := Γ.affine_of_on_l hy hy_l hy_ne_U
  have hyA_not_m : ¬ yA ≤ Γ.U ⊔ Γ.V := Γ.affine_of_on_l hyA hyA_l hyA_ne_U
  have hy_ne_EI : y ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hy_l)
  have hyAE_inf_m : (yA ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.V) = Γ.E :=
    Γ.E_line_inf_m hyA hyA_l hyA_ne_U
  have hU_not_yAE : ¬ Γ.U ≤ yA ⊔ Γ.E := Γ.U_not_E_line hyA hyA_l hyA_ne_U
  have hyAE_inf_diag : (yA ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.C) = Γ.E :=
    Γ.E_line_inf_diag hyA hyA_l hyA_ne_O
  have hE_lt_yAE : Γ.E < yA ⊔ Γ.E := lt_of_le_of_ne le_sup_right
    (fun h => Γ.hE_not_l ((IsAtom.eq_of_le hyA Γ.hE_atom
      (le_sup_left.trans h.symm.le)) ▸ hyA_l))
  have hyAE_le_π : yA ⊔ Γ.E ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (hyA_l.trans le_sup_left) (CoordSystem.hE_on_m.trans Γ.m_le_π)
  -- the waypoint Cy := (C ⊔ U) ⊓ (yA ⊔ E)  (= pg O yA C)
  have hCU_cov : Γ.C ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h1 := line_covBy_plane Γ.hC Γ.hU Γ.hV Γ.hUC.symm
      (Γ.ne_V_of_affine Γ.hC_not_m) Γ.hUV (Γ.V_not_le_sup_U Γ.hC Γ.hC_not_m)
    rwa [show Γ.C ⊔ Γ.U ⊔ Γ.V = (Γ.U ⊔ Γ.V) ⊔ Γ.C from by ac_rfl,
      Γ.m_sup_C_eq_π] at h1
  have hCU_ne_yAE : ¬ yA ⊔ Γ.E ≤ Γ.C ⊔ Γ.U := by
    intro h
    have hE_le_U : Γ.E ≤ Γ.U := le_of_le_of_eq
      (le_inf (le_sup_right.trans h) CoordSystem.hE_on_m) Γ.C_sup_U_inf_m
    exact CoordSystem.hEU (IsAtom.eq_of_le Γ.hE_atom Γ.hU hE_le_U)
  have hCy_ne_bot : (Γ.C ⊔ Γ.U) ⊓ (yA ⊔ Γ.E) ≠ ⊥ :=
    lines_meet_if_coplanar hCU_cov hyAE_le_π hCU_ne_yAE Γ.hE_atom hE_lt_yAE
  have hCy_lt : (Γ.C ⊔ Γ.U) ⊓ (yA ⊔ Γ.E) < Γ.C ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_left
    intro h
    exact hU_not_yAE (le_sup_right.trans (inf_eq_left.mp h))
  have hCy_atom : IsAtom ((Γ.C ⊔ Γ.U) ⊓ (yA ⊔ Γ.E)) :=
    line_height_two Γ.hC Γ.hU Γ.hUC.symm (bot_lt_iff_ne_bot.mpr hCy_ne_bot) hCy_lt
  set Cy := (Γ.C ⊔ Γ.U) ⊓ (yA ⊔ Γ.E) with hCy_def
  have hCy_le_CU : Cy ≤ Γ.C ⊔ Γ.U := inf_le_left
  have hCy_le_yAE : Cy ≤ yA ⊔ Γ.E := inf_le_right
  have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
  have hCy_ne_C : Cy ≠ Γ.C := fun h => hCE (IsAtom.eq_of_le Γ.hC Γ.hE_atom
    (le_of_le_of_eq (le_inf (h ▸ hCy_le_yAE) (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C))
      hyAE_inf_diag))
  have hCy_ne_E : Cy ≠ Γ.E := fun h => CoordSystem.hEU (IsAtom.eq_of_le Γ.hE_atom
    Γ.hU (le_of_le_of_eq (le_inf (h ▸ hCy_le_CU) CoordSystem.hE_on_m)
      Γ.C_sup_U_inf_m))
  have hCy_ne_U : Cy ≠ Γ.U := fun h => hU_not_yAE (h ▸ hCy_le_yAE)
  have hCy_not_m : ¬ Cy ≤ Γ.U ⊔ Γ.V := fun h => hCy_ne_U
    (IsAtom.eq_of_le hCy_atom Γ.hU (le_of_le_of_eq (le_inf hCy_le_CU h)
      Γ.C_sup_U_inf_m))
  have hCy_not_l : ¬ Cy ≤ Γ.O ⊔ Γ.U := fun h => hCy_ne_U
    (IsAtom.eq_of_le hCy_atom Γ.hU (le_of_le_of_eq (le_inf hCy_le_CU h)
      Γ.C_sup_U_inf_l))
  have hC_sup_Cy : Γ.C ⊔ Cy = Γ.C ⊔ Γ.U :=
    (line_eq_of_atom_le' Γ.hC Γ.hU hCy_atom Γ.hUC.symm hCy_ne_C.symm
      hCy_le_CU).symm
  have hCy_sup_E : Cy ⊔ Γ.E = yA ⊔ Γ.E := by
    have h := line_eq_of_atom_le' Γ.hE_atom hyA hCy_atom
      (fun hh => Γ.hE_not_l (hh ▸ hyA_l)) hCy_ne_E.symm
      (by rwa [sup_comm] at hCy_le_yAE)
    rw [sup_comm Cy Γ.E, sup_comm yA Γ.E, h]
  have hCyA_eq : parallelogram_completion Γ.O yA Γ.C (Γ.U ⊔ Γ.V) = Cy := by
    show (Γ.C ⊔ (Γ.O ⊔ yA) ⊓ (Γ.U ⊔ Γ.V)) ⊓
      (yA ⊔ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) = Cy
    rw [Γ.sup_O_eq_l hyA hyA_l hyA_ne_O, Γ.l_inf_m_eq_U]
    rfl
  -- the translation representation: coord_add y yA = pg C Cy y
  have h_rep : coord_add Γ y yA =
      parallelogram_completion Γ.C Cy y (Γ.U ⊔ Γ.V) := by
    by_cases hyy : yA = y
    · subst hyy
      have h : coord_add Γ yA yA = parallelogram_completion Γ.C
          (parallelogram_completion Γ.O yA Γ.C (Γ.U ⊔ Γ.V)) yA (Γ.U ⊔ Γ.V) :=
        coord_add_eq_translation_diag Γ yA hyA hyA_l hyA_ne_O hyA_ne_U
      rwa [hCyA_eq] at h
    · have h_comm : coord_add Γ y yA = coord_add Γ yA y :=
        coord_add_comm Γ y yA hy hyA hy_l hyA_l hy_ne_O hyA_ne_O hy_ne_U
          hyA_ne_U (fun h => hyy h.symm) R hR hR_not h_irred
      have h : coord_add Γ yA y = parallelogram_completion Γ.C
          (parallelogram_completion Γ.O yA Γ.C (Γ.U ⊔ Γ.V)) y (Γ.U ⊔ Γ.V) :=
        coord_add_eq_translation Γ yA y hyA hy hyA_l hy_l hyA_ne_O hy_ne_O
          hyA_ne_U hy_ne_U hyy R hR hR_not h_irred
      rw [h_comm, h, hCyA_eq]
  by_cases hDC : Γ.diagseat y = Γ.C
  · -- the seat is the unit point: y = I, and the tower point IS the waypoint
    have hyI : y = Γ.I := by
      have h1 : (Γ.diagseat y ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = y := Γ.drop_diagseat hy hy_l
      have h2 : (Γ.diagseat y ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) = Γ.I := by
        rw [hDC]
        calc (Γ.C ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U)
            = (Γ.diagproj Γ.C ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) := by
              rw [Γ.diagproj_of_on_OC Γ.hC le_sup_right Γ.hUC.symm]
          _ = Γ.I := Γ.ycoord_C
      exact h1.symm.trans h2
    rw [hDC, h_rep]
    show (Cy ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) =
      parallelogram_completion Γ.C Cy y (Γ.U ⊔ Γ.V)
    have h_tail : parallelogram_completion Γ.C Cy y (Γ.U ⊔ Γ.V) =
        (y ⊔ Γ.U) ⊓ (Cy ⊔ Γ.E_I) := by
      show (y ⊔ (Γ.C ⊔ Cy) ⊓ (Γ.U ⊔ Γ.V)) ⊓
        (Cy ⊔ (Γ.C ⊔ y) ⊓ (Γ.U ⊔ Γ.V)) = (y ⊔ Γ.U) ⊓ (Cy ⊔ Γ.E_I)
      rw [hC_sup_Cy, Γ.C_sup_U_inf_m, hyI, sup_comm Γ.C Γ.I]
      rfl
    rw [h_tail, Γ.sup_U_eq_l hy hy_l hy_ne_U, inf_comm (Γ.O ⊔ Γ.U) (Cy ⊔ Γ.E_I)]
  · -- the generic waypoint transfer (C, Cy, D, y)
    have hD_atom : IsAtom (Γ.diagseat y) := Γ.diagseat_is_atom hy hy_l hy_ne_U
    have hD_le_diag : Γ.diagseat y ≤ Γ.O ⊔ Γ.C := inf_le_right
    have hD_ne_E : Γ.diagseat y ≠ Γ.E := Γ.diagseat_ne_E hy hy_l hy_ne_U
    have hD_ne_U : Γ.diagseat y ≠ Γ.U := fun h => Γ.hU_not_OC (h ▸ hD_le_diag)
    have hD_not_m : ¬ Γ.diagseat y ≤ Γ.U ⊔ Γ.V := fun h => hD_ne_E
      (IsAtom.eq_of_le hD_atom Γ.hE_atom
        (le_inf hD_le_diag h : Γ.diagseat y ≤ Γ.E))
    have hD_le_yEI : Γ.diagseat y ≤ y ⊔ Γ.E_I := inf_le_left
    have hD_ne_O : Γ.diagseat y ≠ Γ.O := by
      intro h
      have h_line : y ⊔ Γ.E_I = y ⊔ Γ.O :=
        line_eq_of_atom_le' hy Γ.hE_I_atom Γ.hO hy_ne_EI hy_ne_O
          (h ▸ hD_le_yEI)
      exact Γ.hE_I_not_l ((h_line ▸ le_sup_right : Γ.E_I ≤ y ⊔ Γ.O).trans
        (sup_le hy_l le_sup_left))
    have hD_not_l : ¬ Γ.diagseat y ≤ Γ.O ⊔ Γ.U := fun h => hD_ne_O
      (IsAtom.eq_of_le hD_atom Γ.hO (le_of_le_of_eq (le_inf h hD_le_diag)
        Γ.l_inf_OC_eq_O))
    have hD_ne_y : Γ.diagseat y ≠ y := fun h => hD_not_l (h.le.trans hy_l)
    have hC_sup_D : Γ.C ⊔ Γ.diagseat y = Γ.O ⊔ Γ.C :=
      Γ.sup_C_eq_diag hD_atom hD_le_diag hDC
    -- the tower point T := (D ⊔ U) ⊓ (yA ⊔ E) is an atom
    have hDU_cov : Γ.diagseat y ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
      have h1 := line_covBy_plane hD_atom Γ.hU Γ.hV hD_ne_U
        (Γ.ne_V_of_affine hD_not_m) Γ.hUV (Γ.V_not_le_sup_U hD_atom hD_not_m)
      have h2 : Γ.diagseat y ⊔ Γ.U ⊔ Γ.V = Γ.O ⊔ Γ.U ⊔ Γ.V := by
        have hmD : (Γ.U ⊔ Γ.V) ⊔ Γ.diagseat y = Γ.O ⊔ Γ.U ⊔ Γ.V := by
          have h_lt : Γ.U ⊔ Γ.V < (Γ.U ⊔ Γ.V) ⊔ Γ.diagseat y :=
            lt_of_le_of_ne le_sup_left
              (fun h => hD_not_m (le_sup_right.trans h.symm.le))
          exact (Γ.m_covBy_π.eq_or_eq h_lt.le (sup_le Γ.m_le_π
            (hD_le_diag.trans Γ.OC_le_π))).resolve_left (ne_of_gt h_lt)
        apply le_antisymm
        · exact sup_le (sup_le (hD_le_diag.trans Γ.OC_le_π)
            (le_sup_right.trans le_sup_left)) le_sup_right
        · rw [← hmD]
          exact sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
            (le_sup_left.trans le_sup_left)
      rwa [h2] at h1
    have hDU_not_yAE : ¬ yA ⊔ Γ.E ≤ Γ.diagseat y ⊔ Γ.U := by
      intro h
      have hE_le : Γ.E ≤ Γ.diagseat y ⊔ Γ.U := le_sup_right.trans h
      have hm_le : Γ.U ⊔ Γ.V ≤ Γ.diagseat y ⊔ Γ.U := by
        rw [← CoordSystem.EU_eq_m]
        exact sup_le hE_le le_sup_right
      exact Γ.V_not_le_sup_U hD_atom hD_not_m (le_sup_right.trans hm_le)
    have hT_ne_bot : (Γ.diagseat y ⊔ Γ.U) ⊓ (yA ⊔ Γ.E) ≠ ⊥ :=
      lines_meet_if_coplanar hDU_cov hyAE_le_π hDU_not_yAE Γ.hE_atom hE_lt_yAE
    have hT_lt : (Γ.diagseat y ⊔ Γ.U) ⊓ (yA ⊔ Γ.E) < Γ.diagseat y ⊔ Γ.U := by
      apply lt_of_le_of_ne inf_le_left
      intro h
      exact hU_not_yAE (le_sup_right.trans (inf_eq_left.mp h))
    have hT_atom : IsAtom ((Γ.diagseat y ⊔ Γ.U) ⊓ (yA ⊔ Γ.E)) :=
      line_height_two hD_atom Γ.hU hD_ne_U (bot_lt_iff_ne_bot.mpr hT_ne_bot)
        hT_lt
    set T := (Γ.diagseat y ⊔ Γ.U) ⊓ (yA ⊔ Γ.E) with hT_def
    have hT_le_DU : T ≤ Γ.diagseat y ⊔ Γ.U := inf_le_left
    have hT_le_yAE : T ≤ yA ⊔ Γ.E := inf_le_right
    have hT_ne_D : T ≠ Γ.diagseat y := fun h => hD_ne_E
      (IsAtom.eq_of_le hD_atom Γ.hE_atom (le_of_le_of_eq
        (le_inf (h ▸ hT_le_yAE) hD_le_diag) hyAE_inf_diag))
    have hD_sup_T : Γ.diagseat y ⊔ T = Γ.diagseat y ⊔ Γ.U :=
      (line_eq_of_atom_le' hD_atom Γ.hU hT_atom hD_ne_U hT_ne_D.symm
        hT_le_DU).symm
    have hDU_inf_l : (Γ.diagseat y ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.U) = Γ.U := by
      rw [sup_comm (Γ.diagseat y) Γ.U, sup_comm Γ.O Γ.U]
      refine modular_intersection Γ.hU hD_atom Γ.hO hD_ne_U.symm Γ.hOU.symm
        hD_ne_O ?_
      intro h
      have h_line : Γ.U ⊔ Γ.diagseat y = Γ.U ⊔ Γ.O :=
        line_eq_of_atom_le' Γ.hU hD_atom Γ.hO hD_ne_U.symm Γ.hOU.symm h
      exact hD_not_l (by
        calc Γ.diagseat y ≤ Γ.U ⊔ Γ.diagseat y := le_sup_right
          _ = Γ.U ⊔ Γ.O := h_line
          _ = Γ.O ⊔ Γ.U := sup_comm _ _)
    -- pg C Cy D = T
    have hPCD : parallelogram_completion Γ.C Cy (Γ.diagseat y) (Γ.U ⊔ Γ.V) = T := by
      show (Γ.diagseat y ⊔ (Γ.C ⊔ Cy) ⊓ (Γ.U ⊔ Γ.V)) ⊓
        (Cy ⊔ (Γ.C ⊔ Γ.diagseat y) ⊓ (Γ.U ⊔ Γ.V)) = T
      rw [hC_sup_Cy, Γ.C_sup_U_inf_m, hC_sup_D]
      show (Γ.diagseat y ⊔ Γ.U) ⊓ (Cy ⊔ Γ.E) = T
      rw [hCy_sup_E]
    -- names and positions for the waypoint transfer (C, Cy, D, y)
    have hC_ne_D : Γ.C ≠ Γ.diagseat y := fun h => hDC h.symm
    have hC_ne_y : Γ.C ≠ y := fun h => Γ.hC_not_l (h.le.trans hy_l)
    have hCy_ne_D : Cy ≠ Γ.diagseat y := fun h =>
      hDC (IsAtom.eq_of_le hD_atom Γ.hC (le_of_le_of_eq
        (le_inf (h ▸ hCy_le_CU) hD_le_diag) Γ.C_sup_U_inf_diag))
    have hCy_ne_y : Cy ≠ y := fun h => hCy_not_l (h.le.trans hy_l)
    have hCy_le_π : Cy ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
      hCy_le_CU.trans (sup_le Γ.hC_plane (le_sup_right.trans le_sup_left))
    have hD_le_π : Γ.diagseat y ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hD_le_diag.trans Γ.OC_le_π
    have hy_le_π : y ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hy_l.trans le_sup_left
    have hm_line : ∀ x, IsAtom x → x ≤ Γ.U ⊔ Γ.V → x ⋖ Γ.U ⊔ Γ.V :=
      fun x hx hxm => line_covers_its_atoms Γ.hU Γ.hV Γ.hUV hx hxm
    have hD_not_CCy : ¬ Γ.diagseat y ≤ Γ.C ⊔ Cy := by
      rw [hC_sup_Cy]
      intro h
      exact hDC (IsAtom.eq_of_le hD_atom Γ.hC (le_of_le_of_eq
        (le_inf h hD_le_diag) Γ.C_sup_U_inf_diag))
    have hy_not_CCy : ¬ y ≤ Γ.C ⊔ Cy := by
      rw [hC_sup_Cy]
      intro h
      exact hy_ne_U (IsAtom.eq_of_le hy Γ.hU (le_of_le_of_eq
        (le_inf h hy_l) Γ.C_sup_U_inf_l))
    have hy_not_CD : ¬ y ≤ Γ.C ⊔ Γ.diagseat y := by
      rw [hC_sup_D]
      intro h
      exact hy_ne_O (IsAtom.eq_of_le hy Γ.hO (le_of_le_of_eq
        (le_inf hy_l h) Γ.l_inf_OC_eq_O))
    have hD_not_Cy_pt : ¬ Γ.diagseat y ≤ Γ.C ⊔ y := by
      intro h
      have hO_not : ¬ Γ.O ≤ Γ.C ⊔ y := by
        intro hO
        have h_line : Γ.C ⊔ y = Γ.C ⊔ Γ.O :=
          line_eq_of_atom_le' Γ.hC hy Γ.hO hC_ne_y Γ.hOC.symm hO
        have hy_le : y ≤ Γ.O ⊔ Γ.C :=
          (le_sup_right.trans h_line.le).trans (sup_comm Γ.C Γ.O).le
        exact hy_ne_O (IsAtom.eq_of_le hy Γ.hO (le_of_le_of_eq
          (le_inf hy_l hy_le) Γ.l_inf_OC_eq_O))
      have h_inf : (Γ.C ⊔ y) ⊓ (Γ.C ⊔ Γ.O) = Γ.C :=
        modular_intersection Γ.hC hy Γ.hO hC_ne_y Γ.hOC.symm hy_ne_O hO_not
      exact hDC (IsAtom.eq_of_le hD_atom Γ.hC (le_of_le_of_eq
        (le_inf h ((sup_comm Γ.O Γ.C) ▸ hD_le_diag)) h_inf))
    have hy_not_DT : ¬ y ≤ Γ.diagseat y ⊔
        parallelogram_completion Γ.C Cy (Γ.diagseat y) (Γ.U ⊔ Γ.V) := by
      rw [hPCD, hD_sup_T]
      intro h
      exact hy_ne_U (IsAtom.eq_of_le hy Γ.hU (le_of_le_of_eq
        (le_inf h hy_l) hDU_inf_l))
    have h_span : Γ.C ⊔ Γ.diagseat y ⊔ y = Γ.O ⊔ Γ.U ⊔ Γ.V :=
      span_plane Γ Γ.hC hD_atom hy hC_ne_D Γ.hC_plane hD_le_π hy_le_π
        Γ.hC_not_m hy_not_CD
    have h_wd := parallelogram_completion_well_defined
      Γ.hC hCy_atom hD_atom hy
      hCy_ne_C.symm hC_ne_D hC_ne_y hCy_ne_D hCy_ne_y hD_ne_y
      Γ.hC_plane hCy_le_π hD_le_π hy_le_π
      Γ.m_le_π Γ.m_covBy_π hm_line
      Γ.hC_not_m hCy_not_m hD_not_m hy_not_m
      hD_not_CCy hy_not_CCy hy_not_CD hD_not_Cy_pt hy_not_DT
      h_span R hR hR_not h_irred
    -- the final drop: pg D T y = (T ⊔ E_I) ⊓ l
    have hDy_inf_m : (Γ.diagseat y ⊔ y) ⊓ (Γ.U ⊔ Γ.V) = Γ.E_I := by
      rw [sup_comm (Γ.diagseat y) y, ← line_eq_of_atom_le' hy Γ.hE_I_atom
        hD_atom hy_ne_EI hD_ne_y.symm hD_le_yEI]
      exact line_direction hy hy_not_m Γ.hE_I_on_m
    have h_drop : parallelogram_completion (Γ.diagseat y) T y (Γ.U ⊔ Γ.V) =
        (T ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) := by
      show (y ⊔ (Γ.diagseat y ⊔ T) ⊓ (Γ.U ⊔ Γ.V)) ⊓
        (T ⊔ (Γ.diagseat y ⊔ y) ⊓ (Γ.U ⊔ Γ.V)) = (T ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U)
      rw [hD_sup_T, line_direction hD_atom hD_not_m le_sup_left, hDy_inf_m,
        Γ.sup_U_eq_l hy hy_l hy_ne_U]
      exact inf_comm _ _
    calc (T ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U)
        = parallelogram_completion (Γ.diagseat y) T y (Γ.U ⊔ Γ.V) := h_drop.symm
      _ = parallelogram_completion Γ.C Cy y (Γ.U ⊔ Γ.V) := by
          rw [← hPCD]; exact h_wd.symm
      _ = coord_add Γ y yA := h_rep.symm

theorem CoordSystem.E_line_inf_diag' {x : L} (hx : IsAtom x)
    (hx_not_diag : ¬ x ≤ Γ.O ⊔ Γ.C) : (x ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.C) = Γ.E := by
  have hxE : x ≠ Γ.E := fun h => hx_not_diag (h.le.trans CoordSystem.hE_le_OC)
  have hx_ne_O : x ≠ Γ.O := fun h => hx_not_diag (h.le.trans le_sup_left)
  have hO_not : ¬ Γ.O ≤ x ⊔ Γ.E := by
    intro h
    have h_line : Γ.E ⊔ x = Γ.E ⊔ Γ.O :=
      line_eq_of_atom_le' Γ.hE_atom hx Γ.hO hxE.symm CoordSystem.hOE.symm
        (by rwa [sup_comm x Γ.E] at h)
    exact hx_not_diag (by
      calc x ≤ Γ.E ⊔ x := le_sup_right
        _ = Γ.E ⊔ Γ.O := h_line
        _ = Γ.O ⊔ Γ.E := sup_comm _ _
        _ = Γ.O ⊔ Γ.C := CoordSystem.OE_eq_OC)
  rw [sup_comm x Γ.E, ← CoordSystem.OE_eq_OC, sup_comm Γ.O Γ.E]
  exact modular_intersection Γ.hE_atom hx Γ.hO hxE.symm CoordSystem.hOE.symm
    hx_ne_O (by rw [sup_comm]; exact hO_not)

theorem CoordSystem.ycoord_translate (Γ : CoordSystem L) {A z : L}
    (hA : IsAtom A) (hA_π : A ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hA_not_m : ¬ A ≤ Γ.U ⊔ Γ.V)
    (hA_not_l : ¬ A ≤ Γ.O ⊔ Γ.U)
    (hz : IsAtom z) (hz_π : z ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hz_not_m : ¬ z ≤ Γ.U ⊔ Γ.V)
    (hz_not_l : ¬ z ≤ Γ.O ⊔ Γ.U)
    (hz_not_ray : ¬ z ≤ Γ.O ⊔ A)
    (hG1 : ¬ A ≤ Γ.O ⊔ Γ.C)
    (hG3 : ¬ Γ.E ≤ Γ.ycoord A ⊔ A)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    Γ.ycoord (parallelogram_completion Γ.O A z (Γ.U ⊔ Γ.V)) =
      coord_add Γ (Γ.ycoord z) (Γ.ycoord A) := by
  have hm_line : ∀ x, IsAtom x → x ≤ Γ.U ⊔ Γ.V → x ⋖ Γ.U ⊔ Γ.V :=
    fun x hx hxm => line_covers_its_atoms Γ.hU Γ.hV Γ.hUV hx hxm
  have hO_le_π : Γ.O ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := le_sup_left.trans le_sup_left
  have hU_le_π : Γ.U ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := le_sup_right.trans le_sup_left
  have hE_le_π : Γ.E ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := CoordSystem.hE_on_m.trans Γ.m_le_π
  have hEI_le_π : Γ.E_I ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := Γ.hE_I_on_m.trans Γ.m_le_π
  have hO_ne_A : Γ.O ≠ A := fun h => hA_not_l (h ▸ le_sup_left)
  have hO_ne_z : Γ.O ≠ z := fun h => hz_not_l (h ▸ le_sup_left)
  have hA_ne_z : A ≠ z := fun h => hz_not_ray (h.symm.le.trans le_sup_right)
  have hz_ne_U : z ≠ Γ.U := Γ.ne_U_of_affine hz_not_m
  have hA_ne_U : A ≠ Γ.U := Γ.ne_U_of_affine hA_not_m
  have hA_ne_V : A ≠ Γ.V := Γ.ne_V_of_affine hA_not_m
  have hA_ne_C : A ≠ Γ.C := fun h => hG1 (h ▸ le_sup_right)
  have hC_not_OA : ¬ Γ.C ≤ Γ.O ⊔ A := fun h => hG1
    (by rw [← line_eq_of_atom_le' Γ.hO hA Γ.hC hO_ne_A Γ.hOC h]; exact le_sup_right)
  -- the two directions eA, ez on m
  have heA_atom : IsAtom ((Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V)) :=
    line_meets_m_at_atom Γ.hO hA hO_ne_A (sup_le hO_le_π hA_π) Γ.m_le_π
      Γ.m_covBy_π Γ.hO_not_m
  have hez_atom : IsAtom ((Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V)) :=
    line_meets_m_at_atom Γ.hO hz hO_ne_z (sup_le hO_le_π hz_π) Γ.m_le_π
      Γ.m_covBy_π Γ.hO_not_m
  have hO_ne_eA : Γ.O ≠ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
    fun h => Γ.hO_not_m (h.le.trans inf_le_right)
  have hO_ne_ez : Γ.O ≠ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) :=
    fun h => Γ.hO_not_m (h.le.trans inf_le_right)
  have hA_ne_eA : A ≠ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
    fun h => hA_not_m (h.le.trans inf_le_right)
  have hA_ne_ez : A ≠ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) :=
    fun h => hA_not_m (h.le.trans inf_le_right)
  have hz_ne_ez : z ≠ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) :=
    fun h => hz_not_m (h.le.trans inf_le_right)
  have hz_ne_eA : z ≠ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
    fun h => hz_not_m (h.le.trans inf_le_right)
  have hA_sup_eA : A ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) = Γ.O ⊔ A := by
    have h := line_eq_of_atom_le' hA Γ.hO heA_atom hO_ne_A.symm hA_ne_eA
      (by rw [sup_comm]; exact inf_le_left)
    rw [← h, sup_comm]
  have hz_sup_ez : z ⊔ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) = Γ.O ⊔ z := by
    have h := line_eq_of_atom_le' hz Γ.hO hez_atom hO_ne_z.symm hz_ne_ez
      (by rw [sup_comm]; exact inf_le_left)
    rw [← h, sup_comm]
  have heA_ne_ez : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≠ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) := by
    intro h
    have h1 : Γ.O ⊔ A = Γ.O ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
      line_eq_of_atom_le' Γ.hO hA heA_atom hO_ne_A hO_ne_eA inf_le_left
    have h2 : Γ.O ⊔ z = Γ.O ⊔ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) :=
      line_eq_of_atom_le' Γ.hO hz hez_atom hO_ne_z hO_ne_ez inf_le_left
    exact hz_not_ray (by
      calc z ≤ Γ.O ⊔ z := le_sup_right
        _ = Γ.O ⊔ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) := h2
        _ = Γ.O ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := by rw [h]
        _ = Γ.O ⊔ A := h1.symm)
  have heA_ne_E : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≠ Γ.E := by
    intro h
    have hE_le : Γ.E ≤ Γ.O ⊔ A := h ▸ (inf_le_left : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ A)
    have h_line : Γ.O ⊔ A = Γ.O ⊔ Γ.E :=
      line_eq_of_atom_le' Γ.hO hA Γ.hE_atom hO_ne_A CoordSystem.hOE hE_le
    exact hG1 (by
      rw [← CoordSystem.OE_eq_OC (Γ := Γ), ← h_line]
      exact le_sup_right)
  have heA_ne_U : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≠ Γ.U := by
    intro h
    have hU_le : Γ.U ≤ Γ.O ⊔ A := h ▸ (inf_le_left : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ A)
    have h_line : Γ.O ⊔ A = Γ.O ⊔ Γ.U :=
      line_eq_of_atom_le' Γ.hO hA Γ.hU hO_ne_A Γ.hOU hU_le
    exact hA_not_l (h_line ▸ le_sup_right)
  have hez_ne_U : (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) ≠ Γ.U := by
    intro h
    have hU_le : Γ.U ≤ Γ.O ⊔ z := h ▸ (inf_le_left : (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ z)
    have h_line : Γ.O ⊔ z = Γ.O ⊔ Γ.U :=
      line_eq_of_atom_le' Γ.hO hz Γ.hU hO_ne_z Γ.hOU hU_le
    exact hz_not_l (h_line ▸ le_sup_right)
  have heA_not_diag : ¬ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.C := fun h =>
    heA_ne_E (IsAtom.eq_of_le heA_atom Γ.hE_atom
      (le_inf h inf_le_right : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.E))
  -- the ordinates
  have hy : IsAtom (Γ.ycoord z) := Γ.ycoord_is_atom hz hz_π hz_not_m
  have hy_l : Γ.ycoord z ≤ Γ.O ⊔ Γ.U := Γ.ycoord_le_l z
  have hy_ne_U : Γ.ycoord z ≠ Γ.U := Γ.ycoord_ne_U hz hz_π hz_not_m
  have hy_ne_O : Γ.ycoord z ≠ Γ.O := by
    intro h
    have hyO : Γ.ycoord Γ.O = Γ.O := Γ.ycoord_of_on_l Γ.hO le_sup_left Γ.hOU
    have h_supU : z ⊔ Γ.U = Γ.O ⊔ Γ.U :=
      Γ.sup_U_eq_of_ycoord_eq hz hz_π hz_not_m Γ.hO hO_le_π Γ.hO_not_m
        (h.trans hyO.symm)
    exact hz_not_l (le_sup_left.trans h_supU.le)
  have hyA : IsAtom (Γ.ycoord A) := Γ.ycoord_is_atom hA hA_π hA_not_m
  have hyA_l : Γ.ycoord A ≤ Γ.O ⊔ Γ.U := Γ.ycoord_le_l A
  have hyA_ne_U : Γ.ycoord A ≠ Γ.U := Γ.ycoord_ne_U hA hA_π hA_not_m
  have hyA_ne_O : Γ.ycoord A ≠ Γ.O := by
    intro h
    have hyO : Γ.ycoord Γ.O = Γ.O := Γ.ycoord_of_on_l Γ.hO le_sup_left Γ.hOU
    have h_supU : A ⊔ Γ.U = Γ.O ⊔ Γ.U :=
      Γ.sup_U_eq_of_ycoord_eq hA hA_π hA_not_m Γ.hO hO_le_π Γ.hO_not_m
        (h.trans hyO.symm)
    exact hA_not_l (le_sup_left.trans h_supU.le)
  have hyA_not_m : ¬ Γ.ycoord A ≤ Γ.U ⊔ Γ.V :=
    Γ.affine_of_on_l hyA hyA_l hyA_ne_U
  have hy_not_m : ¬ Γ.ycoord z ≤ Γ.U ⊔ Γ.V :=
    Γ.affine_of_on_l hy hy_l hy_ne_U
  have hyA_ne_E : Γ.ycoord A ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hyA_l)
  have hyA_ne_EI : Γ.ycoord A ≠ Γ.E_I := fun h => Γ.hE_I_not_l (h ▸ hyA_l)
  have hyA_ne_A : Γ.ycoord A ≠ A := fun h => hA_not_l (h.symm.le.trans hyA_l)
  -- the seat D := diagproj z
  have hD_atom : IsAtom (Γ.diagproj z) := Γ.diagproj_is_atom hz hz_π hz_ne_U
  have hD_le_diag : Γ.diagproj z ≤ Γ.O ⊔ Γ.C := inf_le_right
  have hD_le_zU : Γ.diagproj z ≤ z ⊔ Γ.U := inf_le_left
  have hD_ne_E : Γ.diagproj z ≠ Γ.E := Γ.diagproj_ne_E hz hz_not_m
  have hD_ne_O : Γ.diagproj z ≠ Γ.O := by
    intro h
    have hO_le : Γ.O ≤ z ⊔ Γ.U := h ▸ hD_le_zU
    have h_line : Γ.U ⊔ z = Γ.U ⊔ Γ.O :=
      line_eq_of_atom_le' Γ.hU hz Γ.hO hz_ne_U.symm Γ.hOU.symm
        (by rwa [sup_comm] at hO_le)
    exact hz_not_l (by
      calc z ≤ Γ.U ⊔ z := le_sup_right
        _ = Γ.U ⊔ Γ.O := h_line
        _ = Γ.O ⊔ Γ.U := sup_comm _ _)
  have hD_not_l : ¬ Γ.diagproj z ≤ Γ.O ⊔ Γ.U := fun h => hD_ne_O
    (IsAtom.eq_of_le hD_atom Γ.hO (le_of_le_of_eq (le_inf h hD_le_diag)
      Γ.l_inf_OC_eq_O))
  have hD_not_m : ¬ Γ.diagproj z ≤ Γ.U ⊔ Γ.V := fun h => hD_ne_E
    (IsAtom.eq_of_le hD_atom Γ.hE_atom
      (le_inf hD_le_diag h : Γ.diagproj z ≤ Γ.E))
  have hD_ne_U : Γ.diagproj z ≠ Γ.U := fun h => Γ.hU_not_OC (h ▸ hD_le_diag)
  have hD_le_π : Γ.diagproj z ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hD_le_diag.trans Γ.OC_le_π
  have hA_ne_D : A ≠ Γ.diagproj z := fun h => hG1 (h.le.trans hD_le_diag)
  have hO_ne_D : Γ.O ≠ Γ.diagproj z := hD_ne_O.symm
  have hO_sup_D : Γ.O ⊔ Γ.diagproj z = Γ.O ⊔ Γ.C :=
    Γ.sup_O_eq_diag hD_atom hD_le_diag hD_ne_O
  have hD_not_OA : ¬ Γ.diagproj z ≤ Γ.O ⊔ A := by
    intro h
    have h_inf : (Γ.O ⊔ A) ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
      modular_intersection Γ.hO hA Γ.hC hO_ne_A Γ.hOC hA_ne_C hC_not_OA
    exact hD_ne_O (IsAtom.eq_of_le hD_atom Γ.hO
      (le_of_le_of_eq (le_inf h hD_le_diag) h_inf))
  have hDU_inf_l : (Γ.diagproj z ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.U) = Γ.U := by
    rw [sup_comm (Γ.diagproj z) Γ.U, sup_comm Γ.O Γ.U]
    refine modular_intersection Γ.hU hD_atom Γ.hO hD_ne_U.symm Γ.hOU.symm
      hD_ne_O ?_
    intro h
    have h_line : Γ.U ⊔ Γ.diagproj z = Γ.U ⊔ Γ.O :=
      line_eq_of_atom_le' Γ.hU hD_atom Γ.hO hD_ne_U.symm Γ.hOU.symm h
    exact hD_not_l (by
      calc Γ.diagproj z ≤ Γ.U ⊔ Γ.diagproj z := le_sup_right
        _ = Γ.U ⊔ Γ.O := h_line
        _ = Γ.O ⊔ Γ.U := sup_comm _ _)
  -- the seat dA := diagproj A
  have hdA_atom : IsAtom (Γ.diagproj A) := Γ.diagproj_is_atom hA hA_π hA_ne_U
  have hdA_le_diag : Γ.diagproj A ≤ Γ.O ⊔ Γ.C := inf_le_right
  have hdA_le_AU : Γ.diagproj A ≤ A ⊔ Γ.U := inf_le_left
  have hdA_ne_E : Γ.diagproj A ≠ Γ.E := Γ.diagproj_ne_E hA hA_not_m
  have hdA_ne_O : Γ.diagproj A ≠ Γ.O := by
    intro h
    have hO_le : Γ.O ≤ A ⊔ Γ.U := h ▸ hdA_le_AU
    have h_line : Γ.U ⊔ A = Γ.U ⊔ Γ.O :=
      line_eq_of_atom_le' Γ.hU hA Γ.hO hA_ne_U.symm Γ.hOU.symm
        (by rwa [sup_comm] at hO_le)
    exact hA_not_l (by
      calc A ≤ Γ.U ⊔ A := le_sup_right
        _ = Γ.U ⊔ Γ.O := h_line
        _ = Γ.O ⊔ Γ.U := sup_comm _ _)
  have hdA_not_l : ¬ Γ.diagproj A ≤ Γ.O ⊔ Γ.U := fun h => hdA_ne_O
    (IsAtom.eq_of_le hdA_atom Γ.hO (le_of_le_of_eq (le_inf h hdA_le_diag)
      Γ.l_inf_OC_eq_O))
  have hdA_not_m : ¬ Γ.diagproj A ≤ Γ.U ⊔ Γ.V := fun h => hdA_ne_E
    (IsAtom.eq_of_le hdA_atom Γ.hE_atom
      (le_inf hdA_le_diag h : Γ.diagproj A ≤ Γ.E))
  have hdA_ne_U : Γ.diagproj A ≠ Γ.U := fun h => Γ.hU_not_OC (h ▸ hdA_le_diag)
  have hdA_le_π : Γ.diagproj A ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hdA_le_diag.trans Γ.OC_le_π
  have hA_ne_dA : A ≠ Γ.diagproj A := fun h => hG1 (h.le.trans hdA_le_diag)
  have hdA_le_yAEI : Γ.diagproj A ≤ Γ.ycoord A ⊔ Γ.E_I := by
    rw [← Γ.diagseat_ycoord hA hA_π hA_not_m]
    exact inf_le_left
  have hyA_ne_dA : Γ.ycoord A ≠ Γ.diagproj A :=
    fun h => hdA_not_l (h.symm.le.trans hyA_l)
  have hA_sup_dA : A ⊔ Γ.diagproj A = A ⊔ Γ.U :=
    (line_eq_of_atom_le' hA Γ.hU hdA_atom hA_ne_U hA_ne_dA hdA_le_AU).symm
  have hyA_sup_dA : Γ.ycoord A ⊔ Γ.diagproj A = Γ.ycoord A ⊔ Γ.E_I :=
    (line_eq_of_atom_le' hyA Γ.hE_I_atom hdA_atom hyA_ne_EI hyA_ne_dA
      hdA_le_yAEI).symm
  -- the translate z'
  have hz'_atom : IsAtom (parallelogram_completion Γ.O A z (Γ.U ⊔ Γ.V)) :=
    parallelogram_completion_atom Γ.hO hA hz hO_ne_A hO_ne_z hA_ne_z hO_le_π
      hA_π hz_π Γ.m_le_π Γ.m_covBy_π hm_line Γ.hO_not_m hA_not_m hz_not_m
      hz_not_ray
  set z' := parallelogram_completion Γ.O A z (Γ.U ⊔ Γ.V) with hz'_def
  have hz'_le_zeA : z' ≤ z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := by
    rw [hz'_def]; exact inf_le_left
  have hz'_le_Aez : z' ≤ A ⊔ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) := by
    rw [hz'_def]; exact inf_le_right
  have hz'_π : z' ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    hz'_le_zeA.trans (sup_le hz_π (inf_le_right.trans Γ.m_le_π))
  have hz'_not_m : ¬ z' ≤ Γ.U ⊔ Γ.V := by
    intro h
    have hz'_eq_eA : z' = (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
      IsAtom.eq_of_le hz'_atom heA_atom (le_of_le_of_eq (le_inf hz'_le_zeA h)
        (line_direction hz hz_not_m inf_le_right))
    have heA_le : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ A ⊔ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) :=
      hz'_eq_eA ▸ hz'_le_Aez
    have h_line : A ⊔ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) =
        A ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
      line_eq_of_atom_le' hA hez_atom heA_atom hA_ne_ez hA_ne_eA heA_le
    have hez_le : (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) ≤ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
      le_inf ((le_sup_right.trans h_line.le).trans hA_sup_eA.le) inf_le_right
    exact heA_ne_ez.symm (IsAtom.eq_of_le hez_atom heA_atom hez_le)
  have hz'_ne_U : z' ≠ Γ.U := Γ.ne_U_of_affine hz'_not_m
  have hz'_ne_A : z' ≠ A := by
    intro h
    have hA_le : A ≤ z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := h ▸ hz'_le_zeA
    have hOA_le : Γ.O ⊔ A ≤ z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
      calc Γ.O ⊔ A = A ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := hA_sup_eA.symm
        _ ≤ z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := sup_le hA_le le_sup_right
    have h_cov : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ⋖ z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := by
      have h1 := atom_covBy_join heA_atom hz hz_ne_eA.symm
      rwa [sup_comm ((Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V)) z] at h1
    rcases h_cov.eq_or_eq inf_le_left hOA_le with h1 | h1
    · exact hO_ne_eA (IsAtom.eq_of_le Γ.hO heA_atom (h1 ▸ le_sup_left))
    · exact hz_not_ray (le_of_le_of_eq le_sup_left h1.symm)
  have hz'_ne_z : z' ≠ z := by
    intro h
    have hz_le : z ≤ A ⊔ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) := h ▸ hz'_le_Aez
    have h_line : A ⊔ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) = A ⊔ z :=
      line_eq_of_atom_le' hA hez_atom hz hA_ne_ez hA_ne_z hz_le
    have hO_not_zA : ¬ Γ.O ≤ z ⊔ A := by
      intro hO
      have h_line2 : z ⊔ A = z ⊔ Γ.O :=
        line_eq_of_atom_le' hz hA Γ.hO hA_ne_z.symm hO_ne_z.symm hO
      have hA_le : A ≤ Γ.O ⊔ z := (le_sup_right.trans h_line2.le).trans
        (sup_comm z Γ.O).le
      have h_line3 : Γ.O ⊔ z = Γ.O ⊔ A :=
        line_eq_of_atom_le' Γ.hO hz hA hO_ne_z hO_ne_A hA_le
      exact hz_not_ray (le_of_le_of_eq le_sup_right h_line3)
    have h_inf : (z ⊔ A) ⊓ (z ⊔ Γ.O) = z :=
      modular_intersection hz hA Γ.hO hA_ne_z.symm hO_ne_z.symm hO_ne_A.symm
        hO_not_zA
    have hez_le_z : (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) ≤ z :=
      le_of_le_of_eq (le_inf
        ((le_sup_right.trans h_line.le).trans (sup_comm A z).le)
        (inf_le_left.trans (sup_comm Γ.O z).le)) h_inf
    exact hz_ne_ez.symm (IsAtom.eq_of_le hez_atom hz hez_le_z)
  -- the translate of the seat: W := pg O A D
  have hW_atom : IsAtom (parallelogram_completion Γ.O A (Γ.diagproj z)
      (Γ.U ⊔ Γ.V)) :=
    parallelogram_completion_atom Γ.hO hA hD_atom hO_ne_A hO_ne_D hA_ne_D
      hO_le_π hA_π hD_le_π Γ.m_le_π Γ.m_covBy_π hm_line Γ.hO_not_m hA_not_m
      hD_not_m hD_not_OA
  set W := parallelogram_completion Γ.O A (Γ.diagproj z) (Γ.U ⊔ Γ.V)
    with hW_def
  have hW_le_DeA : W ≤ Γ.diagproj z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := by
    rw [hW_def]; exact inf_le_left
  have hW_le_AE : W ≤ A ⊔ Γ.E := by
    have h : W ≤ A ⊔ (Γ.O ⊔ Γ.diagproj z) ⊓ (Γ.U ⊔ Γ.V) := by
      rw [hW_def]; exact inf_le_right
    rw [hO_sup_D] at h
    exact h
  have hW_le_π : W ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    hW_le_AE.trans (sup_le hA_π hE_le_π)
  have hW_ne_E : W ≠ Γ.E := by
    intro h
    have hE_le : Γ.E ≤ Γ.diagproj z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := h ▸ hW_le_DeA
    have hD_ne_eA : Γ.diagproj z ≠ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
      fun hh => hD_not_m (hh.le.trans inf_le_right)
    have h_line : Γ.diagproj z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) =
        Γ.diagproj z ⊔ Γ.E :=
      line_eq_of_atom_le' hD_atom heA_atom Γ.hE_atom hD_ne_eA hD_ne_E hE_le
    have heA_le_diag : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.C :=
      (le_sup_right.trans h_line.le).trans
        (sup_le hD_le_diag CoordSystem.hE_le_OC)
    exact heA_not_diag heA_le_diag
  have hW_not_m : ¬ W ≤ Γ.U ⊔ Γ.V := by
    intro h
    have hW_eq_eA : W = (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
      IsAtom.eq_of_le hW_atom heA_atom (le_of_le_of_eq (le_inf hW_le_DeA h)
        (line_direction hD_atom hD_not_m inf_le_right))
    have heA_le_AE : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ A ⊔ Γ.E := hW_eq_eA ▸ hW_le_AE
    exact heA_ne_E (IsAtom.eq_of_le heA_atom Γ.hE_atom (le_of_le_of_eq
      (le_inf heA_le_AE inf_le_right)
      (line_direction hA hA_not_m CoordSystem.hE_on_m)))
  have hW_ne_A : W ≠ A := by
    intro h
    have hA_le : A ≤ Γ.diagproj z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := h ▸ hW_le_DeA
    have hOA_le : Γ.O ⊔ A ≤ Γ.diagproj z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
      calc Γ.O ⊔ A = A ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := hA_sup_eA.symm
        _ ≤ Γ.diagproj z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := sup_le hA_le le_sup_right
    have hD_ne_eA : Γ.diagproj z ≠ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) :=
      fun hh => hD_not_m (hh.le.trans inf_le_right)
    have h_cov : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ⋖
        Γ.diagproj z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := by
      have h1 := atom_covBy_join heA_atom hD_atom hD_ne_eA.symm
      rwa [sup_comm ((Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V)) (Γ.diagproj z)] at h1
    rcases h_cov.eq_or_eq inf_le_left hOA_le with h1 | h1
    · exact hO_ne_eA (IsAtom.eq_of_le Γ.hO heA_atom (h1 ▸ le_sup_left))
    · exact hD_not_OA (le_of_le_of_eq le_sup_left h1.symm)
  have hW_ne_D : W ≠ Γ.diagproj z := fun h => hD_ne_E
    (IsAtom.eq_of_le hD_atom Γ.hE_atom (le_of_le_of_eq
      (le_inf (h ▸ hW_le_AE) hD_le_diag) (Γ.E_line_inf_diag' hA hG1)))
  -- the seat of the translate: d' := diagproj z'
  have hd'_atom : IsAtom (Γ.diagproj z') :=
    Γ.diagproj_is_atom hz'_atom hz'_π hz'_ne_U
  have hd'_le_diag : Γ.diagproj z' ≤ Γ.O ⊔ Γ.C := inf_le_right
  have hd'_le_z'U : Γ.diagproj z' ≤ z' ⊔ Γ.U := inf_le_left
  have hd'_ne_E : Γ.diagproj z' ≠ Γ.E := Γ.diagproj_ne_E hz'_atom hz'_not_m
  have hd'_ne_U : Γ.diagproj z' ≠ Γ.U := fun h => Γ.hU_not_OC (h ▸ hd'_le_diag)
  have hd'_le_π : Γ.diagproj z' ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hd'_le_diag.trans Γ.OC_le_π
  have hD_ne_d' : Γ.diagproj z ≠ Γ.diagproj z' := by
    intro h
    have h1 : z ⊔ Γ.U = Γ.diagproj z ⊔ Γ.U := Γ.sup_U_diagproj hz hz_π hz_not_m
    have h2 : z' ⊔ Γ.U = Γ.diagproj z' ⊔ Γ.U :=
      Γ.sup_U_diagproj hz'_atom hz'_π hz'_not_m
    have h3 : z' ≤ z ⊔ Γ.U := by
      rw [h1, h]
      exact le_of_le_of_eq le_sup_left h2
    have heA_not_zU : ¬ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ z ⊔ Γ.U := by
      intro hh
      exact heA_ne_U (IsAtom.eq_of_le heA_atom Γ.hU (le_of_le_of_eq
        (le_inf hh inf_le_right) (line_direction hz hz_not_m le_sup_left)))
    have h_inf : (z ⊔ Γ.U) ⊓ (z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V)) = z :=
      modular_intersection hz Γ.hU heA_atom hz_ne_U hz_ne_eA heA_ne_U.symm
        heA_not_zU
    exact hz'_ne_z (IsAtom.eq_of_le hz'_atom hz (le_of_le_of_eq
      (le_inf h3 hz'_le_zeA) h_inf))
  -- the U-side: U rides d' ⊔ W (and d' ≠ W), by cases on the seat position
  have hU_side : Γ.U ≤ Γ.diagproj z' ⊔ W ∧ Γ.diagproj z' ≠ W := by
    by_cases hz_diag : z ≤ Γ.O ⊔ Γ.C
    · -- z on the diagonal: W = z' and the ride is definitional
      have hD_eq_z : Γ.diagproj z = z := Γ.diagproj_of_on_OC hz hz_diag hz_ne_U
      have hW_eq_z' : W = z' := by
        rw [hW_def, hD_eq_z]
      have hO_sup_z : Γ.O ⊔ z = Γ.O ⊔ Γ.C := Γ.sup_O_eq_diag hz hz_diag
        hO_ne_z.symm
      have hz'_not_diag : ¬ z' ≤ Γ.O ⊔ Γ.C := by
        intro h
        have hO_not_zeA : ¬ Γ.O ≤ z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) := by
          intro hO
          have h_line : z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) = z ⊔ Γ.O :=
            line_eq_of_atom_le' hz heA_atom Γ.hO hz_ne_eA hO_ne_z.symm hO
          have heA_le : (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.C := by
            calc (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ z ⊔ Γ.O := le_sup_right.trans h_line.le
              _ = Γ.O ⊔ z := sup_comm _ _
              _ = Γ.O ⊔ Γ.C := hO_sup_z
          exact heA_not_diag heA_le
        have h_inf : (z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (z ⊔ Γ.O) = z :=
          modular_intersection hz heA_atom Γ.hO hz_ne_eA hO_ne_z.symm
            hO_ne_eA.symm hO_not_zeA
        have hz'_le_zO : z' ≤ z ⊔ Γ.O := by
          rw [sup_comm z Γ.O, hO_sup_z]
          exact h
        exact hz'_ne_z (IsAtom.eq_of_le hz'_atom hz (le_of_le_of_eq
          (le_inf hz'_le_zeA hz'_le_zO) h_inf))
      have hd'_ne_z' : Γ.diagproj z' ≠ z' :=
        fun h => hz'_not_diag (h.symm.le.trans hd'_le_diag)
      have h_line : z' ⊔ Γ.U = z' ⊔ Γ.diagproj z' :=
        line_eq_of_atom_le' hz'_atom Γ.hU hd'_atom hz'_ne_U hd'_ne_z'.symm
          hd'_le_z'U
      constructor
      · rw [hW_eq_z']
        calc Γ.U ≤ z' ⊔ Γ.U := le_sup_right
          _ = z' ⊔ Γ.diagproj z' := h_line
          _ ≤ Γ.diagproj z' ⊔ z' := (sup_comm z' (Γ.diagproj z')).le
      · rw [hW_eq_z']
        exact hd'_ne_z'
    · -- z off the diagonal: one cross_parallelism (O, A; z, D)
      have hz_ne_D : z ≠ Γ.diagproj z := fun h => hz_diag (h.le.trans hD_le_diag)
      have hz'_ne_W : z' ≠ W := by
        intro h
        have hrc_z : parallelogram_completion A Γ.O
            (parallelogram_completion Γ.O A z (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) = z :=
          reverse_completion Γ.hO hA hz hO_ne_A hO_ne_z hA_ne_z hO_le_π hA_π
            hz_π Γ.m_le_π Γ.m_covBy_π hm_line Γ.hO_not_m hA_not_m hz_not_m
            hz_not_ray
        have hrc_D : parallelogram_completion A Γ.O
            (parallelogram_completion Γ.O A (Γ.diagproj z) (Γ.U ⊔ Γ.V))
            (Γ.U ⊔ Γ.V) = Γ.diagproj z :=
          reverse_completion Γ.hO hA hD_atom hO_ne_A hO_ne_D hA_ne_D hO_le_π
            hA_π hD_le_π Γ.m_le_π Γ.m_covBy_π hm_line Γ.hO_not_m hA_not_m
            hD_not_m hD_not_OA
        rw [hz'_def, hW_def] at h
        exact hz_ne_D (by
          calc z = parallelogram_completion A Γ.O
                (parallelogram_completion Γ.O A z (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) :=
                hrc_z.symm
            _ = parallelogram_completion A Γ.O
                (parallelogram_completion Γ.O A (Γ.diagproj z) (Γ.U ⊔ Γ.V))
                (Γ.U ⊔ Γ.V) := by rw [h]
            _ = Γ.diagproj z := hrc_D)
      have hC_not_Oz : ¬ Γ.C ≤ Γ.O ⊔ z := fun hh => hz_diag (by
        rw [← line_eq_of_atom_le' Γ.hO hz Γ.hC hO_ne_z Γ.hOC hh]
        exact le_sup_right)
      have hz_ne_C : z ≠ Γ.C := fun hh => hz_diag (hh.le.trans le_sup_right)
      have hD_not_Oz : ¬ Γ.diagproj z ≤ Γ.O ⊔ z := by
        intro h
        have h_inf : (Γ.O ⊔ z) ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
          modular_intersection Γ.hO hz Γ.hC hO_ne_z Γ.hOC hz_ne_C hC_not_Oz
        exact hD_ne_O (IsAtom.eq_of_le hD_atom Γ.hO
          (le_of_le_of_eq (le_inf h hD_le_diag) h_inf))
      have h_spanU : Γ.O ⊔ z ⊔ Γ.diagproj z = Γ.O ⊔ Γ.U ⊔ Γ.V :=
        span_plane Γ Γ.hO hz hD_atom hO_ne_z hO_le_π hz_π hD_le_π Γ.hO_not_m
          hD_not_Oz
      have hcp := cross_parallelism Γ.hO hA hz hD_atom hO_ne_A hO_ne_z hO_ne_D
        hz_ne_D (hz'_def ▸ hz'_ne_A.symm) (hW_def ▸ hW_ne_A.symm)
        (by rw [← hz'_def, ← hW_def]; exact hz'_ne_W)
        hO_le_π hA_π hz_π hD_le_π Γ.m_le_π Γ.m_covBy_π hm_line
        Γ.hO_not_m hA_not_m hz_not_m hD_not_m
        hz_not_ray hD_not_OA hD_not_Oz h_spanU R hR hR_not h_irred
      have hz_sup_D : z ⊔ Γ.diagproj z = z ⊔ Γ.U :=
        (line_eq_of_atom_le' hz Γ.hU hD_atom hz_ne_U hz_ne_D hD_le_zU).symm
      have hU_le_z'W : Γ.U ≤ z' ⊔ W := by
        have h1 : (z' ⊔ W) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
          rw [hz'_def, hW_def, ← hcp, hz_sup_D]
          exact line_direction hz hz_not_m le_sup_left
        exact h1.symm.le.trans inf_le_left
      have hd'_ne_W : Γ.diagproj z' ≠ W := fun h => hW_ne_E
        (IsAtom.eq_of_le hW_atom Γ.hE_atom (le_of_le_of_eq
          (le_inf hW_le_AE (h ▸ hd'_le_diag)) (Γ.E_line_inf_diag' hA hG1)))
      have hz'_sup_W : z' ⊔ W = z' ⊔ Γ.U :=
        line_eq_of_atom_le' hz'_atom hW_atom Γ.hU hz'_ne_W hz'_ne_U hU_le_z'W
      have hd'_le_z'W : Γ.diagproj z' ≤ z' ⊔ W := by
        rw [hz'_sup_W]
        exact hd'_le_z'U
      have h_line : W ⊔ z' = W ⊔ Γ.diagproj z' :=
        line_eq_of_atom_le' hW_atom hz'_atom hd'_atom hz'_ne_W.symm
          hd'_ne_W.symm (by rwa [sup_comm] at hd'_le_z'W)
      constructor
      · calc Γ.U ≤ z' ⊔ W := hU_le_z'W
          _ = W ⊔ z' := sup_comm _ _
          _ = W ⊔ Γ.diagproj z' := h_line
          _ = Γ.diagproj z' ⊔ W := sup_comm _ _
      · exact hd'_ne_W
  obtain ⟨hU_le_d'W, hd'_ne_W⟩ := hU_side
  -- the tower point T := (D ⊔ U) ⊓ (yA ⊔ E)
  have hyAE_inf_diag : (Γ.ycoord A ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.C) = Γ.E :=
    Γ.E_line_inf_diag hyA hyA_l hyA_ne_O
  have hU_not_yAE : ¬ Γ.U ≤ Γ.ycoord A ⊔ Γ.E :=
    Γ.U_not_E_line hyA hyA_l hyA_ne_U
  have hE_lt_yAE : Γ.E < Γ.ycoord A ⊔ Γ.E := lt_of_le_of_ne le_sup_right
    (fun h => Γ.hE_not_l ((IsAtom.eq_of_le hyA Γ.hE_atom
      (le_sup_left.trans h.symm.le)) ▸ hyA_l))
  have hyAE_le_π : Γ.ycoord A ⊔ Γ.E ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (hyA_l.trans le_sup_left) hE_le_π
  have hDU_cov : Γ.diagproj z ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h1 := line_covBy_plane hD_atom Γ.hU Γ.hV hD_ne_U
      (Γ.ne_V_of_affine hD_not_m) Γ.hUV (Γ.V_not_le_sup_U hD_atom hD_not_m)
    have hmD : (Γ.U ⊔ Γ.V) ⊔ Γ.diagproj z = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      have h_lt : Γ.U ⊔ Γ.V < (Γ.U ⊔ Γ.V) ⊔ Γ.diagproj z :=
        lt_of_le_of_ne le_sup_left
          (fun h => hD_not_m (le_sup_right.trans h.symm.le))
      exact (Γ.m_covBy_π.eq_or_eq h_lt.le (sup_le Γ.m_le_π hD_le_π)).resolve_left
        (ne_of_gt h_lt)
    have h2 : Γ.diagproj z ⊔ Γ.U ⊔ Γ.V = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      apply le_antisymm
      · exact sup_le (sup_le hD_le_π hU_le_π) (le_sup_right : Γ.V ≤ _)
      · rw [← hmD]
        exact sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
          (le_sup_left.trans le_sup_left)
    rwa [h2] at h1
  have hDU_not_yAE : ¬ Γ.ycoord A ⊔ Γ.E ≤ Γ.diagproj z ⊔ Γ.U := by
    intro h
    have hE_le : Γ.E ≤ Γ.diagproj z ⊔ Γ.U := le_sup_right.trans h
    have hm_le : Γ.U ⊔ Γ.V ≤ Γ.diagproj z ⊔ Γ.U := by
      rw [← CoordSystem.EU_eq_m]
      exact sup_le hE_le le_sup_right
    exact Γ.V_not_le_sup_U hD_atom hD_not_m (le_sup_right.trans hm_le)
  have hT_ne_bot : (Γ.diagproj z ⊔ Γ.U) ⊓ (Γ.ycoord A ⊔ Γ.E) ≠ ⊥ :=
    lines_meet_if_coplanar hDU_cov hyAE_le_π hDU_not_yAE Γ.hE_atom hE_lt_yAE
  have hT_lt : (Γ.diagproj z ⊔ Γ.U) ⊓ (Γ.ycoord A ⊔ Γ.E) < Γ.diagproj z ⊔ Γ.U := by
    apply lt_of_le_of_ne inf_le_left
    intro h
    exact hU_not_yAE (le_sup_right.trans (inf_eq_left.mp h))
  have hT_atom : IsAtom ((Γ.diagproj z ⊔ Γ.U) ⊓ (Γ.ycoord A ⊔ Γ.E)) :=
    line_height_two hD_atom Γ.hU hD_ne_U (bot_lt_iff_ne_bot.mpr hT_ne_bot) hT_lt
  set T := (Γ.diagproj z ⊔ Γ.U) ⊓ (Γ.ycoord A ⊔ Γ.E) with hT_def
  have hT_le_DU : T ≤ Γ.diagproj z ⊔ Γ.U := inf_le_left
  have hT_le_yAE : T ≤ Γ.ycoord A ⊔ Γ.E := inf_le_right
  have hT_le_π : T ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hT_le_DU.trans (sup_le hD_le_π hU_le_π)
  have hT_ne_D : T ≠ Γ.diagproj z := fun h => hD_ne_E
    (IsAtom.eq_of_le hD_atom Γ.hE_atom (le_of_le_of_eq
      (le_inf (h ▸ hT_le_yAE) hD_le_diag) hyAE_inf_diag))
  have hT_ne_yA : T ≠ Γ.ycoord A := fun h => hyA_ne_U
    (IsAtom.eq_of_le hyA Γ.hU (le_of_le_of_eq
      (le_inf (h ▸ hT_le_DU) hyA_l) hDU_inf_l))
  have hT_ne_E : T ≠ Γ.E := by
    intro h
    have hE_le : Γ.E ≤ Γ.diagproj z ⊔ Γ.U := h ▸ hT_le_DU
    have hm_le : Γ.U ⊔ Γ.V ≤ Γ.diagproj z ⊔ Γ.U := by
      rw [← CoordSystem.EU_eq_m]
      exact sup_le hE_le le_sup_right
    exact Γ.V_not_le_sup_U hD_atom hD_not_m (le_sup_right.trans hm_le)
  have hT_not_m : ¬ T ≤ Γ.U ⊔ Γ.V := fun h => hT_ne_E
    (IsAtom.eq_of_le hT_atom Γ.hE_atom (le_of_le_of_eq (le_inf hT_le_yAE h)
      (Γ.E_line_inf_m hyA hyA_l hyA_ne_U)))
  have hT_ne_U : T ≠ Γ.U := fun h => hU_not_yAE (h ▸ hT_le_yAE)
  have hT_ne_EI : T ≠ Γ.E_I := fun h => hT_not_m (h.le.trans Γ.hE_I_on_m)
  have hT_ne_d' : T ≠ Γ.diagproj z' := fun h => hT_ne_E
    (IsAtom.eq_of_le hT_atom Γ.hE_atom (le_of_le_of_eq
      (le_inf hT_le_yAE (h.le.trans hd'_le_diag)) hyAE_inf_diag))
  have hA_ne_E : A ≠ Γ.E := fun h => hA_not_m (h ▸ CoordSystem.hE_on_m)
  have hA_not_yAE : ¬ A ≤ Γ.ycoord A ⊔ Γ.E := by
    intro h
    have h_line : Γ.ycoord A ⊔ Γ.E = Γ.ycoord A ⊔ A :=
      line_eq_of_atom_le' hyA Γ.hE_atom hA hyA_ne_E hyA_ne_A h
    exact hG3 (le_of_le_of_eq le_sup_right h_line)
  have hT_ne_W : T ≠ W := by
    intro h
    have h_inf : (Γ.E ⊔ Γ.ycoord A) ⊓ (Γ.E ⊔ A) = Γ.E :=
      modular_intersection Γ.hE_atom hyA hA hyA_ne_E.symm hA_ne_E.symm hyA_ne_A
        (by rw [sup_comm]; exact hA_not_yAE)
    exact hT_ne_E (IsAtom.eq_of_le hT_atom Γ.hE_atom (le_of_le_of_eq
      (le_inf (le_of_le_of_eq hT_le_yAE (sup_comm _ _))
        (le_of_le_of_eq (h ▸ hW_le_AE) (sup_comm _ _))) h_inf))
  have hD_sup_T : Γ.diagproj z ⊔ T = Γ.diagproj z ⊔ Γ.U :=
    (line_eq_of_atom_le' hD_atom Γ.hU hT_atom hD_ne_U hT_ne_D.symm hT_le_DU).symm
  -- the sides of the Desargues configuration
  have hT_not_yAEI : ¬ T ≤ Γ.ycoord A ⊔ Γ.E_I := by
    intro h
    have hE_not_yAEI : ¬ Γ.E ≤ Γ.ycoord A ⊔ Γ.E_I := by
      intro hh
      exact Γ.hE_I_ne_E.symm (IsAtom.eq_of_le Γ.hE_atom Γ.hE_I_atom
        (le_of_le_of_eq (le_inf hh CoordSystem.hE_on_m)
          (line_direction hyA hyA_not_m Γ.hE_I_on_m)))
    have h_inf : (Γ.ycoord A ⊔ Γ.E_I) ⊓ (Γ.ycoord A ⊔ Γ.E) = Γ.ycoord A :=
      modular_intersection hyA Γ.hE_I_atom Γ.hE_atom hyA_ne_EI hyA_ne_E
        Γ.hE_I_ne_E hE_not_yAEI
    exact hT_ne_yA (IsAtom.eq_of_le hT_atom hyA (le_of_le_of_eq
      (le_inf h hT_le_yAE) h_inf))
  have h_sides₁₂ : Γ.ycoord A ⊔ Γ.diagproj A ≠ T ⊔ Γ.diagproj z' := fun h =>
    hT_not_yAEI (hyA_sup_dA ▸ (le_sup_left.trans h.symm.le))
  have h_sides₁₃ : Γ.ycoord A ⊔ A ≠ T ⊔ W := by
    intro h
    have h_inf : (Γ.ycoord A ⊔ A) ⊓ (Γ.ycoord A ⊔ Γ.E) = Γ.ycoord A :=
      modular_intersection hyA hA Γ.hE_atom hyA_ne_A hyA_ne_E hA_ne_E hG3
    exact hT_ne_yA (IsAtom.eq_of_le hT_atom hyA (le_of_le_of_eq
      (le_inf (le_sup_left.trans h.symm.le) hT_le_yAE) h_inf))
  have hdA_ne_d' : Γ.diagproj A ≠ Γ.diagproj z' := by
    intro h
    by_cases hh : z' ≤ A ⊔ Γ.U
    · have hez_not_AU : ¬ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V) ≤ A ⊔ Γ.U := by
        intro hle
        exact hez_ne_U (IsAtom.eq_of_le hez_atom Γ.hU (le_of_le_of_eq
          (le_inf hle inf_le_right) (line_direction hA hA_not_m le_sup_left)))
      have h_inf : (A ⊔ Γ.U) ⊓ (A ⊔ (Γ.O ⊔ z) ⊓ (Γ.U ⊔ Γ.V)) = A :=
        modular_intersection hA Γ.hU hez_atom hA_ne_U hA_ne_ez hez_ne_U.symm
          hez_not_AU
      exact hz'_ne_A (IsAtom.eq_of_le hz'_atom hA (le_of_le_of_eq
        (le_inf hh hz'_le_Aez) h_inf))
    · have h_inf : (Γ.U ⊔ A) ⊓ (Γ.U ⊔ z') = Γ.U :=
        modular_intersection Γ.hU hA hz'_atom hA_ne_U.symm hz'_ne_U.symm
          hz'_ne_A.symm (fun hle => hh (by rwa [sup_comm] at hle))
      have hdA_le : Γ.diagproj A ≤ (Γ.U ⊔ A) ⊓ (Γ.U ⊔ z') :=
        le_inf (by rw [sup_comm]; exact hdA_le_AU)
          (by rw [sup_comm]; exact h ▸ hd'_le_z'U)
      exact hdA_ne_U (IsAtom.eq_of_le hdA_atom Γ.hU (le_of_le_of_eq hdA_le h_inf))
  have h_sides₂₃ : Γ.diagproj A ⊔ A ≠ Γ.diagproj z' ⊔ W := by
    intro h
    have hd'_le : Γ.diagproj z' ≤ A ⊔ Γ.U :=
      calc Γ.diagproj z' ≤ Γ.diagproj A ⊔ A := le_sup_left.trans h.symm.le
        _ = A ⊔ Γ.diagproj A := sup_comm _ _
        _ = A ⊔ Γ.U := hA_sup_dA
    have hd'_le_dA : Γ.diagproj z' ≤ Γ.diagproj A :=
      le_inf hd'_le hd'_le_diag
    exact hdA_ne_d' (IsAtom.eq_of_le hd'_atom hdA_atom hd'_le_dA).symm
  -- the spans and covers
  have hπA : Γ.ycoord A ⊔ Γ.diagproj A ⊔ A = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    refine span_plane Γ hyA hdA_atom hA hyA_ne_dA (hyA_l.trans le_sup_left)
      hdA_le_π hA_π hyA_not_m ?_
    intro h
    have hA_le : A ≤ Γ.ycoord A ⊔ Γ.E_I := hyA_sup_dA ▸ h
    have hAU_le : A ⊔ Γ.U ≤ Γ.ycoord A ⊔ Γ.E_I := by
      rw [← hA_sup_dA]
      exact sup_le hA_le hdA_le_yAEI
    have hU_le_EI : Γ.U ≤ Γ.E_I :=
      le_of_le_of_eq (le_inf (le_sup_right.trans hAU_le) Γ.hU_on_m)
        (line_direction hyA hyA_not_m Γ.hE_I_on_m)
    exact Γ.hE_I_ne_U (IsAtom.eq_of_le Γ.hU Γ.hE_I_atom hU_le_EI).symm
  have hπB : T ⊔ Γ.diagproj z' ⊔ W = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    refine span_plane Γ hT_atom hd'_atom hW_atom hT_ne_d' hT_le_π hd'_le_π
      hW_le_π hT_not_m ?_
    intro hWTd'
    have hU_le_Td' : Γ.U ≤ T ⊔ Γ.diagproj z' :=
      hU_le_d'W.trans (sup_le le_sup_right hWTd')
    have hd'_sup_eq : Γ.diagproj z' ⊔ T = Γ.diagproj z' ⊔ Γ.U :=
      line_eq_of_atom_le' hd'_atom hT_atom Γ.hU hT_ne_d'.symm hd'_ne_U
        (by rwa [sup_comm] at hU_le_Td')
    have hT_le_d'U : T ≤ Γ.diagproj z' ⊔ Γ.U :=
      le_of_le_of_eq le_sup_right hd'_sup_eq
    have hUz'_eq : Γ.U ⊔ z' = Γ.U ⊔ Γ.diagproj z' :=
      line_eq_of_atom_le' Γ.hU hz'_atom hd'_atom hz'_ne_U.symm hd'_ne_U.symm
        (by rwa [sup_comm] at hd'_le_z'U)
    have hUd'_inf_diag : (Γ.U ⊔ Γ.diagproj z') ⊓ (Γ.O ⊔ Γ.C) = Γ.diagproj z' := by
      rw [← hUz'_eq, sup_comm Γ.U z']
      rfl
    have hD_not_Ud' : ¬ Γ.diagproj z ≤ Γ.U ⊔ Γ.diagproj z' := by
      intro hh
      exact hD_ne_d' (IsAtom.eq_of_le hD_atom hd'_atom
        (le_of_le_of_eq (le_inf hh hD_le_diag) hUd'_inf_diag))
    have h_inf : (Γ.U ⊔ Γ.diagproj z') ⊓ (Γ.U ⊔ Γ.diagproj z) = Γ.U :=
      modular_intersection Γ.hU hd'_atom hD_atom hd'_ne_U.symm hD_ne_U.symm
        hD_ne_d'.symm hD_not_Ud'
    have hT_le_U : T ≤ Γ.U :=
      le_of_le_of_eq (le_inf (by rwa [sup_comm] at hT_le_d'U)
        (by rw [sup_comm]; exact hT_le_DU)) h_inf
    exact hT_ne_U (IsAtom.eq_of_le hT_atom Γ.hU hT_le_U)
  have h_cov₁₂ : Γ.ycoord A ⊔ Γ.diagproj A ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have hU_not_yAEI : ¬ Γ.U ≤ Γ.ycoord A ⊔ Γ.E_I := by
      intro h
      exact Γ.hE_I_ne_U (IsAtom.eq_of_le Γ.hU Γ.hE_I_atom
        (le_of_le_of_eq (le_inf h Γ.hU_on_m)
          (line_direction hyA hyA_not_m Γ.hE_I_on_m))).symm
    have h1 := line_covBy_plane hyA Γ.hE_I_atom Γ.hU hyA_ne_EI hyA_ne_U
      Γ.hE_I_ne_U hU_not_yAEI
    have h2 : Γ.ycoord A ⊔ Γ.E_I ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      apply le_antisymm
      · exact sup_le (sup_le (hyA_l.trans le_sup_left) hEI_le_π) hU_le_π
      · rw [← Γ.l_sup_E_I_eq_π]
        refine sup_le (sup_le ?_ ?_) (le_sup_right.trans le_sup_left)
        · have hO_le : Γ.O ≤ Γ.ycoord A ⊔ Γ.U :=
            le_of_le_of_eq le_sup_left (Γ.sup_U_eq_l hyA hyA_l hyA_ne_U).symm
          exact hO_le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        · exact le_sup_right
    rw [h2] at h1
    rwa [← hyA_sup_dA] at h1
  have h_cov₁₃ : Γ.ycoord A ⊔ A ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h1 := line_covBy_plane hyA hA Γ.hE_atom hyA_ne_A hyA_ne_E hA_ne_E hG3
    have h2 : Γ.ycoord A ⊔ A ⊔ Γ.E = Γ.O ⊔ Γ.U ⊔ Γ.V :=
      span_plane Γ hyA hA Γ.hE_atom hyA_ne_A (hyA_l.trans le_sup_left) hA_π
        hE_le_π hyA_not_m hG3
    rwa [h2] at h1
  have h_cov₂₃ : Γ.diagproj A ⊔ A ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h1 := line_covBy_plane hA Γ.hU Γ.hV hA_ne_U hA_ne_V Γ.hUV
      (Γ.V_not_le_sup_U hA hA_not_m)
    have hmA : (Γ.U ⊔ Γ.V) ⊔ A = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      have h_lt : Γ.U ⊔ Γ.V < (Γ.U ⊔ Γ.V) ⊔ A := lt_of_le_of_ne le_sup_left
        (fun h => hA_not_m (le_sup_right.trans h.symm.le))
      exact (Γ.m_covBy_π.eq_or_eq h_lt.le (sup_le Γ.m_le_π hA_π)).resolve_left
        (ne_of_gt h_lt)
    have h2 : A ⊔ Γ.U ⊔ Γ.V = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      apply le_antisymm
      · exact sup_le (sup_le hA_π hU_le_π) le_sup_right
      · rw [← hmA]
        exact sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
          (le_sup_left.trans le_sup_left)
    rw [h2] at h1
    have h3 : Γ.diagproj A ⊔ A = A ⊔ Γ.U := by
      rw [sup_comm (Γ.diagproj A) A, hA_sup_dA]
    rwa [← h3] at h1
  -- the ζ-side: one cross_parallelism (O, D; yA, A)
  have hODyA_eq : parallelogram_completion Γ.O (Γ.diagproj z) (Γ.ycoord A)
      (Γ.U ⊔ Γ.V) = T := by
    show (Γ.ycoord A ⊔ (Γ.O ⊔ Γ.diagproj z) ⊓ (Γ.U ⊔ Γ.V)) ⊓
      (Γ.diagproj z ⊔ (Γ.O ⊔ Γ.ycoord A) ⊓ (Γ.U ⊔ Γ.V)) = T
    rw [hO_sup_D, Γ.sup_O_eq_l hyA hyA_l hyA_ne_O, Γ.l_inf_m_eq_U]
    show (Γ.ycoord A ⊔ Γ.E) ⊓ (Γ.diagproj z ⊔ Γ.U) = T
    rw [hT_def]
    exact inf_comm _ _
  have hODA_eq : parallelogram_completion Γ.O (Γ.diagproj z) A (Γ.U ⊔ Γ.V) = W := by
    rw [hW_def]
    show (A ⊔ (Γ.O ⊔ Γ.diagproj z) ⊓ (Γ.U ⊔ Γ.V)) ⊓
      (Γ.diagproj z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V)) =
      (Γ.diagproj z ⊔ (Γ.O ⊔ A) ⊓ (Γ.U ⊔ Γ.V)) ⊓
      (A ⊔ (Γ.O ⊔ Γ.diagproj z) ⊓ (Γ.U ⊔ Γ.V))
    exact inf_comm _ _
  have hyA_not_OD : ¬ Γ.ycoord A ≤ Γ.O ⊔ Γ.diagproj z := by
    rw [hO_sup_D]
    intro h
    exact hyA_ne_O (IsAtom.eq_of_le hyA Γ.hO (le_of_le_of_eq
      (le_inf hyA_l h) Γ.l_inf_OC_eq_O))
  have hcpζ := cross_parallelism Γ.hO hD_atom hyA hA hO_ne_D hyA_ne_O.symm
    hO_ne_A hyA_ne_A
    (by rw [hODyA_eq]; exact hT_ne_D.symm)
    (by rw [hODA_eq]; exact hW_ne_D.symm)
    (by rw [hODyA_eq, hODA_eq]; exact hT_ne_W)
    hO_le_π hD_le_π (hyA_l.trans le_sup_left) hA_π
    Γ.m_le_π Γ.m_covBy_π hm_line
    Γ.hO_not_m hD_not_m hyA_not_m hA_not_m
    hyA_not_OD
    (by rw [hO_sup_D]; exact hG1)
    (by rw [Γ.sup_O_eq_l hyA hyA_l hyA_ne_O]; exact hA_not_l)
    (span_plane Γ Γ.hO hyA hA hyA_ne_O.symm hO_le_π (hyA_l.trans le_sup_left)
      hA_π Γ.hO_not_m
      (by rw [Γ.sup_O_eq_l hyA hyA_l hyA_ne_O]; exact hA_not_l))
    R hR hR_not h_irred
  have hζ_le_TW : (Γ.ycoord A ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ T ⊔ W := by
    rw [hcpζ, hODyA_eq, hODA_eq]
    exact inf_le_left
  have hζ_atom : IsAtom ((Γ.ycoord A ⊔ A) ⊓ (Γ.U ⊔ Γ.V)) :=
    line_meets_m_at_atom hyA hA hyA_ne_A (sup_le (hyA_l.trans le_sup_left) hA_π)
      Γ.m_le_π Γ.m_covBy_π hyA_not_m
  have hζ_ne_U : (Γ.ycoord A ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≠ Γ.U := by
    intro h
    have hU_le : Γ.U ≤ Γ.ycoord A ⊔ A :=
      h ▸ (inf_le_left : (Γ.ycoord A ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.ycoord A ⊔ A)
    have h_line : Γ.ycoord A ⊔ A = Γ.ycoord A ⊔ Γ.U :=
      line_eq_of_atom_le' hyA hA Γ.hU hyA_ne_A hyA_ne_U hU_le
    exact hA_not_l (by
      calc A ≤ Γ.ycoord A ⊔ A := le_sup_right
        _ = Γ.ycoord A ⊔ Γ.U := h_line
        _ = Γ.O ⊔ Γ.U := Γ.sup_U_eq_l hyA hyA_l hyA_ne_U)
  -- the Desargues: center E on the axis m
  have hE_sup_dA : Γ.E ⊔ Γ.diagproj A = Γ.O ⊔ Γ.C := by
    have h := line_eq_of_atom_le' Γ.hE_atom Γ.hO hdA_atom CoordSystem.hOE.symm
      hdA_ne_E.symm (by
        rw [sup_comm Γ.E Γ.O, CoordSystem.OE_eq_OC (Γ := Γ)]
        exact hdA_le_diag)
    calc Γ.E ⊔ Γ.diagproj A = Γ.E ⊔ Γ.O := h.symm
      _ = Γ.O ⊔ Γ.E := sup_comm _ _
      _ = Γ.O ⊔ Γ.C := CoordSystem.OE_eq_OC
  obtain ⟨axis, haxis_le, haxis_ne, hM12, hM13, hM23⟩ :=
    desargues_planar Γ.hE_atom hyA hdA_atom hA hT_atom hd'_atom hW_atom
      hE_le_π (hyA_l.trans le_sup_left) hdA_le_π hA_π hT_le_π hd'_le_π hW_le_π
      (le_of_le_of_eq hT_le_yAE (sup_comm _ _))
      (le_of_le_of_eq hd'_le_diag hE_sup_dA.symm)
      (le_of_le_of_eq hW_le_AE (sup_comm _ _))
      hyA_ne_dA hyA_ne_A hA_ne_dA.symm
      hT_ne_d' hT_ne_W hd'_ne_W
      h_sides₁₂ h_sides₁₃ h_sides₂₃
      hπA hπB
      hyA_ne_E.symm hdA_ne_E.symm hA_ne_E.symm
      hT_ne_E.symm hd'_ne_E.symm hW_ne_E.symm
      hT_ne_yA.symm hdA_ne_d' hW_ne_A.symm
      R hR hR_not h_irred
      h_cov₁₂ h_cov₁₃ h_cov₂₃
  -- the axis is m, so the E_I-side meets on m at E_I: KEY
  have hU_le_axis : Γ.U ≤ axis := by
    refine le_trans (le_inf ?_ hU_le_d'W) hM23
    calc Γ.U ≤ A ⊔ Γ.U := le_sup_right
      _ = A ⊔ Γ.diagproj A := hA_sup_dA.symm
      _ = Γ.diagproj A ⊔ A := sup_comm _ _
  have hζ_le_axis : (Γ.ycoord A ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ axis :=
    le_trans (le_inf inf_le_left hζ_le_TW) hM13
  have hm_le_axis : Γ.U ⊔ Γ.V ≤ axis := by
    rw [line_eq_of_atom_le' Γ.hU Γ.hV hζ_atom Γ.hUV hζ_ne_U.symm
      (inf_le_right : (Γ.ycoord A ⊔ A) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V)]
    exact sup_le hU_le_axis hζ_le_axis
  have haxis_eq : axis = Γ.U ⊔ Γ.V :=
    (Γ.m_covBy_π.eq_or_eq hm_le_axis haxis_le).resolve_right haxis_ne
  have hM12_le_EI : (Γ.ycoord A ⊔ Γ.diagproj A) ⊓ (T ⊔ Γ.diagproj z') ≤ Γ.E_I :=
    le_of_le_of_eq (le_inf (inf_le_left.trans hyA_sup_dA.le)
      (le_of_le_of_eq hM12 haxis_eq))
      (line_direction hyA hyA_not_m Γ.hE_I_on_m)
  have hM12_ne_bot : (Γ.ycoord A ⊔ Γ.diagproj A) ⊓ (T ⊔ Γ.diagproj z') ≠ ⊥ :=
    lines_meet_if_coplanar h_cov₁₂ (sup_le hT_le_π hd'_le_π)
      (fun h => hT_not_yAEI (hyA_sup_dA ▸ (le_sup_left.trans h)))
      hT_atom (lt_of_le_of_ne le_sup_left (fun h => hT_ne_d'
        (IsAtom.eq_of_le hd'_atom hT_atom (le_sup_right.trans h.symm.le)).symm))
  have hKEY : Γ.E_I ≤ T ⊔ Γ.diagproj z' := by
    have h_eq : (Γ.ycoord A ⊔ Γ.diagproj A) ⊓ (T ⊔ Γ.diagproj z') = Γ.E_I :=
      (Γ.hE_I_atom.le_iff.mp hM12_le_EI).resolve_left hM12_ne_bot
    exact h_eq ▸ inf_le_right
  -- the drop: ycoord z' reads at T
  have hd'_ne_EI : Γ.diagproj z' ≠ Γ.E_I :=
    fun h => Γ.hE_I_not_OC (h ▸ hd'_le_diag)
  have h1 : Γ.diagproj z' ⊔ T = Γ.diagproj z' ⊔ Γ.E_I :=
    line_eq_of_atom_le' hd'_atom hT_atom Γ.hE_I_atom hT_ne_d'.symm hd'_ne_EI
      (by rwa [sup_comm] at hKEY)
  have h2 : T ⊔ Γ.diagproj z' = T ⊔ Γ.E_I :=
    line_eq_of_atom_le' hT_atom hd'_atom Γ.hE_I_atom hT_ne_d' hT_ne_EI hKEY
  have h_ycoord : Γ.ycoord z' = (T ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) :=
    calc Γ.ycoord z' = (Γ.diagproj z' ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) := rfl
      _ = (Γ.diagproj z' ⊔ T) ⊓ (Γ.O ⊔ Γ.U) := by rw [h1]
      _ = (T ⊔ Γ.diagproj z') ⊓ (Γ.O ⊔ Γ.U) := by
          rw [sup_comm (Γ.diagproj z') T]
      _ = (T ⊔ Γ.E_I) ⊓ (Γ.O ⊔ Γ.U) := by rw [h2]
  -- the second half: the T-drop is coord_add
  rw [h_ycoord]
  have h_seat := Γ.coord_add_eq_seat_drop hy hy_l hy_ne_O hy_ne_U hyA hyA_l
    hyA_ne_O hyA_ne_U R hR hR_not h_irred
  rw [Γ.diagseat_ycoord hz hz_π hz_not_m, ← hT_def] at h_seat
  exact h_seat

end Foam.Bridges

/-- info: 'Foam.Bridges.CoordSystem.sup_U_eq_l' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.sup_U_eq_l

/-- info: 'Foam.Bridges.CoordSystem.E_line_inf_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.E_line_inf_diag

/-- info: 'Foam.Bridges.CoordSystem.C_sup_U_inf_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.C_sup_U_inf_diag

/-- info: 'Foam.Bridges.CoordSystem.E_line_inf_diag'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.E_line_inf_diag'

/-- info: 'Foam.Bridges.CoordSystem.coord_add_eq_seat_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.coord_add_eq_seat_drop

/-- info: 'Foam.Bridges.CoordSystem.ycoord_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ycoord_translate
