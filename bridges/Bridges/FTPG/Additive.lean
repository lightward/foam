import Bridges.FTPG.CoordinateAlgebra
import Bridges.FTPG.AddCancel
import Bridges.FTPG.AssocCapstone
import Bridges.FTPG.WellDefined

/-!
# The additive group of the FTPG coordinate line — CLOSED

This file is the additive-group construction for the FTPG *coordinate line*
`Coordinate Φ.Γ` — the geometric model of the coordinate ring's additive group,
built synthetically inside a modular, complemented, atomistic lattice `L` (the
subspace lattice of the fundamental theorem of projective geometry).  Addition is
`fadd` (lattice-level `coord_add`, a parallelogram completion); negation is `fneg`.

Everything is proven, axiom-clean-modulo-classical
(`[propext, Classical.choice, Quot.sound]`): `fadd_assoc_total` seals the full
abelian group, no `sorry` anywhere in its trace.

## The shape of the proof

* The **abelian-group skeleton**: `fadd_comm`, `fadd_left_cancel`,
  `fadd_right_cancel`, `fadd_zero`, `fzero_add`, `fadd_neg`, `fneg_add`,
  `fneg_fneg`, and the *generic* associator `fadd_assoc_generic`.

* The **translation calculus**: `key_identity` (`τ_a(C_b) = C_{a+b}`),
  `beta_step_core`/`dbl_beta_generic` (`τ_{a+b} = τ_a ∘ τ_b` on towers, composite
  parameter good), `dbl_key_identity` (the coincident case), `recover_std`,
  `reverse_completion`, `C_tower_facts`, `tower_meets_E_line`, `tower_inj`.

* The **τ-inverse master lemma** `tau_inv_tower` — `τ_x (τ_{-x} X) = X` for `X`
  on the auxiliary line `q` in general position: the one composition law the
  β-step cannot state (composite parameter `O`).  Proven by transporting both
  translations through the auxiliary point `z = (x ⊔ Γ.E) ⊓ (w' ⊔ X)`
  (`inv_aux_point`), with `neg_tower_reverse` (`pc x O C m = C_{-x}`)
  identifying the base pairs.  This subsumes what the prior era isolated as the
  base-change involution, the 17 witness-incidence leaves, AND the char-2 knot:
  `char2_absorb` is just `tau_inv_tower` with `-a` rewritten to `a`.

* The **two degenerate associators**, as corollaries:
  `inv_absorb_generic` (`a + (-a + c) = c`, two `key_identity` steps + the
  master lemma) and `double_left` (via `coord_double_left_generic'`,
  `char2_absorb`, and the doubling satellites `z3_knot`, `dbl_plus_neg`,
  `dbl_assoc_sq` — the ℤ/3 sub-line closing is `dbl_beta_generic` in four moves).

The earlier route to the same summit — `inv_absorb_core`, `base_change_hinv`,
`grounding_left`/`grounding_right`, `noncol_symm` — remains here, proven, as the
record of how the wall first bent.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

omit [ComplementedLattice L] in
/-- **Reverse parallelogram completion.**  `pc P' P (pc P P' Q m) m = Q`. -/
theorem reverse_completion {P P' Q m π : L}
    (hP : IsAtom P) (hP' : IsAtom P') (hQ : IsAtom Q)
    (hPP' : P ≠ P') (hPQ : P ≠ Q) (hP'Q : P' ≠ Q)
    (hP_le : P ≤ π) (hP'_le : P' ≤ π) (hQ_le : Q ≤ π)
    (hm_le : m ≤ π) (hm_cov : m ⋖ π)
    (hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m)
    (hP_not : ¬ P ≤ m) (hP'_not : ¬ P' ≤ m) (hQ_not : ¬ Q ≤ m)
    (hQ_not_PP' : ¬ Q ≤ P ⊔ P') :
    parallelogram_completion P' P (parallelogram_completion P P' Q m) m = Q := by
  set d := (P ⊔ P') ⊓ m with hd_def
  set e := (P ⊔ Q) ⊓ m with he_def
  set S := parallelogram_completion P P' Q m with hS_def
  have hd_le_m : d ≤ m := inf_le_right
  have he_le_m : e ≤ m := inf_le_right
  have hd_atom : IsAtom d :=
    line_meets_m_at_atom hP hP' hPP' (sup_le hP_le hP'_le) hm_le hm_cov hP_not
  have he_atom : IsAtom e :=
    line_meets_m_at_atom hP hQ hPQ (sup_le hP_le hQ_le) hm_le hm_cov hP_not
  have hd_ne_P : d ≠ P := fun h => hP_not (h ▸ hd_le_m)
  have hd_ne_Q : d ≠ Q := fun h => hQ_not (h ▸ hd_le_m)
  have hde_ne : d ≠ e := by
    intro h_eq
    have hd_le_PQ : d ≤ P ⊔ Q := h_eq ▸ (inf_le_left : e ≤ P ⊔ Q)
    have hd_le_P : d ≤ P := by
      have := le_inf (inf_le_left : d ≤ P ⊔ P') hd_le_PQ
      rwa [modular_intersection hP hP' hQ hPP' hPQ hP'Q hQ_not_PP'] at this
    have hPm : P ⊓ m = ⊥ :=
      (hP.le_iff.mp inf_le_left).resolve_right (fun h => hP_not (h ▸ inf_le_right))
    exact hd_atom.1 (le_antisymm (hPm ▸ le_inf hd_le_P hd_le_m) bot_le)
  have hS_atom : IsAtom S :=
    parallelogram_completion_atom hP hP' hQ hPP' hPQ hP'Q
      hP_le hP'_le hQ_le hm_le hm_cov hm_line hP_not hP'_not hQ_not hQ_not_PP'
  have hS_le_Qd : S ≤ Q ⊔ d := by rw [hS_def]; exact inf_le_left
  have hS_le_P'e : S ≤ P' ⊔ e := by rw [hS_def]; exact inf_le_right
  have hS_not_m : ¬ S ≤ m := by
    intro h
    have hS_le_d : S ≤ d := by
      calc S ≤ (Q ⊔ d) ⊓ m := le_inf hS_le_Qd h
        _ = d := line_direction hQ hQ_not hd_le_m
    have hS_eq_d : S = d := (hd_atom.le_iff.mp hS_le_d).resolve_left hS_atom.1
    have hd_le_P'e : d ≤ P' ⊔ e := hS_eq_d ▸ hS_le_P'e
    have hP'e_ne : P' ≠ e := fun h => hP'_not (h ▸ inf_le_right)
    have h_d_lt_de : d < d ⊔ e := lt_of_le_of_ne le_sup_left
      (fun h => hde_ne ((hd_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        he_atom.1).symm)
    have h_dx_le : d ⊔ e ≤ P' ⊔ e := sup_le hd_le_P'e le_sup_right
    have hd_cov : d ⋖ P' ⊔ e := line_covers_its_atoms hP' he_atom hP'e_ne hd_atom hd_le_P'e
    rcases hd_cov.eq_or_eq h_d_lt_de.le h_dx_le with h_eq | h_eq
    · exact absurd h_eq (ne_of_gt h_d_lt_de)
    · exact hP'_not (le_trans le_sup_left (h_eq ▸ sup_le hd_le_m he_le_m))
  have hS_ne_d : S ≠ d := fun h => hS_not_m (h ▸ hd_le_m)
  have hdP_eq_PP' : d ⊔ P = P ⊔ P' := by
    have hd_le_PP' : d ≤ P ⊔ P' := inf_le_left
    have hP_lt_dP : P < d ⊔ P := lt_of_le_of_ne le_sup_right
      (fun h => hd_ne_P ((hP.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left hd_atom.1))
    exact ((atom_covBy_join hP hP' hPP').eq_or_eq hP_lt_dP.le
      (sup_le hd_le_PP' le_sup_left)).resolve_left (ne_of_gt hP_lt_dP)
  have hP'_on_dP : P' ≤ d ⊔ P := hdP_eq_PP' ▸ le_sup_right
  have hS_ne_P' : S ≠ P' := by
    intro h
    have hP'_le_Qd : P' ≤ Q ⊔ d := h ▸ hS_le_Qd
    by_cases hlines : Q ⊔ d = d ⊔ P
    · exact hQ_not_PP' ((le_sup_left : Q ≤ Q ⊔ d).trans (hlines.trans hdP_eq_PP').le)
    · have hP'_le_inf : P' ≤ (Q ⊔ d) ⊓ (d ⊔ P) := le_inf hP'_le_Qd hP'_on_dP
      have hd_le_inf : d ≤ (Q ⊔ d) ⊓ (d ⊔ P) := le_inf le_sup_right le_sup_left
      have h_inf_lt : (Q ⊔ d) ⊓ (d ⊔ P) < Q ⊔ d := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h_eq
        have h_le : Q ⊔ d ≤ d ⊔ P := inf_eq_left.mp h_eq
        have h_d_lt_Qd : d < Q ⊔ d := by
          have := (atom_covBy_join hd_atom hQ hd_ne_Q).lt; rwa [sup_comm] at this
        have h_or := (atom_covBy_join hd_atom hP hd_ne_P).eq_or_eq h_d_lt_Qd.le h_le
        exact hlines (h_or.resolve_left (ne_of_gt h_d_lt_Qd))
      have h_pos : ⊥ < (Q ⊔ d) ⊓ (d ⊔ P) := lt_of_lt_of_le hd_atom.bot_lt hd_le_inf
      have h_inf_atom := line_height_two hQ hd_atom hd_ne_Q.symm h_pos h_inf_lt
      have h_inf_eq := ((h_inf_atom.le_iff.mp hd_le_inf).resolve_left hd_atom.1).symm
      have hd_ne_P' : d ≠ P' := fun hh => hP'_not (hh ▸ hd_le_m)
      exact hd_ne_P' ((hd_atom.le_iff.mp (h_inf_eq ▸ hP'_le_inf)).resolve_left hP'.1).symm
  have hP'S_le_π : P' ⊔ S ≤ π :=
    sup_le hP'_le (hS_le_Qd.trans (sup_le hQ_le (hd_le_m.trans hm_le)))
  have he0_atom : IsAtom ((P' ⊔ S) ⊓ m) :=
    line_meets_m_at_atom hP' hS_atom (Ne.symm hS_ne_P') hP'S_le_π hm_le hm_cov hP'_not
  have he0_le_e : (P' ⊔ S) ⊓ m ≤ e := by
    have h : (P' ⊔ S) ⊓ m ≤ (P' ⊔ e) ⊓ m := inf_le_inf_right m (sup_le le_sup_left hS_le_P'e)
    rwa [line_direction hP' hP'_not he_le_m] at h
  have he0_eq_e : (P' ⊔ S) ⊓ m = e := (he_atom.le_iff.mp he0_le_e).resolve_left he0_atom.1
  have hStepA : S ⊔ d = Q ⊔ d := by
    have hd_cov_QD : d ⋖ Q ⊔ d := by
      have h := atom_covBy_join hd_atom hQ hd_ne_Q; rwa [sup_comm] at h
    rcases hd_cov_QD.eq_or_eq (le_sup_right : d ≤ S ⊔ d) (sup_le hS_le_Qd le_sup_right) with h | h
    · exact absurd ((hd_atom.le_iff.mp (le_sup_left.trans h.le)).resolve_left hS_atom.1) hS_ne_d
    · exact h
  have hPm_eq_π : P ⊔ m = π := by
    have h_lt : m < P ⊔ m := lt_of_le_of_ne le_sup_right
      (fun h => hP_not (le_sup_left.trans h.symm.le))
    exact (hm_cov.eq_or_eq h_lt.le (sup_le hP_le hm_le)).resolve_left (ne_of_gt h_lt)
  have hPe_eq_PQ : P ⊔ e = P ⊔ Q := by
    have hPQ_le_π : P ⊔ Q ≤ π := sup_le hP_le hQ_le
    calc P ⊔ e = P ⊔ m ⊓ (P ⊔ Q) := by rw [he_def, inf_comm (P ⊔ Q) m]
      _ = (P ⊔ m) ⊓ (P ⊔ Q) := (sup_inf_assoc_of_le m (le_sup_left : P ≤ P ⊔ Q)).symm
      _ = π ⊓ (P ⊔ Q) := by rw [hPm_eq_π]
      _ = P ⊔ Q := inf_eq_right.mpr hPQ_le_π
  have hStepC : (Q ⊔ d) ⊓ (P ⊔ e) = Q := by
    rw [hPe_eq_PQ]
    have hQ_le_inf : Q ≤ (Q ⊔ d) ⊓ (P ⊔ Q) := le_inf le_sup_left le_sup_right
    have hQ_cov_Qd : Q ⋖ Q ⊔ d := atom_covBy_join hQ hd_atom (Ne.symm hd_ne_Q)
    rcases hQ_cov_Qd.eq_or_eq hQ_le_inf inf_le_left with h | h
    · exact h
    · exfalso
      have hQd_le_PQ : Q ⊔ d ≤ P ⊔ Q := inf_eq_left.mp h
      have hd_le_e : d ≤ e := by
        rw [he_def]; exact le_inf (le_sup_right.trans hQd_le_PQ) hd_le_m
      exact hde_ne ((he_atom.le_iff.mp hd_le_e).resolve_left hd_atom.1)
  have hd_symm : (P' ⊔ P) ⊓ m = d := by rw [sup_comm]
  have key : parallelogram_completion P' P S m = (S ⊔ d) ⊓ (P ⊔ e) := by
    show (S ⊔ (P' ⊔ P) ⊓ m) ⊓ (P ⊔ (P' ⊔ S) ⊓ m) = (S ⊔ d) ⊓ (P ⊔ e)
    rw [he0_eq_e, hd_symm]
  rw [key, hStepA, hStepC]

omit [ComplementedLattice L] [IsAtomistic L] in
/-- **Identity translation.**  `pc O O Q m = Q` for any point `Q` in the plane `π`
(the translation by the zero vector fixes everything).  Generalizes `C_O_eq_C`
(`Q = Γ.C`) and is the left-hand-side simplification of the char-2 doubling branch
(`pc O (a+a) C_c m = pc O O C_c m = C_c`). -/
theorem pc_id_left {O Q m π : L} (hO : IsAtom O) (hO_le : O ≤ π) (hO_not : ¬ O ≤ m)
    (hm_le : m ≤ π) (hm_cov : m ⋖ π) (hQ_le : Q ≤ π) :
    parallelogram_completion O O Q m = Q := by
  show (Q ⊔ (O ⊔ O) ⊓ m) ⊓ (O ⊔ (O ⊔ Q) ⊓ m) = Q
  have hOm : O ⊓ m = ⊥ :=
    (hO.le_iff.mp inf_le_left).resolve_right (fun h => hO_not (h ▸ inf_le_right))
  rw [sup_idem, hOm, sup_bot_eq]
  have hOm_eq_π : O ⊔ m = π := by
    have h_lt : m < O ⊔ m := lt_of_le_of_ne le_sup_right
      (fun h => hO_not (le_sup_left.trans h.symm.le))
    exact (hm_cov.eq_or_eq h_lt.le (sup_le hO_le hm_le)).resolve_left (ne_of_gt h_lt)
  have hstep : O ⊔ (O ⊔ Q) ⊓ m = O ⊔ Q := by
    calc O ⊔ (O ⊔ Q) ⊓ m = O ⊔ m ⊓ (O ⊔ Q) := by rw [inf_comm (O ⊔ Q) m]
      _ = (O ⊔ m) ⊓ (O ⊔ Q) := (sup_inf_assoc_of_le m (le_sup_left : O ≤ O ⊔ Q)).symm
      _ = π ⊓ (O ⊔ Q) := by rw [hOm_eq_π]
      _ = O ⊔ Q := inf_eq_right.mpr (sup_le hO_le hQ_le)
  rw [hstep]; exact inf_eq_left.mpr le_sup_right

/-- The `C`-tower of `O` is `Γ.C` itself: `pc O O C m = C`.  Grounds `τ_a ∘ τ_{-a} = id`
(the composite translation's parameter is `a + (-a) = O`, whose completion is `Γ.C`). -/
theorem C_O_eq_C (Γ : CoordSystem L) :
    parallelogram_completion Γ.O Γ.O Γ.C (Γ.U ⊔ Γ.V) = Γ.C := by
  show (Γ.C ⊔ (Γ.O ⊔ Γ.O) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) = Γ.C
  have hOm : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
    (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
  rw [sup_idem, hOm, sup_bot_eq]
  have hE : (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.E := rfl
  rw [hE, CoordSystem.OE_eq_OC]
  exact inf_eq_left.mpr le_sup_right

/-- C-tower injectivity, in constructive/recover form: a good atom `x` on `l` is recovered
from its completion `C_x = pc O x C m` by `(C_x ⊔ E) ⊓ l = x`.  Extracted verbatim from the
local `recover` inside `coord_add_assoc`. -/
theorem recover_std (Γ : CoordSystem L) (x : L) (hx : IsAtom x) (hx_l : x ≤ Γ.O ⊔ Γ.U) :
    (parallelogram_completion Γ.O x Γ.C (Γ.U ⊔ Γ.V) ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = x := by
  set l := Γ.O ⊔ Γ.U with hl
  set m := Γ.U ⊔ Γ.V with hm
  set q := Γ.U ⊔ Γ.C with hq
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hE_inf_l : Γ.E ⊓ l = ⊥ :=
    (Γ.hE_atom.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hE_not_l (h ▸ inf_le_right))
  suffices h_eq : parallelogram_completion Γ.O x Γ.C m ⊔ Γ.E = x ⊔ Γ.E by
    rw [h_eq, sup_inf_assoc_of_le Γ.E hx_l, hE_inf_l, sup_bot_eq]
  apply le_antisymm
  · exact sup_le (show parallelogram_completion Γ.O x Γ.C m ≤ x ⊔ Γ.E from
      inf_le_right) le_sup_right
  · apply sup_le _ le_sup_right
    have h_mod : parallelogram_completion Γ.O x Γ.C m ⊔ Γ.E =
        ((Γ.C ⊔ (Γ.O ⊔ x) ⊓ m) ⊔ Γ.E) ⊓ (x ⊔ Γ.E) := by
      show (Γ.C ⊔ (Γ.O ⊔ x) ⊓ m) ⊓ (x ⊔ Γ.E) ⊔ Γ.E =
           ((Γ.C ⊔ (Γ.O ⊔ x) ⊓ m) ⊔ Γ.E) ⊓ (x ⊔ Γ.E)
      have := sup_inf_assoc_of_le (Γ.C ⊔ (Γ.O ⊔ x) ⊓ m)
        (le_sup_right : Γ.E ≤ x ⊔ Γ.E)
      rw [sup_comm] at this
      rw [sup_comm Γ.E _] at this
      exact this.symm
    rw [h_mod]
    apply le_inf _ le_sup_left
    by_cases hx_O : x = Γ.O
    · subst hx_O
      have hC_ne_E : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
      have hCE_eq_OC : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
        have hCE_le : Γ.C ⊔ Γ.E ≤ Γ.C ⊔ Γ.O :=
          (sup_comm Γ.O Γ.C) ▸ (sup_le le_sup_right Γ.hE_le_OC : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C)
        have hC_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
          (fun h => hC_ne_E ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            Γ.hE_atom.1).symm)
        have := ((atom_covBy_join Γ.hC Γ.hO (fun h => Γ.hC_not_l (h ▸ le_sup_left))).eq_or_eq
          hC_lt.le hCE_le).resolve_left (ne_of_gt hC_lt)
        rw [sup_comm Γ.C Γ.O] at this; exact this
      calc Γ.O ≤ Γ.O ⊔ Γ.C := le_sup_left
        _ = Γ.C ⊔ Γ.E := hCE_eq_OC.symm
        _ ≤ (Γ.C ⊔ (Γ.O ⊔ Γ.O) ⊓ m) ⊔ Γ.E :=
            sup_le_sup_right (le_sup_left : Γ.C ≤ Γ.C ⊔ (Γ.O ⊔ Γ.O) ⊓ m) Γ.E
    · have hOx_eq_l : Γ.O ⊔ x = l := by
        have hO_lt : Γ.O < Γ.O ⊔ x := by
          apply lt_of_le_of_ne le_sup_left; intro h
          have hx_le_O : x ≤ Γ.O := le_sup_right.trans (le_of_eq h.symm)
          exact hx_O (le_antisymm hx_le_O
            (Γ.hO.le_iff.mp hx_le_O |>.resolve_left hx.1 ▸ le_refl _))
        exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
          (sup_le le_sup_left hx_l)).resolve_left (ne_of_gt hO_lt)
      rw [hOx_eq_l, Γ.l_inf_m_eq_U]
      have hqm : q ⊓ m = Γ.U := by
        show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
        rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
        have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
          (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
        rw [this, sup_bot_eq]
      have hq_covBy_π : q ⋖ π := by
        have h_inf : m ⊓ q ⋖ m := by
          rw [inf_comm, hqm]
          exact atom_covBy_join Γ.hU Γ.hV (fun h => Γ.hV_off (h ▸ le_sup_right))
        have hmq : m ⊔ q = π := by
          have : m ⊔ q = m ⊔ Γ.C := by
            show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
            rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
          rw [this]
          exact (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
            (sup_le hm_le_π Γ.hC_plane)).resolve_left
            (ne_of_gt (lt_of_le_of_ne le_sup_left
              (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
        have h1 := covBy_sup_of_inf_covBy_left h_inf; rwa [hmq] at h1
      have hqE_eq_π : q ⊔ Γ.E = π := by
        have hE_not_q : ¬ Γ.E ≤ q := fun hle =>
          Γ.hEU ((Γ.hU.le_iff.mp (hqm ▸ le_inf hle Γ.hE_on_m)).resolve_left Γ.hE_atom.1)
        have hq_lt : q < q ⊔ Γ.E := lt_of_le_of_ne le_sup_left
          (fun h => hE_not_q (le_sup_right.trans h.symm.le))
        exact (hq_covBy_π.eq_or_eq hq_lt.le
          (sup_le (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
            (Γ.hE_on_m.trans hm_le_π))).resolve_left (ne_of_gt hq_lt)
      calc x ≤ l := hx_l
        _ ≤ π := le_sup_left
        _ = q ⊔ Γ.E := hqE_eq_π.symm
        _ = (Γ.C ⊔ Γ.U) ⊔ Γ.E := by
            show (Γ.U ⊔ Γ.C) ⊔ Γ.E = (Γ.C ⊔ Γ.U) ⊔ Γ.E; rw [sup_comm Γ.U Γ.C]

/-- **Diagonal translation identity.**  `coord_add Γ a a = pc Γ.C C_a a m`, where
`C_a = pc Γ.O a Γ.C m`.  This is `coord_add_eq_translation` specialized to `b = a`;
the only use of `a ≠ b` in the generic proof is the terminal `coord_add_comm`, which
here is a `sup_comm` (`coord_add Γ a a` is literally symmetric). -/
theorem coord_add_eq_translation_diag (Γ : CoordSystem L)
    (a : L) (ha : IsAtom a)
    (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    let C' := parallelogram_completion Γ.O a Γ.C (Γ.U ⊔ Γ.V)
    coord_add Γ a a = parallelogram_completion Γ.C C' a (Γ.U ⊔ Γ.V) := by
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have ha_ne_E : a ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ ha_on)
  have hUC_inf_m : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U :=
    modular_intersection Γ.hU Γ.hC Γ.hV hUC hUV
      (fun h => Γ.hC_not_m (h ▸ le_sup_right))
      (fun hle => Γ.hC_not_m (((atom_covBy_join Γ.hU Γ.hC hUC).eq_or_eq
        (atom_covBy_join Γ.hU Γ.hV hUV).lt.le (sup_le le_sup_left hle)).resolve_left
        (ne_of_gt (atom_covBy_join Γ.hU Γ.hV hUV).lt) ▸ le_sup_right))
  have hOa_eq_l : Γ.O ⊔ a = Γ.O ⊔ Γ.U := by
    have hO_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_of_le_of_eq le_sup_right h.symm)).resolve_left ha.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt hO_lt)
  have hC'_simp : parallelogram_completion Γ.O a Γ.C (Γ.U ⊔ Γ.V) =
      (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := by
    show (Γ.C ⊔ (Γ.O ⊔ a) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (a ⊔ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) =
      (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)
    rw [hOa_eq_l, Γ.l_inf_m_eq_U, sup_comm Γ.C Γ.U]; rfl
  show coord_add Γ a a =
    parallelogram_completion Γ.C (parallelogram_completion Γ.O a Γ.C (Γ.U ⊔ Γ.V)) a (Γ.U ⊔ Γ.V)
  rw [hC'_simp]
  have hCE_eq_CO : Γ.C ⊔ Γ.E = Γ.C ⊔ Γ.O := by
    have hC_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hCE ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_atom.1).symm)
    exact ((atom_covBy_join Γ.hC Γ.hO hOC.symm).eq_or_eq hC_lt.le
      (sup_le le_sup_left (Γ.hE_le_OC.trans (sup_comm Γ.O Γ.C).le))).resolve_left
      (ne_of_gt hC_lt)
  have hC_join_C' : Γ.C ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) = Γ.U ⊔ Γ.C := by
    apply le_antisymm (sup_le le_sup_right inf_le_left)
    have haEC_ge_UC : Γ.U ⊔ Γ.C ≤ a ⊔ Γ.E ⊔ Γ.C := by
      suffices Γ.U ≤ a ⊔ Γ.E ⊔ Γ.C from sup_le this le_sup_right
      calc Γ.U ≤ Γ.O ⊔ Γ.U := le_sup_right
        _ = Γ.O ⊔ a := hOa_eq_l.symm
        _ ≤ a ⊔ Γ.E ⊔ Γ.C := sup_le
            ((le_of_le_of_eq (le_sup_right : Γ.O ≤ Γ.C ⊔ Γ.O) hCE_eq_CO.symm).trans
              (sup_le le_sup_right (le_sup_right.trans le_sup_left)))
            (le_sup_left.trans le_sup_left)
    calc Γ.U ⊔ Γ.C
        ≤ (Γ.C ⊔ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.C) := le_inf
          (haEC_ge_UC.trans (show a ⊔ Γ.E ⊔ Γ.C = Γ.C ⊔ (a ⊔ Γ.E) from by ac_rfl).le) le_rfl
      _ = Γ.C ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) :=
          sup_inf_assoc_of_le (a ⊔ Γ.E) (le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C)
      _ = Γ.C ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) := by rw [inf_comm]
  have hRHS_dir : (Γ.C ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
    rw [hC_join_C', hUC_inf_m]
  have hbU_eq_l : a ⊔ Γ.U = Γ.O ⊔ Γ.U := by
    have hU_lt : Γ.U < Γ.U ⊔ a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_U ((Γ.hU.le_iff.mp (le_of_le_of_eq le_sup_right h.symm)).resolve_left ha.1))
    calc a ⊔ Γ.U = Γ.U ⊔ a := sup_comm _ _
      _ = Γ.U ⊔ Γ.O := ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq hU_lt.le
          (sup_le le_sup_left (ha_on.trans (sup_comm Γ.O Γ.U).le))).resolve_left (ne_of_gt hU_lt)
      _ = Γ.O ⊔ Γ.U := sup_comm _ _
  show ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) =
    (a ⊔ (Γ.C ⊔ (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) ⊓ (Γ.U ⊔ Γ.V)) ⊓
    ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ⊔ (Γ.C ⊔ a) ⊓ (Γ.U ⊔ Γ.V))
  rw [hRHS_dir, hbU_eq_l, sup_comm Γ.C a, inf_comm (Γ.O ⊔ Γ.U)]
  show ((a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) ⊔ (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C)) ⊓ (Γ.O ⊔ Γ.U) =
    ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ Γ.U)
  rw [inf_comm (Γ.U ⊔ Γ.C) (a ⊔ Γ.E), sup_comm ((a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C))]

/-- **Fresh general-position auxiliary point for the doubling case.**

Given two distinct good atoms `a, d` on the coordinate line `l = Γ.O ⊔ Γ.U`, the
perspectivity image `P = (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C)` of `d` from `Γ.E` onto the line
`a ⊔ Γ.C` is a non-degenerate auxiliary point: it is an atom, lies in the plane
`π`, lies on `a ⊔ Γ.C`, and is off each of the three distinguished lines
`l = Γ.O ⊔ Γ.U`, `m = Γ.U ⊔ Γ.V`, `q = Γ.U ⊔ Γ.C`.

This is the `b ↦ d` reparametrization of the auxiliary point built inside
`coord_add_assoc`'s β-step; taking `d` distinct from `a` is exactly what stops the
collapse `(a ⊔ Γ.E) ⊓ (a ⊔ Γ.C) = a` that happens at `b = a`. -/
theorem dbl_aux_point (Γ : CoordSystem L) (a d : L)
    (ha : IsAtom a) (hd : IsAtom d)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hd_on : d ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hd_ne_O : d ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hd_ne_U : d ≠ Γ.U)
    (had : a ≠ d) :
    IsAtom ((d ⊔ Γ.E) ⊓ (a ⊔ Γ.C)) ∧
    (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ∧
    ¬ (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ Γ.O ⊔ Γ.U ∧
    ¬ (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ Γ.U ⊔ Γ.V ∧
    ¬ (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ Γ.U ⊔ Γ.C ∧
    (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ a ⊔ Γ.C := by
  set l := Γ.O ⊔ Γ.U with hl
  set m := Γ.U ⊔ Γ.V with hm
  set q := Γ.U ⊔ Γ.C with hq
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)
  have hd_ne_E : d ≠ Γ.E := fun h => CoordSystem.hE_not_l (h ▸ hd_on)
  have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ CoordSystem.hE_on_m)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hE_not_aC : ¬ Γ.E ≤ a ⊔ Γ.C := by
    intro hle
    have hCE_le : Γ.C ⊔ Γ.E ≤ a ⊔ Γ.C := sup_le le_sup_right hle
    have hE_le_CO : Γ.E ≤ Γ.C ⊔ Γ.O := sup_comm Γ.O Γ.C ▸ CoordSystem.hE_le_OC
    have h_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hCE ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have h_CE : Γ.C ⊔ Γ.E = Γ.C ⊔ Γ.O :=
      ((atom_covBy_join Γ.hC Γ.hO hOC.symm).eq_or_eq h_lt.le
        (sup_le le_sup_left hE_le_CO)).resolve_left (ne_of_gt h_lt)
    have hO_le_aC : Γ.O ≤ a ⊔ Γ.C :=
      calc Γ.O ≤ Γ.C ⊔ Γ.O := le_sup_right
        _ = Γ.C ⊔ Γ.E := h_CE.symm
        _ ≤ a ⊔ Γ.C := hCE_le
    have hO_le : Γ.O ≤ a := by
      have h := le_inf hO_le_aC (show Γ.O ≤ l from le_sup_left)
      rwa [inf_comm, sup_comm, inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on] at h
    exact ha_ne_O ((ha.le_iff.mp hO_le).resolve_left Γ.hO.1).symm
  have haCE_eq_π : (a ⊔ Γ.C) ⊔ Γ.E = π := by
    have haC_le_π : a ⊔ Γ.C ≤ π := sup_le (ha_on.trans le_sup_left) Γ.hC_plane
    have haC_ne_m : ¬ a ⊔ Γ.C ≤ m := fun h =>
      ha_ne_U (Γ.hU.le_iff.mp (Γ.l_inf_m_eq_U ▸ le_inf ha_on (le_sup_left.trans h))
        |>.resolve_left ha.1)
    have hD_ne_bot : (a ⊔ Γ.C) ⊓ m ≠ ⊥ := by
      rw [inf_comm]
      exact lines_meet_if_coplanar Γ.m_covBy_π haC_le_π haC_ne_m ha
        (lt_of_le_of_ne (le_sup_left : a ≤ a ⊔ Γ.C) (fun h => ha_ne_C
          ((ha.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm))
    have hD_ne_E : (a ⊔ Γ.C) ⊓ m ≠ Γ.E :=
      fun h => hE_not_aC (h ▸ inf_le_left)
    have hD_atom : IsAtom ((a ⊔ Γ.C) ⊓ m) :=
      line_height_two ha Γ.hC ha_ne_C (bot_lt_iff_ne_bot.mpr hD_ne_bot)
        (lt_of_le_of_ne inf_le_left (fun h => haC_ne_m (h ▸ inf_le_right)))
    have hDaE_eq_m : (a ⊔ Γ.C) ⊓ m ⊔ Γ.E = m := by
      have hE_cov : Γ.E ⋖ m := by
        show Γ.E ⋖ Γ.U ⊔ Γ.V
        have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
        rw [← Γ.EU_eq_m]; exact atom_covBy_join Γ.hE_atom Γ.hU CoordSystem.hEU
      have h_lt : Γ.E < (a ⊔ Γ.C) ⊓ m ⊔ Γ.E := lt_of_le_of_ne le_sup_right
        (fun h => hD_ne_E ((Γ.hE_atom.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left
          hD_atom.1))
      exact (hE_cov.eq_or_eq h_lt.le
        (sup_le (inf_le_right) CoordSystem.hE_on_m)).resolve_left (ne_of_gt h_lt)
    have hm_le : m ≤ (a ⊔ Γ.C) ⊔ Γ.E :=
      hDaE_eq_m ▸ sup_le (inf_le_left.trans le_sup_left) le_sup_right
    have ha_not_m : ¬ a ≤ m := fun h =>
      ha_ne_U (Γ.hU.le_iff.mp (Γ.l_inf_m_eq_U ▸ le_inf ha_on h) |>.resolve_left ha.1)
    have h_lt : m < (a ⊔ Γ.C) ⊔ Γ.E := lt_of_le_of_ne hm_le
      (fun h => ha_not_m ((le_sup_left : a ≤ a ⊔ Γ.C).trans le_sup_left |>.trans h.symm.le))
    exact (Γ.m_covBy_π.eq_or_eq h_lt.le
      (sup_le haC_le_π (CoordSystem.hE_on_m.trans hm_le_π))).resolve_left (ne_of_gt h_lt)
  have hdE_plane : d ⊔ Γ.E ≤ (a ⊔ Γ.C) ⊔ Γ.E :=
    sup_le (haCE_eq_π ▸ hd_on.trans le_sup_left) le_sup_right
  have hP_atom := perspect_atom Γ.hE_atom hd hd_ne_E ha Γ.hC ha_ne_C hE_not_aC hdE_plane
  refine ⟨hP_atom,
    inf_le_right.trans (sup_le (ha_on.trans le_sup_left) Γ.hC_plane), ?_, ?_, ?_, inf_le_right⟩
  ·
    intro hle
    have hPa : (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ a := by
      have h : (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ (a ⊔ Γ.C) ⊓ l := le_inf inf_le_right hle
      have h2 : (a ⊔ Γ.C) ⊓ l = a := by
        show (a ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = a
        rw [inf_comm]; exact (sup_comm Γ.C a ▸
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l ha_on : (Γ.O ⊔ Γ.U) ⊓ (a ⊔ Γ.C) = a)
      exact h.trans (le_of_eq h2)
    have ha_dE : a ≤ d ⊔ Γ.E :=
      (ha.le_iff.mp hPa).resolve_left hP_atom.1 ▸ inf_le_left
    have h_lb : (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ d) = d :=
      inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l hd_on
    have ha_d : a ≤ d := by
      have h : a ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ d) :=
        le_inf ha_on (show a ≤ Γ.E ⊔ d from (sup_comm Γ.E d).symm ▸ ha_dE)
      exact h_lb ▸ h
    exact had (hd.le_iff.mp ha_d |>.resolve_left ha.1)
  ·
    intro hle
    have hd_not_m : ¬ d ≤ m := fun hdm => hd_ne_U
      (Γ.hU.le_iff.mp (show d ≤ Γ.U from Γ.l_inf_m_eq_U ▸ le_inf hd_on hdm)
        |>.resolve_left hd.1)
    have hPE : (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ Γ.E := by
      have h : (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ (d ⊔ Γ.E) ⊓ m := le_inf inf_le_left hle
      have h2 : (d ⊔ Γ.E) ⊓ m = Γ.E := by
        show (d ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.V) = Γ.E
        rw [inf_comm]; exact (sup_comm Γ.E d ▸
          inf_sup_of_atom_not_le hd hd_not_m CoordSystem.hE_on_m :
          (Γ.U ⊔ Γ.V) ⊓ (d ⊔ Γ.E) = Γ.E)
      exact h.trans (le_of_eq h2)
    exact hE_not_aC ((Γ.hE_atom.le_iff.mp hPE).resolve_left hP_atom.1 ▸ inf_le_right)
  ·
    intro hle
    have ha_not_q : ¬ a ≤ q := fun haq => ha_ne_U
      (Γ.hU.le_iff.mp (show a ≤ Γ.U from by
        have h := le_inf ha_on haq
        have h2 : l ⊓ q = Γ.U := by
          show (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U
          rw [sup_comm Γ.O]
          have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
          exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm hUC hOC
            (fun hle => Γ.hC_not_l (sup_comm Γ.U Γ.O ▸ hle))
        exact h2 ▸ h) |>.resolve_left ha.1)
    have hPC : (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ Γ.C := by
      have h : (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≤ (a ⊔ Γ.C) ⊓ q := le_inf inf_le_right hle
      have h2 : (a ⊔ Γ.C) ⊓ q = Γ.C := by
        show (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C) = Γ.C
        rw [inf_comm]; exact (sup_comm Γ.C a ▸
          inf_sup_of_atom_not_le ha ha_not_q (le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C) :
          (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.C) = Γ.C)
      exact h.trans (le_of_eq h2)
    have hC_dE : Γ.C ≤ d ⊔ Γ.E :=
      (Γ.hC.le_iff.mp hPC).resolve_left hP_atom.1 ▸ inf_le_left
    have hOC_dE : Γ.O ⊔ Γ.C ≤ d ⊔ Γ.E := by
      have h_CE : Γ.C ⊔ Γ.E = Γ.C ⊔ Γ.O := by
        have h_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
          (fun h => hCE ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            Γ.hE_atom.1).symm)
        exact ((atom_covBy_join Γ.hC Γ.hO hOC.symm).eq_or_eq h_lt.le
          (sup_le le_sup_left (sup_comm Γ.O Γ.C ▸ CoordSystem.hE_le_OC))).resolve_left
          (ne_of_gt h_lt)
      calc Γ.O ⊔ Γ.C = Γ.C ⊔ Γ.O := sup_comm _ _
        _ = Γ.C ⊔ Γ.E := h_CE.symm
        _ ≤ d ⊔ Γ.E := sup_le hC_dE le_sup_right
    have h_lb : (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ d) = d :=
      inf_sup_of_atom_not_le Γ.hE_atom CoordSystem.hE_not_l hd_on
    have hO_d : Γ.O ≤ d := by
      have h : Γ.O ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.E ⊔ d) :=
        le_inf le_sup_left (show Γ.O ≤ Γ.E ⊔ d from
          (sup_comm Γ.E d).symm ▸ le_sup_left.trans hOC_dE)
      exact h_lb ▸ h
    exact hd_ne_O (hd.le_iff.mp hO_d |>.resolve_left Γ.hO.1).symm

/-- **Reusable β-step core** (the `a ≠ b`-free tail of `coord_add_assoc`'s β-step).

Given an auxiliary point `P` on `a ⊔ Γ.C` off `l`, `m`, `q`, together with the
one-step key-identity `h_ki_ab : τ_a(C_b) = C_{a+b}`, this proves the
translation-composition law `τ_{a+b}(C_c) = τ_a(τ_b(C_c))` on the `C`-tower of `c`.

It is verbatim the tail of `coord_add_assoc.h_beta_eq` (AssocCapstone lines 344–1459),
which uses `a ≠ b` nowhere — so it applies equally to the doubling case `b = a`,
provided a *fresh* `P` (from `dbl_aux_point`) and the doubling key-identity are
supplied. -/
theorem beta_step_core (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hs_ne_O : coord_add Γ a b ≠ Γ.O) (hs_ne_U : coord_add Γ a b ≠ Γ.U)
    (P : L) (hP_atom : IsAtom P) (hP_π : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_q : ¬ P ≤ Γ.U ⊔ Γ.C) (hP_le_aC : P ≤ a ⊔ Γ.C)
    (h_ki_ab : parallelogram_completion Γ.O a
        (parallelogram_completion Γ.O b Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_add Γ a b) Γ.C (Γ.U ⊔ Γ.V))
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    parallelogram_completion Γ.O (coord_add Γ a b)
        (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O a
          (parallelogram_completion Γ.O b
            (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) := by
    set l := Γ.O ⊔ Γ.U
    set m := Γ.U ⊔ Γ.V
    set q := Γ.U ⊔ Γ.C
    set π := Γ.O ⊔ Γ.U ⊔ Γ.V
    set s := coord_add Γ a b
    have hs_atom : IsAtom s := coord_add_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
    have hs_on : s ≤ l := by show coord_add Γ a b ≤ Γ.O ⊔ Γ.U; exact inf_le_right
    have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
    set C_c := parallelogram_completion Γ.O c Γ.C m
    set C_b := parallelogram_completion Γ.O b Γ.C m
    set C_s := parallelogram_completion Γ.O s Γ.C m
    set τ_s_P := parallelogram_completion Γ.O s P m
    set τ_b_P := parallelogram_completion Γ.O b P m
    set τ_a_τ_b_P := parallelogram_completion Γ.O a τ_b_P m
    set τ_s_C_c := parallelogram_completion Γ.O s C_c m
    set τ_b_C_c := parallelogram_completion Γ.O b C_c m
    set τ_a_τ_b_C_c := parallelogram_completion Γ.O a τ_b_C_c m

    have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    have hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m := fun x hx hle =>
      line_covers_its_atoms Γ.hU Γ.hV hUV hx hle
    have hm_cov : m ⋖ π := Γ.m_covBy_π

    have hOs_eq_l : Γ.O ⊔ s = l := by
      have h_lt : Γ.O < Γ.O ⊔ s := lt_of_le_of_ne le_sup_left
        (fun h => hs_ne_O (Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left
          hs_atom.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hs_on)).resolve_left (ne_of_gt h_lt)
    have hOb_eq_l : Γ.O ⊔ b = l := by
      have h_lt : Γ.O < Γ.O ⊔ b := lt_of_le_of_ne le_sup_left
        (fun h => hb_ne_O (Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left hb.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hb_on)).resolve_left (ne_of_gt h_lt)
    have hOa_eq_l : Γ.O ⊔ a = l := by
      have h_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
        (fun h => ha_ne_O (Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left ha.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt h_lt)

    have hs_not_m : ¬ s ≤ m := fun h => hs_ne_U (Γ.atom_on_both_eq_U hs_atom hs_on h)
    have hb_not_m : ¬ b ≤ m := fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on h)
    have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)

    have hO_ne_P : Γ.O ≠ P := fun h => hP_not_l (h ▸ le_sup_left)

    have hP_ne_C : P ≠ Γ.C := fun h => hP_not_q (h ▸ le_sup_right)

    have hC_not_OP : ¬ Γ.C ≤ Γ.O ⊔ P := by
      intro hle

      have hOC_le_OP : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ P := sup_le le_sup_left hle
      have hO_lt_OC : Γ.O < Γ.O ⊔ Γ.C := lt_of_le_of_ne le_sup_left
        (fun h => hOC (Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left Γ.hC.1 |>.symm))
      have hOC_eq_OP : Γ.O ⊔ Γ.C = Γ.O ⊔ P :=
        ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt_OC.le hOC_le_OP).resolve_left
          hO_lt_OC.ne'
      have hP_le_OC : P ≤ Γ.O ⊔ Γ.C := hOC_eq_OP.symm ▸ (le_sup_right : P ≤ Γ.O ⊔ P)

      have ha_not_OC : ¬ a ≤ Γ.O ⊔ Γ.C := by
        intro h
        have h1 : l ⊓ (Γ.C ⊔ Γ.O) = Γ.O :=
          inf_sup_of_atom_not_le Γ.hC Γ.hC_not_l (le_sup_left : Γ.O ≤ l)
        have h2 : a ≤ Γ.O := (le_inf ha_on (h.trans (sup_comm Γ.O Γ.C).le)).trans h1.le
        exact ha_ne_O (Γ.hO.le_iff.mp h2 |>.resolve_left ha.1)
      have h_int : (Γ.O ⊔ Γ.C) ⊓ (a ⊔ Γ.C) = Γ.C := by
        have := inf_sup_of_atom_not_le ha ha_not_OC (le_sup_right : Γ.C ≤ Γ.O ⊔ Γ.C)

        exact this
      exact hP_ne_C (Γ.hC.le_iff.mp ((le_inf hP_le_OC hP_le_aC).trans h_int.le)
        |>.resolve_left hP_atom.1)

    have ha_ne_C : a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ ha_on)

    have hl_cov_π : l ⋖ π := by
      have hV_inf_l : Γ.V ⊓ l = ⊥ :=
        (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
      show l ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
      rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = l ⊔ Γ.V from rfl, sup_comm l Γ.V]
      exact covBy_sup_of_inf_covBy_left (hV_inf_l ▸ Γ.hV.bot_covBy)
    have hOPC_span : Γ.O ⊔ P ⊔ Γ.C = π := by

      have hPC_eq_aC : P ⊔ Γ.C = a ⊔ Γ.C := by

        have hC_ne_a : Γ.C ≠ a := ha_ne_C.symm
        have hC_lt : Γ.C < Γ.C ⊔ P := lt_of_le_of_ne le_sup_left
          (fun h => hP_ne_C (Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left
            hP_atom.1))
        have hCP_le : Γ.C ⊔ P ≤ Γ.C ⊔ a := sup_le le_sup_left
          (hP_le_aC.trans (sup_comm a Γ.C).le)
        have hCP_eq_Ca : Γ.C ⊔ P = Γ.C ⊔ a :=
          ((atom_covBy_join Γ.hC ha hC_ne_a).eq_or_eq hC_lt.le hCP_le).resolve_left hC_lt.ne'
        calc P ⊔ Γ.C = Γ.C ⊔ P := sup_comm P Γ.C
          _ = Γ.C ⊔ a := hCP_eq_Ca
          _ = a ⊔ Γ.C := sup_comm Γ.C a
      rw [sup_assoc, hPC_eq_aC, ← sup_assoc, hOa_eq_l]

      have hlC_gt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
        (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
      exact (hl_cov_π.eq_or_eq hlC_gt.le
        (sup_le le_sup_left Γ.hC_plane)).resolve_left hlC_gt.ne'

    have hlq_eq_U : l ⊓ q = Γ.U := by
      show (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U
      rw [sup_comm Γ.O Γ.U]
      have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
      exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm hUC hOC
        (fun h => Γ.hC_not_l (le_trans h (by rw [sup_comm])))

    have hCs_atom : IsAtom C_s :=
      parallelogram_completion_atom Γ.hO hs_atom Γ.hC hs_ne_O.symm hOC
        (fun h => Γ.hC_not_l (h ▸ hs_on)) (le_sup_left.trans le_sup_left)
        (hs_on.trans le_sup_left) Γ.hC_plane hm_le_π hm_cov hm_line
        Γ.hO_not_m hs_not_m Γ.hC_not_m
        (fun h => Γ.hC_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
    have hCs_le_q : C_s ≤ q := by
      have : C_s ≤ Γ.C ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
      rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this
      exact this.trans (sup_comm Γ.C Γ.U ▸ le_refl q)

    have hCb_atom : IsAtom C_b :=
      parallelogram_completion_atom Γ.hO hb Γ.hC (fun h => hb_ne_O h.symm) hOC
        (fun h => Γ.hC_not_l (h ▸ hb_on)) (le_sup_left.trans le_sup_left)
        (hb_on.trans le_sup_left) Γ.hC_plane hm_le_π hm_cov hm_line
        Γ.hO_not_m hb_not_m Γ.hC_not_m
        (fun h => Γ.hC_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
    have hCb_le_q : C_b ≤ q := by
      have : C_b ≤ Γ.C ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
      rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this
      exact this.trans (sup_comm Γ.C Γ.U ▸ le_refl q)

    have hl_inf_PU : l ⊓ (P ⊔ Γ.U) = Γ.U :=
      inf_sup_of_atom_not_le hP_atom hP_not_l (le_sup_right : Γ.U ≤ l)
    have hPU_inf_q : (P ⊔ Γ.U) ⊓ q = Γ.U := by
      rw [inf_comm]; exact inf_sup_of_atom_not_le hP_atom hP_not_q (le_sup_left : Γ.U ≤ q)

    have hqm_eq_U : q ⊓ m = Γ.U := by
      show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
      rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
      rw [(Γ.hC.le_iff.mp inf_le_left).resolve_right
        (fun h => Γ.hC_not_m (h ▸ inf_le_right)), sup_bot_eq]
    have hCs_not_m : ¬ C_s ≤ m := by
      intro hCs_m
      have hCs_le_E : C_s ≤ Γ.E :=
        (le_inf (show C_s ≤ s ⊔ Γ.E from inf_le_right) hCs_m).trans
          (line_direction hs_atom hs_not_m CoordSystem.hE_on_m).le
      have hCsE : C_s = Γ.E := (Γ.hE_atom.le_iff.mp hCs_le_E).resolve_left hCs_atom.1
      exact CoordSystem.hEU (Γ.hU.le_iff.mp
        ((le_inf (hCsE ▸ hCs_le_q) (hCsE ▸ hCs_le_E |>.trans CoordSystem.hE_on_m)).trans
          hqm_eq_U.le) |>.resolve_left Γ.hE_atom.1)
    have hCb_not_m : ¬ C_b ≤ m := by
      intro hCb_m
      have hCb_le_E : C_b ≤ Γ.E :=
        (le_inf (show C_b ≤ b ⊔ Γ.E from inf_le_right) hCb_m).trans
          (line_direction hb hb_not_m CoordSystem.hE_on_m).le
      have hCbE : C_b = Γ.E := (Γ.hE_atom.le_iff.mp hCb_le_E).resolve_left hCb_atom.1
      exact CoordSystem.hEU (Γ.hU.le_iff.mp
        ((le_inf (hCbE ▸ hCb_le_q) (hCbE ▸ hCb_le_E |>.trans CoordSystem.hE_on_m)).trans
          hqm_eq_U.le) |>.resolve_left Γ.hE_atom.1)

    have hcp1 : (P ⊔ Γ.C) ⊓ m = (τ_s_P ⊔ C_s) ⊓ m := by

      have hs_ne_P : s ≠ P := fun h => hP_not_l (h ▸ hs_on)
      have hs_ne_C : s ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hs_on)

      have hs_ne_τ : s ≠ τ_s_P := by
        intro h_eq
        have hs_le_PU : s ≤ P ⊔ Γ.U := by
          have : τ_s_P ≤ P ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
          rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this; exact h_eq ▸ this
        exact hs_ne_U ((Γ.hU.le_iff.mp
          ((le_inf hs_on hs_le_PU).trans hl_inf_PU.le)).resolve_left hs_atom.1)

      have hs_ne_Cs : s ≠ C_s := by
        intro h_eq
        have : s ≤ l ⊓ q := le_inf hs_on (h_eq ▸ hCs_le_q)
        rw [hlq_eq_U] at this
        exact hs_ne_U ((Γ.hU.le_iff.mp this).resolve_left hs_atom.1)

      have hτ_ne_Cs : τ_s_P ≠ C_s := by
        intro h_eq
        have hτ_le_PU : τ_s_P ≤ P ⊔ Γ.U := by
          have : τ_s_P ≤ P ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
          rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this; exact this
        exact hCs_not_m ((Γ.hU.le_iff.mp
          ((le_inf (h_eq ▸ hτ_le_PU) hCs_le_q).trans hPU_inf_q.le)).resolve_left hCs_atom.1 ▸
          (le_sup_left : Γ.U ≤ m))
      exact cross_parallelism Γ.hO hs_atom hP_atom Γ.hC
        hs_ne_O.symm hO_ne_P hOC hP_ne_C
        hs_ne_τ hs_ne_Cs hτ_ne_Cs
        (le_sup_left.trans le_sup_left) (hs_on.trans le_sup_left) hP_π Γ.hC_plane
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hs_not_m hP_not_m Γ.hC_not_m
        (fun h => hP_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
        (fun h => Γ.hC_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
        hC_not_OP hOPC_span
        R hR hR_not h_irred

    have hcp2 : (P ⊔ Γ.C) ⊓ m = (τ_b_P ⊔ C_b) ⊓ m := by
      have hb_ne_P : b ≠ P := fun h => hP_not_l (h ▸ hb_on)
      have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)

      have hb_ne_τ : b ≠ τ_b_P := by
        intro h_eq
        have hb_le_PU : b ≤ P ⊔ Γ.U := by
          have : τ_b_P ≤ P ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
          rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this; exact h_eq ▸ this
        exact hb_ne_U ((Γ.hU.le_iff.mp
          ((le_inf hb_on hb_le_PU).trans hl_inf_PU.le)).resolve_left hb.1)

      have hb_ne_Cb : b ≠ C_b := by
        intro h_eq
        have : b ≤ l ⊓ q := le_inf hb_on (h_eq ▸ hCb_le_q)
        rw [hlq_eq_U] at this
        exact hb_ne_U ((Γ.hU.le_iff.mp this).resolve_left hb.1)

      have hτ_ne_Cb : τ_b_P ≠ C_b := by
        intro h_eq
        have hτ_le_PU : τ_b_P ≤ P ⊔ Γ.U := by
          have : τ_b_P ≤ P ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
          rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this; exact this
        exact hCb_not_m ((Γ.hU.le_iff.mp
          ((le_inf (h_eq ▸ hτ_le_PU) hCb_le_q).trans hPU_inf_q.le)).resolve_left hCb_atom.1 ▸
          (le_sup_left : Γ.U ≤ m))
      exact cross_parallelism Γ.hO hb hP_atom Γ.hC
        (fun h => hb_ne_O h.symm) hO_ne_P hOC hP_ne_C
        hb_ne_τ hb_ne_Cb hτ_ne_Cb
        (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) hP_π Γ.hC_plane
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hb_not_m hP_not_m Γ.hC_not_m
        (fun h => hP_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
        (fun h => Γ.hC_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
        hC_not_OP hOPC_span
        R hR hR_not h_irred

    have hτbP_atom : IsAtom τ_b_P :=
      parallelogram_completion_atom Γ.hO hb hP_atom
        (fun h => hb_ne_O h.symm) hO_ne_P (fun h => hP_not_l (h ▸ hb_on))
        (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) hP_π
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hb_not_m hP_not_m
        (fun h => hP_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
    have hτbP_le_PU : τ_b_P ≤ P ⊔ Γ.U := by
      have : τ_b_P ≤ P ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
      rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this; exact this
    have hτbP_le_bdOP : τ_b_P ≤ b ⊔ (Γ.O ⊔ P) ⊓ m :=
      inf_le_right

    have hτbP_not_q : ¬ τ_b_P ≤ q := by
      intro h
      have hτ_le_U : τ_b_P ≤ Γ.U := (le_inf hτbP_le_PU h).trans hPU_inf_q.le

      have hτbP_eq_U : τ_b_P = Γ.U :=
        (Γ.hU.le_iff.mp hτ_le_U).resolve_left hτbP_atom.1

      have hU_le_OP : Γ.U ≤ Γ.O ⊔ P := by
        have h1 : Γ.U ≤ (b ⊔ (Γ.O ⊔ P) ⊓ m) ⊓ m :=
          le_inf (hτbP_eq_U ▸ hτbP_le_bdOP) (le_sup_left : Γ.U ≤ m)
        rw [line_direction hb hb_not_m inf_le_right] at h1
        exact h1.trans inf_le_left

      have hl_le_OP : l ≤ Γ.O ⊔ P := sup_le le_sup_left hU_le_OP
      have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
        (fun h => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          Γ.hU.1 |>.symm))
      have hl_eq_OP : l = Γ.O ⊔ P :=
        ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt_l.le
          hl_le_OP).resolve_left (ne_of_gt hO_lt_l)
      exact hP_not_l (le_sup_right.trans (le_of_eq hl_eq_OP.symm))
    have hCb_ne_τbP : C_b ≠ τ_b_P := fun h => hτbP_not_q (h ▸ hCb_le_q)

    have hO_ne_τbP : Γ.O ≠ τ_b_P := by
      intro h
      exact Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
        (h ▸ hτbP_le_PU)).trans hl_inf_PU.le)).resolve_left Γ.hO.1)

    have hτbP_not_m : ¬ τ_b_P ≤ m := by
      intro h
      exact hτbP_not_q (((Γ.hU.le_iff.mp (by
        have h1 : τ_b_P ≤ (P ⊔ Γ.U) ⊓ m := le_inf hτbP_le_PU h
        rwa [sup_comm, sup_inf_assoc_of_le P (le_sup_left : Γ.U ≤ m),
          (hP_atom.le_iff.mp inf_le_left).resolve_right (fun h => hP_not_m (h ▸ inf_le_right)),
          sup_bot_eq] at h1)).resolve_left hτbP_atom.1).symm ▸ (le_sup_left : Γ.U ≤ q))

    have hτbP_π : τ_b_P ≤ π := hτbP_le_PU.trans
      (sup_le hP_π (le_sup_right.trans le_sup_left))

    have ha_ne_τbP : a ≠ τ_b_P := fun h => hτbP_not_q
      ((le_inf (h ▸ ha_on) hτbP_le_PU).trans hl_inf_PU.le |>.trans
        (le_sup_left : Γ.U ≤ q))

    have hτa_atom : IsAtom τ_a_τ_b_P :=
      parallelogram_completion_atom Γ.hO ha hτbP_atom
        (fun h => ha_ne_O h.symm) hO_ne_τbP ha_ne_τbP
        (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hτbP_π
        hm_le_π hm_cov hm_line
        Γ.hO_not_m ha_not_m hτbP_not_m
        (fun h => hτbP_not_q ((le_inf (h.trans (hOa_eq_l ▸ le_refl l))
          hτbP_le_PU).trans hl_inf_PU.le |>.trans (le_sup_left : Γ.U ≤ q)))

    have hcp3 : (τ_b_P ⊔ C_b) ⊓ m = (τ_a_τ_b_P ⊔ C_s) ⊓ m := by

      by_cases hCb_collinear : C_b ≤ Γ.O ⊔ τ_b_P
      ·
        set d' := (Γ.O ⊔ τ_b_P) ⊓ m

        have hd'_atom : IsAtom d' :=
          line_meets_m_at_atom Γ.hO hτbP_atom hO_ne_τbP
            (sup_le (le_sup_left.trans le_sup_left) hτbP_π)
            hm_le_π hm_cov Γ.hO_not_m

        have hτbP_lt : τ_b_P < τ_b_P ⊔ C_b := lt_of_le_of_ne le_sup_left
          (fun h => hCb_ne_τbP ((hτbP_atom.le_iff.mp (le_sup_right.trans
            (le_of_eq h.symm))).resolve_left hCb_atom.1))
        have hLHS_line : τ_b_P ⊔ C_b = Γ.O ⊔ τ_b_P :=
          ((sup_comm τ_b_P Γ.O ▸ atom_covBy_join hτbP_atom Γ.hO
            (fun h => hO_ne_τbP h.symm)).eq_or_eq hτbP_lt.le
            (sup_le le_sup_right hCb_collinear)).resolve_left (ne_of_gt hτbP_lt)

        have hO_ne_Cb : Γ.O ≠ C_b := by
          intro h; exact Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
            (h ▸ hCb_le_q)).trans hlq_eq_U.le)).resolve_left Γ.hO.1)
        have hOCb_eq : Γ.O ⊔ C_b = Γ.O ⊔ τ_b_P := by
          have hO_lt : Γ.O < Γ.O ⊔ C_b := lt_of_le_of_ne le_sup_left
            (fun h => hO_ne_Cb ((Γ.hO.le_iff.mp (le_sup_right.trans
              (le_of_eq h.symm))).resolve_left hCb_atom.1).symm)
          exact ((atom_covBy_join Γ.hO hτbP_atom hO_ne_τbP).eq_or_eq hO_lt.le
            (sup_le le_sup_left hCb_collinear)).resolve_left (ne_of_gt hO_lt)

        have hτa_le_ad' : τ_a_τ_b_P ≤ a ⊔ d' := by
          show τ_a_τ_b_P ≤ a ⊔ (Γ.O ⊔ τ_b_P) ⊓ m; exact inf_le_right

        have hCs_le_ad' : C_s ≤ a ⊔ d' := by
          rw [← h_ki_ab]; show parallelogram_completion Γ.O a C_b m ≤ a ⊔ d'
          show parallelogram_completion Γ.O a C_b m ≤ a ⊔ (Γ.O ⊔ τ_b_P) ⊓ m
          rw [← hOCb_eq]; exact inf_le_right

        have had'_dir : (a ⊔ d') ⊓ m = d' := line_direction ha ha_not_m inf_le_right

        have hRHS_le : (τ_a_τ_b_P ⊔ C_s) ⊓ m ≤ d' :=
          (inf_le_inf_right m (sup_le hτa_le_ad' hCs_le_ad')).trans (le_of_eq had'_dir)

        have hτa_ne_Cs : τ_a_τ_b_P ≠ C_s := by
          intro h_eq
          have hτa_le_τU : τ_a_τ_b_P ≤ τ_b_P ⊔ Γ.U := by
            have : τ_a_τ_b_P ≤ τ_b_P ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
            rwa [hOa_eq_l, Γ.l_inf_m_eq_U] at this
          have hτU_ne : τ_b_P ≠ Γ.U := fun h => hτbP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
          have hPU_ne : P ≠ Γ.U := fun h => hP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
          have hU_lt : Γ.U < τ_b_P ⊔ Γ.U := lt_of_le_of_ne le_sup_right
            (fun h => hτU_ne ((Γ.hU.le_iff.mp (le_sup_left.trans
              (le_of_eq h.symm))).resolve_left hτbP_atom.1))
          have hτU_eq_PU : τ_b_P ⊔ Γ.U = P ⊔ Γ.U :=
            ((sup_comm Γ.U P ▸ atom_covBy_join Γ.hU hP_atom hPU_ne.symm).eq_or_eq
              hU_lt.le (sup_le hτbP_le_PU le_sup_right)).resolve_left (ne_of_gt hU_lt)
          have hCs_le_U : C_s ≤ Γ.U := (le_inf (hτU_eq_PU ▸ h_eq ▸ hτa_le_τU)
            hCs_le_q).trans hPU_inf_q.le
          exact hCs_not_m (((Γ.hU.le_iff.mp hCs_le_U).resolve_left hCs_atom.1).symm ▸
            (le_sup_left : Γ.U ≤ m))

        have hCs_lt : C_s < τ_a_τ_b_P ⊔ C_s := lt_of_le_of_ne le_sup_right
          (fun h => hτa_ne_Cs ((hCs_atom.le_iff.mp (le_sup_left.trans
            (le_of_eq h.symm))).resolve_left hτa_atom.1))
        have hRHS_ne : m ⊓ (τ_a_τ_b_P ⊔ C_s) ≠ ⊥ :=
          lines_meet_if_coplanar hm_cov
            (sup_le (hτa_le_ad'.trans (sup_le (ha_on.trans le_sup_left)
              (inf_le_right.trans hm_le_π))) (hCs_le_ad'.trans (sup_le
              (ha_on.trans le_sup_left) (inf_le_right.trans hm_le_π))))
            (fun h => hCs_not_m (le_sup_right.trans h)) hCs_atom hCs_lt

        have hRHS_eq : (τ_a_τ_b_P ⊔ C_s) ⊓ m = d' :=
          (hd'_atom.le_iff.mp hRHS_le).resolve_left (inf_comm m _ ▸ hRHS_ne)
        rw [hLHS_line]; exact hRHS_eq.symm
      ·

        have hO_ne_Cb : Γ.O ≠ C_b := by
          intro h; exact Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
            (h ▸ hCb_le_q)).trans hlq_eq_U.le)).resolve_left Γ.hO.1)

        have ha_ne_Cb : a ≠ C_b := fun h => ha_ne_U ((Γ.hU.le_iff.mp
          ((le_inf ha_on (h ▸ hCb_le_q)).trans hlq_eq_U.le)).resolve_left ha.1)

        have hq_covBy_π : q ⋖ π := by
          have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
          have h_inf : m ⊓ q ⋖ m := by
            rw [inf_comm, hqm_eq_U]; exact atom_covBy_join Γ.hU Γ.hV hUV
          have h1 := covBy_sup_of_inf_covBy_left h_inf
          have hmq : m ⊔ q = m ⊔ Γ.C := by
            show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
            rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
          have hmC : m ⊔ Γ.C = π :=
            (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
              (sup_le hm_le_π Γ.hC_plane)).resolve_left
              (ne_of_gt (lt_of_le_of_ne le_sup_left
                (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
          rwa [hmq, hmC] at h1

        have hO_not_q : ¬ Γ.O ≤ q := fun h =>
          Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
            h).trans hlq_eq_U.le)).resolve_left Γ.hO.1)
        have hW_atom : IsAtom ((Γ.O ⊔ τ_b_P) ⊓ q) :=
          line_meets_m_at_atom Γ.hO hτbP_atom hO_ne_τbP
            (sup_le (le_sup_left.trans le_sup_left) hτbP_π)
            (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane) hq_covBy_π
            hO_not_q
        have hW_ne_Cb : (Γ.O ⊔ τ_b_P) ⊓ q ≠ C_b := fun h =>
          hCb_collinear (h ▸ inf_le_left)

        have hspan : Γ.O ⊔ τ_b_P ⊔ C_b = π := by

          have h_mod : (C_b ⊔ (Γ.O ⊔ τ_b_P)) ⊓ q = C_b ⊔ ((Γ.O ⊔ τ_b_P) ⊓ q) :=
            sup_inf_assoc_of_le (Γ.O ⊔ τ_b_P) hCb_le_q

          have hCb_lt : C_b < C_b ⊔ (Γ.O ⊔ τ_b_P) ⊓ q := by
            apply lt_of_le_of_ne le_sup_left; intro h
            have hW_le : (Γ.O ⊔ τ_b_P) ⊓ q ≤ C_b := le_sup_right.trans (le_of_eq h.symm)
            exact hW_ne_Cb ((hCb_atom.le_iff.mp hW_le).resolve_left hW_atom.1)
          have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
          have hCb_covBy : C_b ⋖ q := line_covers_its_atoms Γ.hU Γ.hC hUC hCb_atom hCb_le_q
          have hCbW_eq_q : C_b ⊔ (Γ.O ⊔ τ_b_P) ⊓ q = q :=
            (hCb_covBy.eq_or_eq hCb_lt.le (sup_le hCb_le_q inf_le_right)).resolve_left
              (ne_of_gt hCb_lt)
          have hq_le : q ≤ Γ.O ⊔ τ_b_P ⊔ C_b := by
            have := inf_eq_right.mp (h_mod.trans hCbW_eq_q); rwa [sup_comm] at this
          have hlC_le : l ⊔ Γ.C ≤ Γ.O ⊔ τ_b_P ⊔ C_b :=
            sup_le (sup_le (le_sup_left.trans le_sup_left)
              ((le_sup_left : Γ.U ≤ q).trans hq_le))
              ((le_sup_right : Γ.C ≤ q).trans hq_le)
          have hl_lt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
          have hlC_eq : l ⊔ Γ.C = π :=
            (hl_cov_π.eq_or_eq hl_lt.le (sup_le le_sup_left
              Γ.hC_plane)).resolve_left (ne_of_gt hl_lt)
          exact le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left) hτbP_π)
            (hCb_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)))
            (le_of_eq hlC_eq.symm |>.trans hlC_le)

        have hCb_not_Oa : ¬ C_b ≤ Γ.O ⊔ a := by
          intro h; exact hCb_not_m ((Γ.hU.le_iff.mp ((le_inf (h.trans (hOa_eq_l ▸ le_refl l))
            hCb_le_q).trans hlq_eq_U.le)).resolve_left hCb_atom.1 ▸ (le_sup_left : Γ.U ≤ m))
        have ha_ne_τa : a ≠ τ_a_τ_b_P := by
          intro h_eq
          have hτa_le_τU : τ_a_τ_b_P ≤ τ_b_P ⊔ Γ.U := by
            have : τ_a_τ_b_P ≤ τ_b_P ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
            rwa [hOa_eq_l, Γ.l_inf_m_eq_U] at this
          rw [← h_eq] at hτa_le_τU
          exact ha_ne_U ((Γ.hU.le_iff.mp ((le_inf ha_on
            (hτa_le_τU.trans (sup_le hτbP_le_PU le_sup_right))).trans
            hl_inf_PU.le)).resolve_left ha.1)
        have ha_ne_Cs_cp : a ≠ parallelogram_completion Γ.O a C_b m := by
          rw [h_ki_ab]; exact fun h => ha_ne_U ((Γ.hU.le_iff.mp
            ((le_inf ha_on (h ▸ hCs_le_q)).trans hlq_eq_U.le)).resolve_left ha.1)
        have hτa_ne_Cs_cp : τ_a_τ_b_P ≠ parallelogram_completion Γ.O a C_b m := by
          rw [h_ki_ab]
          intro h_eq
          have hτa_le_τU : τ_a_τ_b_P ≤ τ_b_P ⊔ Γ.U := by
            have : τ_a_τ_b_P ≤ τ_b_P ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
            rwa [hOa_eq_l, Γ.l_inf_m_eq_U] at this
          have hτU_ne : τ_b_P ≠ Γ.U := fun h => hτbP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
          have hPU_ne : P ≠ Γ.U := fun h => hP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
          have hU_lt : Γ.U < τ_b_P ⊔ Γ.U := lt_of_le_of_ne le_sup_right
            (fun h => hτU_ne ((Γ.hU.le_iff.mp (le_sup_left.trans
              (le_of_eq h.symm))).resolve_left hτbP_atom.1))
          have hτU_eq_PU : τ_b_P ⊔ Γ.U = P ⊔ Γ.U :=
            ((sup_comm Γ.U P ▸ atom_covBy_join Γ.hU hP_atom hPU_ne.symm).eq_or_eq
              hU_lt.le (sup_le hτbP_le_PU le_sup_right)).resolve_left (ne_of_gt hU_lt)
          have hCs_le_U : C_s ≤ Γ.U := (le_inf (hτU_eq_PU ▸ h_eq ▸ hτa_le_τU)
            hCs_le_q).trans hPU_inf_q.le
          exact hCs_not_m (((Γ.hU.le_iff.mp hCs_le_U).resolve_left hCs_atom.1).symm ▸
            (le_sup_left : Γ.U ≤ m))

        have hcp3_raw := cross_parallelism Γ.hO ha hτbP_atom hCb_atom
          (fun h => ha_ne_O h.symm) hO_ne_τbP hO_ne_Cb (fun h => hCb_ne_τbP h.symm)
          ha_ne_τa ha_ne_Cs_cp hτa_ne_Cs_cp
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hτbP_π
          (hCb_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m hτbP_not_m hCb_not_m
          (fun h => hτbP_not_q ((le_inf (h.trans (hOa_eq_l ▸ le_refl l))
            hτbP_le_PU).trans hl_inf_PU.le |>.trans (le_sup_left : Γ.U ≤ q)))
          hCb_not_Oa
          hCb_collinear
          hspan
          R hR hR_not h_irred
        rw [h_ki_ab] at hcp3_raw; exact hcp3_raw

    have h_dir1 : (τ_s_P ⊔ C_s) ⊓ m = (τ_a_τ_b_P ⊔ C_s) ⊓ m :=
      hcp1.symm.trans (hcp2.trans hcp3)

    have hτsP_atom : IsAtom τ_s_P :=
      parallelogram_completion_atom Γ.hO hs_atom hP_atom
        (fun h => hs_ne_O h.symm) hO_ne_P (fun h => hP_not_l (h ▸ hs_on))
        (le_sup_left.trans le_sup_left) (hs_on.trans le_sup_left) hP_π
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hs_not_m hP_not_m
        (fun h => hP_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
    have hτsP_le_PU : τ_s_P ≤ P ⊔ Γ.U := by
      have : τ_s_P ≤ P ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
      rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this; exact this
    have hτa_le_PU : τ_a_τ_b_P ≤ P ⊔ Γ.U := by
      have h1 : τ_a_τ_b_P ≤ τ_b_P ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
      rw [hOa_eq_l, Γ.l_inf_m_eq_U] at h1
      exact h1.trans (sup_le hτbP_le_PU le_sup_right)
    have hτsP_ne_Cs : τ_s_P ≠ C_s := by
      intro h; exact hCs_not_m (((Γ.hU.le_iff.mp ((le_inf (h ▸ hτsP_le_PU) hCs_le_q).trans
        hPU_inf_q.le)).resolve_left hCs_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
    have hτa_ne_Cs : τ_a_τ_b_P ≠ C_s := by
      intro h; exact hCs_not_m (((Γ.hU.le_iff.mp ((le_inf (h ▸ hτa_le_PU) hCs_le_q).trans
        hPU_inf_q.le)).resolve_left hCs_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
    have hCs_not_PU : ¬ C_s ≤ P ⊔ Γ.U := by
      intro h; exact hCs_not_m (((Γ.hU.le_iff.mp ((le_inf h hCs_le_q).trans
        hPU_inf_q.le)).resolve_left hCs_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
    have hP_agree : τ_s_P = τ_a_τ_b_P := by

      have hτsP_π : τ_s_P ≤ π := hτsP_le_PU.trans (sup_le hP_π (le_sup_right.trans le_sup_left))
      have hCs_π : C_s ≤ π := hCs_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
      have hd_atom : IsAtom ((τ_s_P ⊔ C_s) ⊓ m) := by
        rw [sup_comm]; exact line_meets_m_at_atom hCs_atom hτsP_atom
          (fun h => hτsP_ne_Cs h.symm) (sup_le hCs_π hτsP_π) hm_le_π hm_cov hCs_not_m
      have hd_ne_Cs : (τ_s_P ⊔ C_s) ⊓ m ≠ C_s := fun h =>
        hCs_not_m (h ▸ inf_le_right)

      have hCs_covBy_1 : C_s ⋖ τ_s_P ⊔ C_s :=
        sup_comm C_s τ_s_P ▸ atom_covBy_join hCs_atom hτsP_atom hτsP_ne_Cs.symm
      have hCs_lt_d : C_s < C_s ⊔ (τ_s_P ⊔ C_s) ⊓ m := lt_of_le_of_ne le_sup_left
        (fun h => hd_ne_Cs ((hCs_atom.le_iff.mp (le_sup_right.trans
          (le_of_eq h.symm))).resolve_left hd_atom.1))
      have hCsd_eq_1 : C_s ⊔ (τ_s_P ⊔ C_s) ⊓ m = τ_s_P ⊔ C_s :=
        (hCs_covBy_1.eq_or_eq hCs_lt_d.le (sup_le le_sup_right inf_le_left)).resolve_left
          (ne_of_gt hCs_lt_d)
      have hCs_covBy_2 : C_s ⋖ τ_a_τ_b_P ⊔ C_s :=
        sup_comm C_s τ_a_τ_b_P ▸ atom_covBy_join hCs_atom hτa_atom hτa_ne_Cs.symm
      have hd_le_2 : (τ_s_P ⊔ C_s) ⊓ m ≤ τ_a_τ_b_P ⊔ C_s := h_dir1 ▸ inf_le_left
      have hCs_lt_d2 : C_s < C_s ⊔ (τ_s_P ⊔ C_s) ⊓ m := hCs_lt_d
      have hCsd_eq_2 : C_s ⊔ (τ_s_P ⊔ C_s) ⊓ m = τ_a_τ_b_P ⊔ C_s :=
        (hCs_covBy_2.eq_or_eq hCs_lt_d2.le (sup_le le_sup_right hd_le_2)).resolve_left
          (ne_of_gt hCs_lt_d2)

      have hline_eq : τ_s_P ⊔ C_s = τ_a_τ_b_P ⊔ C_s := hCsd_eq_1.symm.trans hCsd_eq_2

      have hτa_on_line : τ_a_τ_b_P ≤ τ_s_P ⊔ C_s := hline_eq ▸ le_sup_left

      have hPU_ne : P ≠ Γ.U := fun h => hP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
      exact two_lines hτsP_atom hτa_atom hCs_atom hτsP_ne_Cs
        hτsP_le_PU hτa_le_PU hτa_on_line hCs_not_PU
        (line_covers_its_atoms hP_atom Γ.hU hPU_ne hτsP_atom hτsP_le_PU)

    have hOc_eq_l : Γ.O ⊔ c = l := by
      have h_lt : Γ.O < Γ.O ⊔ c := lt_of_le_of_ne le_sup_left
        (fun h => hc_ne_O (Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le) |>.resolve_left hc.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hc_on)).resolve_left (ne_of_gt h_lt)
    have hc_not_m : ¬ c ≤ m := fun h => hc_ne_U (Γ.atom_on_both_eq_U hc hc_on h)
    have hCc_atom : IsAtom C_c :=
      parallelogram_completion_atom Γ.hO hc Γ.hC (fun h => hc_ne_O h.symm) hOC
        (fun h => Γ.hC_not_l (h ▸ hc_on)) (le_sup_left.trans le_sup_left)
        (hc_on.trans le_sup_left) Γ.hC_plane hm_le_π hm_cov hm_line
        Γ.hO_not_m hc_not_m Γ.hC_not_m
        (fun h => Γ.hC_not_l (h.trans (hOc_eq_l ▸ le_refl l)))
    have hCc_le_q : C_c ≤ q := by
      have : C_c ≤ Γ.C ⊔ (Γ.O ⊔ c) ⊓ m := inf_le_left
      rw [hOc_eq_l, Γ.l_inf_m_eq_U] at this
      exact this.trans (sup_comm Γ.C Γ.U ▸ le_refl q)
    have hCc_not_m : ¬ C_c ≤ m := by
      intro hCc_m
      have hCc_le_E : C_c ≤ Γ.E :=
        (le_inf (show C_c ≤ c ⊔ Γ.E from inf_le_right) hCc_m).trans
          (line_direction hc hc_not_m CoordSystem.hE_on_m).le
      have hCcE : C_c = Γ.E := (Γ.hE_atom.le_iff.mp hCc_le_E).resolve_left hCc_atom.1
      exact CoordSystem.hEU (Γ.hU.le_iff.mp
        ((le_inf (hCcE ▸ hCc_le_q) (hCcE ▸ hCc_le_E |>.trans CoordSystem.hE_on_m)).trans
          hqm_eq_U.le) |>.resolve_left Γ.hE_atom.1)
    have hCc_π : C_c ≤ π := hCc_le_q.trans
      (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
    have hO_ne_Cc : Γ.O ≠ C_c := by
      intro h; exact Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
        (h ▸ hCc_le_q)).trans hlq_eq_U.le)).resolve_left Γ.hO.1)
    have hP_ne_Cc : P ≠ C_c := fun h => hP_not_q (h ▸ hCc_le_q)
    have hCc_not_l : ¬ C_c ≤ l := by
      intro h; exact hCc_not_m (((Γ.hU.le_iff.mp ((le_inf h hCc_le_q).trans
        hlq_eq_U.le)).resolve_left hCc_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))

    have hPU_ne : P ≠ Γ.U := fun h => hP_not_m (h ▸ (le_sup_left : Γ.U ≤ m))
    have hCc_not_PU : ¬ C_c ≤ P ⊔ Γ.U := by
      intro h; exact hCc_not_m (((Γ.hU.le_iff.mp ((le_inf h hCc_le_q).trans
        hPU_inf_q.le)).resolve_left hCc_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
    have hs_ne_Cc : s ≠ C_c := fun h => hs_ne_U ((Γ.hU.le_iff.mp ((le_inf hs_on
      (h ▸ hCc_le_q)).trans hlq_eq_U.le)).resolve_left hs_atom.1)
    have hb_ne_Cc : b ≠ C_c := fun h => hb_ne_U ((Γ.hU.le_iff.mp ((le_inf hb_on
      (h ▸ hCc_le_q)).trans hlq_eq_U.le)).resolve_left hb.1)

    have hτsCc_le_CcU : τ_s_C_c ≤ C_c ⊔ Γ.U := by
      have : τ_s_C_c ≤ C_c ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
      rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this; exact this
    have hτsCc_le_q : τ_s_C_c ≤ q :=
      hτsCc_le_CcU.trans (sup_le hCc_le_q (le_sup_left : Γ.U ≤ q))
    have hτsCc_atom : IsAtom τ_s_C_c :=
      parallelogram_completion_atom Γ.hO hs_atom hCc_atom hs_ne_O.symm hO_ne_Cc hs_ne_Cc
        (le_sup_left.trans le_sup_left) (hs_on.trans le_sup_left) hCc_π
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hs_not_m hCc_not_m
        (fun h => hCc_not_l (h.trans (hOs_eq_l ▸ le_refl l)))

    have hτbCc_le_CcU : τ_b_C_c ≤ C_c ⊔ Γ.U := by
      have : τ_b_C_c ≤ C_c ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
      rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this; exact this
    have hτbCc_le_q : τ_b_C_c ≤ q :=
      hτbCc_le_CcU.trans (sup_le hCc_le_q (le_sup_left : Γ.U ≤ q))

    have hτsCc_not_m : ¬ τ_s_C_c ≤ m := by
      intro h
      have hτsCc_eq_U : τ_s_C_c = Γ.U :=
        (Γ.hU.le_iff.mp ((le_inf hτsCc_le_q h).trans hqm_eq_U.le)).resolve_left hτsCc_atom.1
      have h1 : Γ.U ≤ s ⊔ (Γ.O ⊔ C_c) ⊓ m := by rw [← hτsCc_eq_U]; exact inf_le_right
      have hU_le_OCc : Γ.U ≤ Γ.O ⊔ C_c :=
        ((le_inf h1 (le_sup_left : Γ.U ≤ m)).trans
          (line_direction hs_atom hs_not_m inf_le_right).le).trans inf_le_left
      have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
        (fun h' => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
      have hl_eq : l = Γ.O ⊔ C_c :=
        ((atom_covBy_join Γ.hO hCc_atom hO_ne_Cc).eq_or_eq hO_lt_l.le
          (sup_le le_sup_left hU_le_OCc)).resolve_left hO_lt_l.ne'
      exact hCc_not_l (hl_eq ▸ le_sup_right)

    have hq_covBy_π : q ⋖ π := by
      have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
      have h_inf : m ⊓ q ⋖ m := by
        rw [inf_comm, hqm_eq_U]; exact atom_covBy_join Γ.hU Γ.hV hUV
      have h1 := covBy_sup_of_inf_covBy_left h_inf
      have hmq : m ⊔ q = m ⊔ Γ.C := by
        show m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
        rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
      have hmC : m ⊔ Γ.C = π :=
        (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
          (sup_le hm_le_π Γ.hC_plane)).resolve_left
          (ne_of_gt (lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
      rwa [hmq, hmC] at h1

    have hτsP_ne_τsCc : τ_s_P ≠ τ_s_C_c := by
      intro h_eq
      have h_q : τ_s_P ≤ q := h_eq ▸ hτsCc_le_q
      have hτsP_eq_U : τ_s_P = Γ.U :=
        (Γ.hU.le_iff.mp ((le_inf hτsP_le_PU h_q).trans hPU_inf_q.le)).resolve_left hτsP_atom.1
      have h1 : Γ.U ≤ s ⊔ (Γ.O ⊔ P) ⊓ m := by rw [← hτsP_eq_U]; exact inf_le_right
      have hU_le_OP : Γ.U ≤ Γ.O ⊔ P :=
        ((le_inf h1 (le_sup_left : Γ.U ≤ m)).trans
          (line_direction hs_atom hs_not_m inf_le_right).le).trans inf_le_left
      have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
        (fun h => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1).symm)
      have hl_eq : l = Γ.O ⊔ P :=
        ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt_l.le
          (sup_le le_sup_left hU_le_OP)).resolve_left hO_lt_l.ne'
      exact hP_not_l (hl_eq ▸ le_sup_right)

    have hτbP_ne_τbCc : τ_b_P ≠ τ_b_C_c := by
      intro h_eq
      have h_q : τ_b_P ≤ q := h_eq ▸ hτbCc_le_q
      exact hτbP_not_m (((Γ.hU.le_iff.mp ((le_inf hτbP_le_PU h_q).trans
        hPU_inf_q.le)).resolve_left hτbP_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))

    have hcp4 : (P ⊔ C_c) ⊓ m = (τ_s_P ⊔ τ_s_C_c) ⊓ m := by
      by_cases hCc_collinear : C_c ≤ Γ.O ⊔ P
      ·
        set d' := (Γ.O ⊔ P) ⊓ m
        have hd'_atom : IsAtom d' :=
          line_meets_m_at_atom Γ.hO hP_atom hO_ne_P
            (sup_le (le_sup_left.trans le_sup_left) hP_π) hm_le_π hm_cov Γ.hO_not_m

        have hP_lt : P < P ⊔ C_c := lt_of_le_of_ne le_sup_left
          (fun h => hP_ne_Cc ((hP_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hCc_atom.1).symm)
        have hLHS_line : P ⊔ C_c = Γ.O ⊔ P :=
          ((sup_comm P Γ.O ▸ atom_covBy_join hP_atom Γ.hO
            (fun h => hO_ne_P h.symm)).eq_or_eq hP_lt.le
            (sup_le le_sup_right hCc_collinear)).resolve_left (ne_of_gt hP_lt)

        have hOCc_eq : Γ.O ⊔ C_c = Γ.O ⊔ P := by
          have hO_lt : Γ.O < Γ.O ⊔ C_c := lt_of_le_of_ne le_sup_left
            (fun h => hO_ne_Cc ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
              hCc_atom.1).symm)
          exact ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt.le
            (sup_le le_sup_left hCc_collinear)).resolve_left (ne_of_gt hO_lt)

        have hτsP_le : τ_s_P ≤ s ⊔ d' := inf_le_right
        have hτsCc_le : τ_s_C_c ≤ s ⊔ d' := by
          have h : τ_s_C_c ≤ s ⊔ (Γ.O ⊔ C_c) ⊓ m := inf_le_right
          rw [hOCc_eq] at h; exact h

        have hsd'_dir : (s ⊔ d') ⊓ m = d' := line_direction hs_atom hs_not_m inf_le_right

        have hRHS_le : (τ_s_P ⊔ τ_s_C_c) ⊓ m ≤ d' :=
          (inf_le_inf_right m (sup_le hτsP_le hτsCc_le)).trans hsd'_dir.le

        have hτsP_lt : τ_s_P < τ_s_P ⊔ τ_s_C_c := lt_of_le_of_ne le_sup_left
          (fun h => hτsP_ne_τsCc ((hτsP_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hτsCc_atom.1).symm)
        have hRHS_ne : m ⊓ (τ_s_P ⊔ τ_s_C_c) ≠ ⊥ :=
          lines_meet_if_coplanar hm_cov
            (sup_le hτsP_le hτsCc_le |>.trans (sup_le (hs_on.trans le_sup_left)
              (inf_le_right.trans hm_le_π)))
            (fun h => hτsCc_not_m (le_sup_right.trans h))
            hτsP_atom hτsP_lt
        rw [hLHS_line]
        exact ((hd'_atom.le_iff.mp hRHS_le).resolve_left (inf_comm m _ ▸ hRHS_ne)).symm
      ·

        have hO_not_q : ¬ Γ.O ≤ q := fun h =>
          Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l) h).trans
            hlq_eq_U.le)).resolve_left Γ.hO.1)
        have hW_atom : IsAtom ((Γ.O ⊔ P) ⊓ q) :=
          line_meets_m_at_atom Γ.hO hP_atom hO_ne_P
            (sup_le (le_sup_left.trans le_sup_left) hP_π)
            (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane) hq_covBy_π
            hO_not_q
        have hW_ne_Cc : (Γ.O ⊔ P) ⊓ q ≠ C_c := fun h => hCc_collinear (h ▸ inf_le_left)
        have hOPCc_span : Γ.O ⊔ P ⊔ C_c = π := by
          have h_mod : (C_c ⊔ (Γ.O ⊔ P)) ⊓ q = C_c ⊔ ((Γ.O ⊔ P) ⊓ q) :=
            sup_inf_assoc_of_le (Γ.O ⊔ P) hCc_le_q
          have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
          have hCc_lt : C_c < C_c ⊔ (Γ.O ⊔ P) ⊓ q := by
            apply lt_of_le_of_ne le_sup_left; intro h
            exact hW_ne_Cc ((hCc_atom.le_iff.mp (le_sup_right.trans (le_of_eq h.symm))).resolve_left
              hW_atom.1)
          have hCc_covBy : C_c ⋖ q := line_covers_its_atoms Γ.hU Γ.hC hUC hCc_atom hCc_le_q
          have hCcW_eq_q : C_c ⊔ (Γ.O ⊔ P) ⊓ q = q :=
            (hCc_covBy.eq_or_eq hCc_lt.le (sup_le hCc_le_q inf_le_right)).resolve_left
              (ne_of_gt hCc_lt)
          have hq_le : q ≤ Γ.O ⊔ P ⊔ C_c := by
            have := inf_eq_right.mp (h_mod.trans hCcW_eq_q); rwa [sup_comm] at this
          have hlC_le : l ⊔ Γ.C ≤ Γ.O ⊔ P ⊔ C_c :=
            sup_le (sup_le (le_sup_left.trans le_sup_left)
              ((le_sup_left : Γ.U ≤ q).trans hq_le))
              ((le_sup_right : Γ.C ≤ q).trans hq_le)
          have hl_lt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
          have hlC_eq : l ⊔ Γ.C = π :=
            (hl_cov_π.eq_or_eq hl_lt.le (sup_le le_sup_left Γ.hC_plane)).resolve_left
              (ne_of_gt hl_lt)
          exact le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left) hP_π) hCc_π)
            (le_of_eq hlC_eq.symm |>.trans hlC_le)

        have hs_ne_τsCc : s ≠ τ_s_C_c := by
          intro h_eq
          have : s ≤ C_c ⊔ Γ.U := by
            have h : τ_s_C_c ≤ C_c ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
            rw [hOs_eq_l, Γ.l_inf_m_eq_U] at h; rwa [← h_eq] at h
          exact hs_ne_U ((Γ.hU.le_iff.mp ((le_inf hs_on
            (this.trans (sup_le hCc_le_q (le_sup_left : Γ.U ≤ q)))).trans
            hlq_eq_U.le)).resolve_left hs_atom.1)
        exact cross_parallelism Γ.hO hs_atom hP_atom hCc_atom
          hs_ne_O.symm hO_ne_P hO_ne_Cc hP_ne_Cc
          (show s ≠ τ_s_P from by
            intro h_eq
            have hs_le_PU : s ≤ P ⊔ Γ.U := by
              have : τ_s_P ≤ P ⊔ (Γ.O ⊔ s) ⊓ m := inf_le_left
              rw [hOs_eq_l, Γ.l_inf_m_eq_U] at this; exact h_eq ▸ this
            exact hs_ne_U ((Γ.hU.le_iff.mp
              ((le_inf hs_on hs_le_PU).trans hl_inf_PU.le)).resolve_left hs_atom.1))
          hs_ne_τsCc hτsP_ne_τsCc
          (le_sup_left.trans le_sup_left) (hs_on.trans le_sup_left) hP_π hCc_π
          hm_le_π hm_cov hm_line
          Γ.hO_not_m hs_not_m hP_not_m hCc_not_m
          (fun h => hP_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
          (fun h => hCc_not_l (h.trans (hOs_eq_l ▸ le_refl l)))
          hCc_collinear hOPCc_span
          R hR hR_not h_irred

    have hcp5 : (P ⊔ C_c) ⊓ m = (τ_b_P ⊔ τ_b_C_c) ⊓ m := by
      by_cases hCc_collinear : C_c ≤ Γ.O ⊔ P
      ·
        set d' := (Γ.O ⊔ P) ⊓ m
        have hd'_atom : IsAtom d' :=
          line_meets_m_at_atom Γ.hO hP_atom hO_ne_P
            (sup_le (le_sup_left.trans le_sup_left) hP_π) hm_le_π hm_cov Γ.hO_not_m

        have hP_lt : P < P ⊔ C_c := lt_of_le_of_ne le_sup_left
          (fun h => hP_ne_Cc ((hP_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hCc_atom.1).symm)
        have hLHS_line : P ⊔ C_c = Γ.O ⊔ P :=
          ((sup_comm P Γ.O ▸ atom_covBy_join hP_atom Γ.hO
            (fun h => hO_ne_P h.symm)).eq_or_eq hP_lt.le
            (sup_le le_sup_right hCc_collinear)).resolve_left (ne_of_gt hP_lt)

        have hOCc_eq : Γ.O ⊔ C_c = Γ.O ⊔ P := by
          have hO_lt : Γ.O < Γ.O ⊔ C_c := lt_of_le_of_ne le_sup_left
            (fun h => hO_ne_Cc ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
              hCc_atom.1).symm)
          exact ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt.le
            (sup_le le_sup_left hCc_collinear)).resolve_left (ne_of_gt hO_lt)

        have hτbP_le : τ_b_P ≤ b ⊔ d' := inf_le_right
        have hτbCc_le : τ_b_C_c ≤ b ⊔ d' := by
          have h : τ_b_C_c ≤ b ⊔ (Γ.O ⊔ C_c) ⊓ m := inf_le_right
          rw [hOCc_eq] at h; exact h

        have hbd'_dir : (b ⊔ d') ⊓ m = d' := line_direction hb hb_not_m inf_le_right

        have hRHS_le : (τ_b_P ⊔ τ_b_C_c) ⊓ m ≤ d' :=
          (inf_le_inf_right m (sup_le hτbP_le hτbCc_le)).trans hbd'_dir.le

        have hτbCc_atom_local : IsAtom τ_b_C_c :=
          parallelogram_completion_atom Γ.hO hb hCc_atom (fun h => hb_ne_O h.symm) hO_ne_Cc
            hb_ne_Cc (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) hCc_π
            hm_le_π hm_cov hm_line Γ.hO_not_m hb_not_m hCc_not_m
            (fun h => hCc_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
        have hτbP_lt : τ_b_P < τ_b_P ⊔ τ_b_C_c := lt_of_le_of_ne le_sup_left
          (fun h => hτbP_ne_τbCc ((hτbP_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hτbCc_atom_local.1).symm)
        have hRHS_ne : m ⊓ (τ_b_P ⊔ τ_b_C_c) ≠ ⊥ :=
          lines_meet_if_coplanar hm_cov
            (sup_le hτbP_le hτbCc_le |>.trans (sup_le (hb_on.trans le_sup_left)
              (inf_le_right.trans hm_le_π)))
            (fun h => hτbP_not_m (le_sup_left.trans h))
            hτbP_atom hτbP_lt
        rw [hLHS_line]
        exact ((hd'_atom.le_iff.mp hRHS_le).resolve_left (inf_comm m _ ▸ hRHS_ne)).symm
      ·

        have hO_not_q : ¬ Γ.O ≤ q := fun h =>
          Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l) h).trans
            hlq_eq_U.le)).resolve_left Γ.hO.1)
        have hW_atom : IsAtom ((Γ.O ⊔ P) ⊓ q) :=
          line_meets_m_at_atom Γ.hO hP_atom hO_ne_P
            (sup_le (le_sup_left.trans le_sup_left) hP_π)
            (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane) hq_covBy_π
            hO_not_q
        have hW_ne_Cc : (Γ.O ⊔ P) ⊓ q ≠ C_c := fun h => hCc_collinear (h ▸ inf_le_left)
        have hOPCc_span : Γ.O ⊔ P ⊔ C_c = π := by
          have h_mod : (C_c ⊔ (Γ.O ⊔ P)) ⊓ q = C_c ⊔ ((Γ.O ⊔ P) ⊓ q) :=
            sup_inf_assoc_of_le (Γ.O ⊔ P) hCc_le_q
          have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
          have hCc_lt : C_c < C_c ⊔ (Γ.O ⊔ P) ⊓ q := by
            apply lt_of_le_of_ne le_sup_left; intro h
            exact hW_ne_Cc ((hCc_atom.le_iff.mp (le_sup_right.trans (le_of_eq h.symm))).resolve_left
              hW_atom.1)
          have hCc_covBy : C_c ⋖ q := line_covers_its_atoms Γ.hU Γ.hC hUC hCc_atom hCc_le_q
          have hCcW_eq_q : C_c ⊔ (Γ.O ⊔ P) ⊓ q = q :=
            (hCc_covBy.eq_or_eq hCc_lt.le (sup_le hCc_le_q inf_le_right)).resolve_left
              (ne_of_gt hCc_lt)
          have hq_le : q ≤ Γ.O ⊔ P ⊔ C_c := by
            have := inf_eq_right.mp (h_mod.trans hCcW_eq_q); rwa [sup_comm] at this
          have hlC_le : l ⊔ Γ.C ≤ Γ.O ⊔ P ⊔ C_c :=
            sup_le (sup_le (le_sup_left.trans le_sup_left)
              ((le_sup_left : Γ.U ≤ q).trans hq_le))
              ((le_sup_right : Γ.C ≤ q).trans hq_le)
          have hl_lt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
          have hlC_eq : l ⊔ Γ.C = π :=
            (hl_cov_π.eq_or_eq hl_lt.le (sup_le le_sup_left Γ.hC_plane)).resolve_left
              (ne_of_gt hl_lt)
          exact le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left) hP_π) hCc_π)
            (le_of_eq hlC_eq.symm |>.trans hlC_le)

        have hb_ne_τbCc : b ≠ τ_b_C_c := by
          intro h_eq
          have : b ≤ C_c ⊔ Γ.U := by
            have h : τ_b_C_c ≤ C_c ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
            rw [hOb_eq_l, Γ.l_inf_m_eq_U] at h; rwa [← h_eq] at h
          exact hb_ne_U ((Γ.hU.le_iff.mp ((le_inf hb_on
            (this.trans (sup_le hCc_le_q (le_sup_left : Γ.U ≤ q)))).trans
            hlq_eq_U.le)).resolve_left hb.1)
        exact cross_parallelism Γ.hO hb hP_atom hCc_atom
          (fun h => hb_ne_O h.symm) hO_ne_P hO_ne_Cc hP_ne_Cc
          (show b ≠ τ_b_P from by
            intro h_eq
            have hb_le_PU : b ≤ P ⊔ Γ.U := by
              have : τ_b_P ≤ P ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
              rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this; exact h_eq ▸ this
            exact hb_ne_U ((Γ.hU.le_iff.mp
              ((le_inf hb_on hb_le_PU).trans hl_inf_PU.le)).resolve_left hb.1))
          hb_ne_τbCc hτbP_ne_τbCc
          (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) hP_π hCc_π
          hm_le_π hm_cov hm_line
          Γ.hO_not_m hb_not_m hP_not_m hCc_not_m
          (fun h => hP_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
          (fun h => hCc_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
          hCc_collinear hOPCc_span
          R hR hR_not h_irred

    have hτbCc_atom : IsAtom τ_b_C_c :=
      parallelogram_completion_atom Γ.hO hb hCc_atom (fun h => hb_ne_O h.symm) hO_ne_Cc
        hb_ne_Cc (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) hCc_π
        hm_le_π hm_cov hm_line Γ.hO_not_m hb_not_m hCc_not_m
        (fun h => hCc_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
    have hτbCc_not_m : ¬ τ_b_C_c ≤ m := by
      intro h
      have hτbCc_eq_U : τ_b_C_c = Γ.U :=
        (Γ.hU.le_iff.mp ((le_inf hτbCc_le_q h).trans hqm_eq_U.le)).resolve_left hτbCc_atom.1
      have h1 : Γ.U ≤ b ⊔ (Γ.O ⊔ C_c) ⊓ m := by rw [← hτbCc_eq_U]; exact inf_le_right
      have hU_le_OCc : Γ.U ≤ Γ.O ⊔ C_c :=
        ((le_inf h1 (le_sup_left : Γ.U ≤ m)).trans
          (line_direction hb hb_not_m inf_le_right).le).trans inf_le_left
      have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
        (fun h' => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
      have hl_eq : l = Γ.O ⊔ C_c :=
        ((atom_covBy_join Γ.hO hCc_atom hO_ne_Cc).eq_or_eq hO_lt_l.le
          (sup_le le_sup_left hU_le_OCc)).resolve_left hO_lt_l.ne'
      exact hCc_not_l (hl_eq ▸ le_sup_right)
    have hO_ne_τbCc : Γ.O ≠ τ_b_C_c := by
      intro h; exact Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l)
        (h ▸ hτbCc_le_q)).trans hlq_eq_U.le)).resolve_left Γ.hO.1)
    have ha_ne_τbCc : a ≠ τ_b_C_c := fun h => ha_ne_U ((Γ.hU.le_iff.mp ((le_inf ha_on
      (h ▸ hτbCc_le_q)).trans hlq_eq_U.le)).resolve_left ha.1)

    have hτaτbCc_le_q : τ_a_τ_b_C_c ≤ q := by
      have : τ_a_τ_b_C_c ≤ τ_b_C_c ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
      rw [hOa_eq_l, Γ.l_inf_m_eq_U] at this
      exact this.trans (sup_le hτbCc_le_q (le_sup_left : Γ.U ≤ q))

    have hτa_not_q : ¬ τ_a_τ_b_P ≤ q := by
      intro h
      have hτa_eq_U : τ_a_τ_b_P = Γ.U :=
        (Γ.hU.le_iff.mp ((le_inf hτa_le_PU h).trans hPU_inf_q.le)).resolve_left hτa_atom.1
      have hτs_eq_U : τ_s_P = Γ.U := hP_agree ▸ hτa_eq_U
      have h1 : Γ.U ≤ s ⊔ (Γ.O ⊔ P) ⊓ m := by rw [← hτs_eq_U]; exact inf_le_right
      have hU_le_OP : Γ.U ≤ Γ.O ⊔ P :=
        ((le_inf h1 (le_sup_left : Γ.U ≤ m)).trans
          (line_direction hs_atom hs_not_m inf_le_right).le).trans inf_le_left
      have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
        (fun h' => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hU.1).symm)
      have hl_eq : l = Γ.O ⊔ P :=
        ((atom_covBy_join Γ.hO hP_atom hO_ne_P).eq_or_eq hO_lt_l.le
          (sup_le le_sup_left hU_le_OP)).resolve_left (ne_of_gt hO_lt_l)
      exact hP_not_l (hl_eq ▸ le_sup_right)

    have hτa_ne_τaτbCc : τ_a_τ_b_P ≠ τ_a_τ_b_C_c := by
      intro h_eq
      exact hτa_not_q (h_eq ▸ hτaτbCc_le_q)

    have hcp6 : (τ_b_P ⊔ τ_b_C_c) ⊓ m = (τ_a_τ_b_P ⊔ τ_a_τ_b_C_c) ⊓ m := by
      by_cases hτbCc_collinear : τ_b_C_c ≤ Γ.O ⊔ τ_b_P
      ·
        set d' := (Γ.O ⊔ τ_b_P) ⊓ m
        have hd'_atom : IsAtom d' :=
          line_meets_m_at_atom Γ.hO hτbP_atom hO_ne_τbP
            (sup_le (le_sup_left.trans le_sup_left) hτbP_π) hm_le_π hm_cov Γ.hO_not_m

        have hτbP_lt : τ_b_P < τ_b_P ⊔ τ_b_C_c := lt_of_le_of_ne le_sup_left
          (fun h => hτbP_ne_τbCc ((hτbP_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hτbCc_atom.1).symm)
        have hLHS_line : τ_b_P ⊔ τ_b_C_c = Γ.O ⊔ τ_b_P :=
          ((sup_comm τ_b_P Γ.O ▸ atom_covBy_join hτbP_atom Γ.hO
            (fun h => hO_ne_τbP h.symm)).eq_or_eq hτbP_lt.le
            (sup_le le_sup_right hτbCc_collinear)).resolve_left (ne_of_gt hτbP_lt)

        have hOτbCc_eq : Γ.O ⊔ τ_b_C_c = Γ.O ⊔ τ_b_P := by
          have hO_lt : Γ.O < Γ.O ⊔ τ_b_C_c := lt_of_le_of_ne le_sup_left
            (fun h => hO_ne_τbCc ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
              hτbCc_atom.1).symm)
          exact ((atom_covBy_join Γ.hO hτbP_atom hO_ne_τbP).eq_or_eq hO_lt.le
            (sup_le le_sup_left hτbCc_collinear)).resolve_left (ne_of_gt hO_lt)

        have hτa_le : τ_a_τ_b_P ≤ a ⊔ d' := inf_le_right

        have hτaτbCc_le : τ_a_τ_b_C_c ≤ a ⊔ d' := by
          have h : τ_a_τ_b_C_c ≤ a ⊔ (Γ.O ⊔ τ_b_C_c) ⊓ m := inf_le_right
          rw [hOτbCc_eq] at h; exact h

        have had'_dir : (a ⊔ d') ⊓ m = d' := line_direction ha ha_not_m inf_le_right

        have hRHS_le : (τ_a_τ_b_P ⊔ τ_a_τ_b_C_c) ⊓ m ≤ d' :=
          (inf_le_inf_right m (sup_le hτa_le hτaτbCc_le)).trans had'_dir.le

        have hτaτbCc_atom : IsAtom τ_a_τ_b_C_c :=
          parallelogram_completion_atom Γ.hO ha hτbCc_atom
            (fun h => ha_ne_O h.symm) hO_ne_τbCc ha_ne_τbCc
            (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left)
            (hτbCc_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
            hm_le_π hm_cov hm_line
            Γ.hO_not_m ha_not_m hτbCc_not_m
            (fun h => hτbCc_not_m (((Γ.hU.le_iff.mp ((le_inf
              (h.trans (hOa_eq_l ▸ le_refl l)) hτbCc_le_q).trans
              hlq_eq_U.le)).resolve_left hτbCc_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m)))

        have hτa_lt : τ_a_τ_b_P < τ_a_τ_b_P ⊔ τ_a_τ_b_C_c := lt_of_le_of_ne le_sup_left
          (fun h => hτa_ne_τaτbCc ((hτa_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hτaτbCc_atom.1).symm)
        have hRHS_ne : m ⊓ (τ_a_τ_b_P ⊔ τ_a_τ_b_C_c) ≠ ⊥ :=
          lines_meet_if_coplanar hm_cov
            (sup_le hτa_le hτaτbCc_le |>.trans (sup_le (ha_on.trans le_sup_left)
              (inf_le_right.trans hm_le_π)))
            (fun h => by

              have h1 := (le_inf hτa_le (le_sup_left.trans h)).trans (line_direction ha ha_not_m inf_le_right).le
              have h2 := (le_inf hτaτbCc_le (le_sup_right.trans h)).trans (line_direction ha ha_not_m inf_le_right).le
              exact hτa_ne_τaτbCc ((hd'_atom.le_iff.mp h1).resolve_left hτa_atom.1 |>.trans
                ((hd'_atom.le_iff.mp h2).resolve_left hτaτbCc_atom.1).symm))
            hτa_atom hτa_lt
        rw [hLHS_line]
        exact ((hd'_atom.le_iff.mp hRHS_le).resolve_left (inf_comm m _ ▸ hRHS_ne)).symm
      ·

        have hO_ne_τbCc' : Γ.O ≠ τ_b_C_c := hO_ne_τbCc

        have hW_atom : IsAtom ((Γ.O ⊔ τ_b_P) ⊓ q) :=
          line_meets_m_at_atom Γ.hO hτbP_atom hO_ne_τbP
            (sup_le (le_sup_left.trans le_sup_left) hτbP_π)
            (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane) hq_covBy_π
            (fun h => Γ.hOU ((Γ.hU.le_iff.mp ((le_inf (le_sup_left : Γ.O ≤ l) h).trans
              hlq_eq_U.le)).resolve_left Γ.hO.1))
        have hW_ne_τbCc : (Γ.O ⊔ τ_b_P) ⊓ q ≠ τ_b_C_c := fun h =>
          hτbCc_collinear (h ▸ inf_le_left)
        have hspan : Γ.O ⊔ τ_b_P ⊔ τ_b_C_c = π := by
          have h_mod : (τ_b_C_c ⊔ (Γ.O ⊔ τ_b_P)) ⊓ q = τ_b_C_c ⊔ ((Γ.O ⊔ τ_b_P) ⊓ q) :=
            sup_inf_assoc_of_le (Γ.O ⊔ τ_b_P) hτbCc_le_q
          have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
          have hτbCc_lt : τ_b_C_c < τ_b_C_c ⊔ (Γ.O ⊔ τ_b_P) ⊓ q := by
            apply lt_of_le_of_ne le_sup_left; intro h
            exact hW_ne_τbCc ((hτbCc_atom.le_iff.mp (le_sup_right.trans (le_of_eq h.symm))).resolve_left
              hW_atom.1)
          have hτbCc_covBy : τ_b_C_c ⋖ q := line_covers_its_atoms Γ.hU Γ.hC hUC hτbCc_atom hτbCc_le_q
          have hτbCcW_eq_q : τ_b_C_c ⊔ (Γ.O ⊔ τ_b_P) ⊓ q = q :=
            (hτbCc_covBy.eq_or_eq hτbCc_lt.le (sup_le hτbCc_le_q inf_le_right)).resolve_left
              (ne_of_gt hτbCc_lt)
          have hq_le : q ≤ Γ.O ⊔ τ_b_P ⊔ τ_b_C_c := by
            have := inf_eq_right.mp (h_mod.trans hτbCcW_eq_q); rwa [sup_comm] at this
          have hlC_le : l ⊔ Γ.C ≤ Γ.O ⊔ τ_b_P ⊔ τ_b_C_c :=
            sup_le (sup_le (le_sup_left.trans le_sup_left)
              ((le_sup_left : Γ.U ≤ q).trans hq_le))
              ((le_sup_right : Γ.C ≤ q).trans hq_le)
          have hl_lt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
          have hlC_eq : l ⊔ Γ.C = π :=
            (hl_cov_π.eq_or_eq hl_lt.le (sup_le le_sup_left Γ.hC_plane)).resolve_left
              (ne_of_gt hl_lt)
          exact le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left) hτbP_π)
            (hτbCc_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)))
            (le_of_eq hlC_eq.symm |>.trans hlC_le)

        have hτbCc_not_Oa : ¬ τ_b_C_c ≤ Γ.O ⊔ a := by
          intro h; exact hτbCc_not_m (((Γ.hU.le_iff.mp ((le_inf (h.trans (hOa_eq_l ▸ le_refl l))
            hτbCc_le_q).trans hlq_eq_U.le)).resolve_left hτbCc_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m))
        have ha_ne_τa' : a ≠ τ_a_τ_b_P := by
          intro h_eq
          have hτa_le_τU : τ_a_τ_b_P ≤ τ_b_P ⊔ Γ.U := by
            have : τ_a_τ_b_P ≤ τ_b_P ⊔ (Γ.O ⊔ a) ⊓ m := inf_le_left
            rwa [hOa_eq_l, Γ.l_inf_m_eq_U] at this
          rw [← h_eq] at hτa_le_τU
          exact ha_ne_U ((Γ.hU.le_iff.mp ((le_inf ha_on
            (hτa_le_τU.trans (sup_le hτbP_le_PU le_sup_right))).trans
            hl_inf_PU.le)).resolve_left ha.1)
        have ha_ne_τaτbCc : a ≠ parallelogram_completion Γ.O a τ_b_C_c m := by
          intro h; exact ha_ne_U ((Γ.hU.le_iff.mp
            ((le_inf ha_on (h ▸ hτaτbCc_le_q)).trans hlq_eq_U.le)).resolve_left ha.1)
        have hτa_ne_τaτbCc' : τ_a_τ_b_P ≠ parallelogram_completion Γ.O a τ_b_C_c m := by
          intro h_eq
          exact hτa_not_q (h_eq ▸ hτaτbCc_le_q)
        exact cross_parallelism Γ.hO ha hτbP_atom hτbCc_atom
          (fun h => ha_ne_O h.symm) hO_ne_τbP hO_ne_τbCc hτbP_ne_τbCc
          ha_ne_τa' ha_ne_τaτbCc hτa_ne_τaτbCc'
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hτbP_π
          (hτbCc_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m hτbP_not_m hτbCc_not_m
          (fun h => hτbP_not_q ((le_inf (h.trans (hOa_eq_l ▸ le_refl l))
            hτbP_le_PU).trans hl_inf_PU.le |>.trans (le_sup_left : Γ.U ≤ q)))
          hτbCc_not_Oa
          hτbCc_collinear
          hspan
          R hR hR_not h_irred

    have h_dir2 : (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m = (τ_a_τ_b_P ⊔ τ_a_τ_b_C_c) ⊓ m := by
      have h := hcp4.symm.trans (hcp5.trans hcp6)
      rwa [hP_agree] at h

    have hCc_agree : τ_s_C_c = τ_a_τ_b_C_c := by

      have hτaτbCc_atom : IsAtom τ_a_τ_b_C_c :=
        parallelogram_completion_atom Γ.hO ha hτbCc_atom
          (fun h => ha_ne_O h.symm) hO_ne_τbCc ha_ne_τbCc
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left)
          (hτbCc_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m hτbCc_not_m
          (fun h => hτbCc_not_m (((Γ.hU.le_iff.mp ((le_inf
            (h.trans (hOa_eq_l ▸ le_refl l)) hτbCc_le_q).trans
            hlq_eq_U.le)).resolve_left hτbCc_atom.1).symm ▸ (le_sup_left : Γ.U ≤ m)))

      have hτsCc_ne_τa : τ_s_C_c ≠ τ_a_τ_b_P := fun h => hτa_not_q (h ▸ hτsCc_le_q)

      have hτa_not_m : ¬ τ_a_τ_b_P ≤ m := by
        intro h; apply hτa_not_q

        have hPm : P ⊓ m = ⊥ :=
          (hP_atom.le_iff.mp inf_le_left).resolve_right (fun h' => hP_not_m (h' ▸ inf_le_right))
        have hPUm : (P ⊔ Γ.U) ⊓ m = Γ.U := by
          show (P ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
          rw [sup_comm P Γ.U, sup_inf_assoc_of_le P (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V),
              hPm, sup_bot_eq]
        have : τ_a_τ_b_P ≤ Γ.U := (le_inf hτa_le_PU h).trans hPUm.le
        exact ((Γ.hU.le_iff.mp this).resolve_left hτa_atom.1).symm ▸ (le_sup_left : Γ.U ≤ q)

      have hd_atom : IsAtom ((τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m) := by
        rw [sup_comm]; exact line_meets_m_at_atom hτsCc_atom hτa_atom
          hτsCc_ne_τa (sup_le (hτsCc_le_q.trans
            (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
            (hτa_le_PU.trans (sup_le hP_π (le_sup_right.trans le_sup_left))))
          hm_le_π hm_cov hτsCc_not_m
      have hd_ne_τa : (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m ≠ τ_a_τ_b_P := fun h =>
        hτa_not_m (h ▸ inf_le_right)
      have hτa_covBy_1 : τ_a_τ_b_P ⋖ τ_a_τ_b_P ⊔ τ_s_C_c :=
        atom_covBy_join hτa_atom hτsCc_atom hτsCc_ne_τa.symm
      have hτa_lt_d : τ_a_τ_b_P < τ_a_τ_b_P ⊔ (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m :=
        lt_of_le_of_ne le_sup_left
          (fun h => hd_ne_τa ((hτa_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
            hd_atom.1))
      have hd_eq_1 : τ_a_τ_b_P ⊔ (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m = τ_a_τ_b_P ⊔ τ_s_C_c :=
        (hτa_covBy_1.eq_or_eq hτa_lt_d.le (sup_le le_sup_left inf_le_left)).resolve_left
          (ne_of_gt hτa_lt_d)
      have hτa_covBy_2 : τ_a_τ_b_P ⋖ τ_a_τ_b_P ⊔ τ_a_τ_b_C_c :=
        atom_covBy_join hτa_atom hτaτbCc_atom hτa_ne_τaτbCc
      have hd_le_2 : (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m ≤ τ_a_τ_b_P ⊔ τ_a_τ_b_C_c :=
        h_dir2 ▸ inf_le_left
      have hd_eq_2 : τ_a_τ_b_P ⊔ (τ_a_τ_b_P ⊔ τ_s_C_c) ⊓ m = τ_a_τ_b_P ⊔ τ_a_τ_b_C_c :=
        (hτa_covBy_2.eq_or_eq hτa_lt_d.le (sup_le le_sup_left hd_le_2)).resolve_left
          (ne_of_gt hτa_lt_d)
      have hline_eq : τ_a_τ_b_P ⊔ τ_s_C_c = τ_a_τ_b_P ⊔ τ_a_τ_b_C_c :=
        hd_eq_1.symm.trans hd_eq_2
      have hτaτbCc_on_line : τ_a_τ_b_C_c ≤ τ_s_C_c ⊔ τ_a_τ_b_P :=
        sup_comm τ_s_C_c τ_a_τ_b_P ▸ hline_eq ▸ le_sup_right
      have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
      exact two_lines hτsCc_atom hτaτbCc_atom hτa_atom hτsCc_ne_τa
        hτsCc_le_q hτaτbCc_le_q hτaτbCc_on_line hτa_not_q
        (line_covers_its_atoms Γ.hU Γ.hC hUC hτsCc_atom hτsCc_le_q)
    exact hCc_agree

/-- **Reusable `key_identity` core** (`a ≠ b`-free).

`key_identity`'s argument uses `a ≠ b` in exactly two places: the fallback
auxiliary point `(a ⊔ Γ.E) ⊓ (b ⊔ Γ.C)` (which collapses to `a` at `b = a`), and
the single `coord_add_eq_translation` call (line 735).  This core abstracts both:
it takes a general-position witness `G` on `b ⊔ Γ.C` (off `l`, `q`, `m`; `≠ b`,
`≠ C`) directly, and the translation identity `h_s_transl` as a hypothesis.  Its
body is verbatim `key_identity`'s `h_cross`-body (Assoc.lean 363–1120) plus its
final argument (1122–1269), with the collapsing `h_irred`/fallback dispatch deleted
and the one translation call replaced by `h_s_transl`.

Then `key_identity Γ a b` = this core with `G` from `h_irred`/fallback and
`h_s_transl := coord_add_eq_translation`; and the *doubling* key-identity
`key_identity Γ a a` = this core with `G` a fresh point from `dbl_aux_point` and
`h_s_transl := coord_add_eq_translation_diag`. -/
theorem key_identity_core (Γ : CoordSystem L)
    (a b : L) (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (G : L) (hG_atom : IsAtom G) (hG_le_bC : G ≤ b ⊔ Γ.C)
    (hG_ne_b_raw : G ≠ b) (hG_ne_C : G ≠ Γ.C)
    (hG_not_l : ¬ G ≤ Γ.O ⊔ Γ.U) (hG_not_q : ¬ G ≤ Γ.U ⊔ Γ.C)
    (hG_not_m : ¬ G ≤ Γ.U ⊔ Γ.V)
    (h_s_transl : coord_add Γ a b
      = parallelogram_completion Γ.C
          (parallelogram_completion Γ.O a Γ.C (Γ.U ⊔ Γ.V)) b (Γ.U ⊔ Γ.V))
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    let C_b := parallelogram_completion Γ.O b Γ.C (Γ.U ⊔ Γ.V)
    let s := coord_add Γ a b
    let C_s := parallelogram_completion Γ.O s Γ.C (Γ.U ⊔ Γ.V)
    parallelogram_completion Γ.O a C_b (Γ.U ⊔ Γ.V) = C_s := by
  intro C_b s C_s
  have hb_ne_C : b ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hb_on)

  set l := Γ.O ⊔ Γ.U
  set m := Γ.U ⊔ Γ.V
  set q := Γ.U ⊔ Γ.C
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set τ_a_C_b := parallelogram_completion Γ.O a C_b m

  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hb_not_m : ¬ b ≤ m := fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on h)
  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hOa_eq_l : Γ.O ⊔ a = l := by
    have h_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
      (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt h_lt)
  have hOb_eq_l : Γ.O ⊔ b = l := by
    have h_lt : Γ.O < Γ.O ⊔ b := lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hb.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
      (sup_le le_sup_left hb_on)).resolve_left (ne_of_gt h_lt)
  have hm_cov : m ⋖ π := by

    show Γ.U ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
    have hO_inf_m : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
    rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = Γ.O ⊔ (Γ.U ⊔ Γ.V) from sup_assoc _ _ _]
    exact covBy_sup_of_inf_covBy_left (hO_inf_m ▸ Γ.hO.bot_covBy)
  have hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m := fun x hx hle =>
    line_covers_its_atoms Γ.hU Γ.hV hUV hx hle

  have hlq_eq_U : l ⊓ q = Γ.U := by
    show (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U
    rw [sup_comm Γ.O Γ.U]
    have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
    have hOC' : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm hUC hOC'
      (fun h => Γ.hC_not_l (le_trans h (by rw [sup_comm])))

  have hCb_atom : IsAtom C_b :=
    parallelogram_completion_atom Γ.hO hb Γ.hC
      (fun h => hb_ne_O h.symm)
      hOC (fun h => Γ.hC_not_l (h ▸ hb_on))
      (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) Γ.hC_plane
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hm_cov hm_line
      Γ.hO_not_m hb_not_m Γ.hC_not_m
      (fun h => Γ.hC_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
  have hCb_le_bE : C_b ≤ b ⊔ Γ.E := (inf_le_right : C_b ≤ b ⊔ (Γ.O ⊔ Γ.C) ⊓ m)
  have hCb_le_q : C_b ≤ q := by
    have : C_b ≤ Γ.C ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
    rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this
    exact this.trans (sup_comm Γ.C Γ.U ▸ le_refl q)
  have hb_ne_Cb : b ≠ C_b := by
    intro h

    have hb_le_q : b ≤ q := h ▸ hCb_le_q
    have hb_le_lq : b ≤ l ⊓ q := le_inf hb_on hb_le_q
    rw [hlq_eq_U] at hb_le_lq
    exact hb_ne_U ((Γ.hU.le_iff.mp hb_le_lq).resolve_left hb.1)
  have hCb_not_m : ¬ C_b ≤ m := by
    intro hCb_m

    have h_bE_dir : (b ⊔ Γ.E) ⊓ m = Γ.E :=
      line_direction hb hb_not_m Γ.hE_on_m
    have hCb_le_E : C_b ≤ Γ.E := by
      have : C_b ≤ (b ⊔ Γ.E) ⊓ m := le_inf hCb_le_bE hCb_m
      rwa [h_bE_dir] at this

    have hCb_eq_E : C_b = Γ.E :=
      (Γ.hE_atom.le_iff.mp hCb_le_E).resolve_left hCb_atom.1

    have hE_le_q : Γ.E ≤ q := hCb_eq_E ▸ hCb_le_q
    have hE_le_m : Γ.E ≤ m := Γ.hE_on_m
    have hE_le_qm : Γ.E ≤ q ⊓ m := le_inf hE_le_q hE_le_m
    have hqm_eq : q ⊓ m = Γ.U := by
      show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U

      rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]

      have hC_inf_m : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
        (Γ.hC.le_iff.mp inf_le_left).resolve_right
          (fun h => Γ.hC_not_m (h ▸ inf_le_right))
      rw [hC_inf_m, sup_bot_eq]
    rw [hqm_eq] at hE_le_qm
    exact Γ.hEU ((Γ.hU.le_iff.mp hE_le_qm).resolve_left Γ.hE_atom.1)

  have h_τ_le_q : τ_a_C_b ≤ q := by
    show (C_b ⊔ (Γ.O ⊔ a) ⊓ m) ⊓ (a ⊔ (Γ.O ⊔ C_b) ⊓ m) ≤ q
    rw [hOa_eq_l, Γ.l_inf_m_eq_U]
    exact inf_le_left.trans (sup_le hCb_le_q (le_sup_left : Γ.U ≤ q))

  have h_bCb_eq_bE : b ⊔ C_b = b ⊔ Γ.E := by
    have hb_ne_E : b ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hb_on)
    have h_lt : b < b ⊔ C_b := lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_Cb ((hb.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hCb_atom.1).symm)
    exact ((atom_covBy_join hb Γ.hE_atom hb_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left hCb_le_bE)).resolve_left (ne_of_gt h_lt)
  have h_bCb_dir : (b ⊔ C_b) ⊓ m = Γ.E := by
    rw [h_bCb_eq_bE]; exact line_direction hb hb_not_m Γ.hE_on_m

  have h_cross : (s ⊔ τ_a_C_b) ⊓ m = Γ.E := by

    set G' := parallelogram_completion Γ.O a G m

    have hG_le_π : G ≤ π :=
      hG_le_bC.trans (sup_le (hb_on.trans le_sup_left) Γ.hC_plane)

    have hG'_atom : IsAtom G' := by
      exact parallelogram_completion_atom Γ.hO ha hG_atom
        (fun h => ha_ne_O h.symm)
        (fun h => hG_not_l (h ▸ le_sup_left))
        (fun h => hG_not_l (h ▸ ha_on))
        (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hG_le_π
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hm_cov hm_line
        Γ.hO_not_m ha_not_m hG_not_m
        (fun h => hG_not_l (h.trans (hOa_eq_l ▸ le_refl l)))

    have hG'_not_m : ¬ G' ≤ m := by
      intro hG'_m
      set d_Oa := (Γ.O ⊔ a) ⊓ m
      set e_OG := (Γ.O ⊔ G) ⊓ m
      have hd_atom : IsAtom d_Oa := line_meets_m_at_atom Γ.hO ha
        (fun h => ha_ne_O h.symm)
        (sup_le (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left))
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
        hm_cov Γ.hO_not_m
      have hd_on_m : d_Oa ≤ m := inf_le_right
      have he_atom : IsAtom e_OG := line_meets_m_at_atom Γ.hO hG_atom
        (fun h => hG_not_l (h ▸ le_sup_left))
        (sup_le (le_sup_left.trans le_sup_left) hG_le_π)
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
        hm_cov Γ.hO_not_m
      have he_on_m : e_OG ≤ m := inf_le_right

      have hG'_le_d : G' ≤ d_Oa := by
        have h1 : G' ≤ G ⊔ d_Oa := by
          show parallelogram_completion Γ.O a G m ≤ G ⊔ d_Oa
          unfold parallelogram_completion; exact inf_le_left
        have h2 : G' ≤ (G ⊔ d_Oa) ⊓ m := le_inf h1 hG'_m
        rwa [line_direction hG_atom hG_not_m hd_on_m] at h2

      have hG'_le_e : G' ≤ e_OG := by
        have h1 : G' ≤ a ⊔ e_OG := by
          show parallelogram_completion Γ.O a G m ≤ a ⊔ e_OG
          unfold parallelogram_completion; exact inf_le_right
        have h2 : G' ≤ (a ⊔ e_OG) ⊓ m := le_inf h1 hG'_m
        rwa [line_direction ha ha_not_m he_on_m] at h2

      have hG'_eq_d := (hd_atom.le_iff.mp hG'_le_d).resolve_left hG'_atom.1
      have hG'_eq_e := (he_atom.le_iff.mp hG'_le_e).resolve_left hG'_atom.1
      have hd_eq_e : d_Oa = e_OG := hG'_eq_d.symm.trans hG'_eq_e

      have hd_le_both : d_Oa ≤ (Γ.O ⊔ a) ⊓ (Γ.O ⊔ G) :=
        le_inf inf_le_left (hd_eq_e ▸ inf_le_left)
      have hOa_inf_OG : (Γ.O ⊔ a) ⊓ (Γ.O ⊔ G) = Γ.O := by
        rw [hOa_eq_l]
        exact modular_intersection Γ.hO Γ.hU hG_atom Γ.hOU
          (fun h => hG_not_l (h ▸ le_sup_left))
          (fun h => hG_not_l (h ▸ le_sup_right))
          hG_not_l
      rw [hOa_inf_OG] at hd_le_both
      exact Γ.hO_not_m ((Γ.hO.le_iff.mp hd_le_both).resolve_left hd_atom.1 ▸ hd_on_m)

    have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
    have hG'_le_π : G' ≤ π := by

      have h1 : G' ≤ G ⊔ (Γ.O ⊔ a) ⊓ m := by
        show parallelogram_completion Γ.O a G m ≤ _
        unfold parallelogram_completion; exact inf_le_left
      exact h1.trans (sup_le hG_le_π (inf_le_right.trans hm_le_π))

    have hGG' : G ≠ G' := by
      intro h_eq

      have hG_le_ae : G ≤ a ⊔ (Γ.O ⊔ G) ⊓ m := by
        have : G' ≤ a ⊔ (Γ.O ⊔ G) ⊓ m := by
          show parallelogram_completion Γ.O a G m ≤ _
          unfold parallelogram_completion; exact inf_le_right
        exact h_eq ▸ this

      have hG_le_OG : G ≤ Γ.O ⊔ G := le_sup_right

      have hG_le_both : G ≤ (a ⊔ (Γ.O ⊔ G) ⊓ m) ⊓ (Γ.O ⊔ G) :=
        le_inf hG_le_ae hG_le_OG

      rw [sup_comm a _, sup_inf_assoc_of_le a (inf_le_left : (Γ.O ⊔ G) ⊓ m ≤ Γ.O ⊔ G)]
        at hG_le_both

      have ha_inf_OG : a ⊓ (Γ.O ⊔ G) = ⊥ := by
        rcases ha.le_iff.mp (inf_le_left : a ⊓ (Γ.O ⊔ G) ≤ a) with h | h
        · exact h
        · exfalso
          have ha_le : a ≤ Γ.O ⊔ G := h ▸ inf_le_right
          have hO_ne_G : Γ.O ≠ G := fun heq => hG_not_l (heq ▸ hOa_eq_l ▸ le_sup_left)
          have hO_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
            (fun heq => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans heq.symm.le)).resolve_left ha.1))
          exact hG_not_l (hOa_eq_l ▸
            ((atom_covBy_join Γ.hO hG_atom hO_ne_G).eq_or_eq hO_lt.le
              (sup_le le_sup_left ha_le)).resolve_left (ne_of_gt hO_lt) ▸ le_sup_right)
      rw [ha_inf_OG, sup_bot_eq] at hG_le_both

      exact hG_not_m (hG_le_both.trans inf_le_right)

    have hG_ne_b : G ≠ b := fun h => hG_not_l (h ▸ hb_on)

    have hG_ne_Cb : G ≠ C_b := fun h => hG_not_q (h ▸ hCb_le_q)

    have hCb_le_π : C_b ≤ π :=
      hCb_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)

    have hG'_le_GU : G' ≤ G ⊔ Γ.U := by
      have h1 : G' ≤ G ⊔ (Γ.O ⊔ a) ⊓ m := by
        show parallelogram_completion Γ.O a G m ≤ _
        unfold parallelogram_completion; exact inf_le_left
      exact h1.trans (sup_le le_sup_left
        (by rw [hOa_eq_l, Γ.l_inf_m_eq_U]; exact le_sup_right))

    have hGG'_le_GU : G ⊔ G' ≤ G ⊔ Γ.U := sup_le le_sup_left hG'_le_GU

    have hG_inf_l : G ⊓ l = ⊥ :=
      (hG_atom.le_iff.mp inf_le_left).resolve_right (fun h => hG_not_l (h ▸ inf_le_right))

    have hG_inf_q : G ⊓ q = ⊥ :=
      (hG_atom.le_iff.mp inf_le_left).resolve_right (fun h => hG_not_q (h ▸ inf_le_right))

    have hb_not_GG' : ¬ b ≤ G ⊔ G' := by
      intro hb_le
      have : b ≤ (G ⊔ Γ.U) ⊓ l := le_inf (hb_le.trans hGG'_le_GU) hb_on
      rw [sup_comm G _, sup_inf_assoc_of_le G (le_sup_right : Γ.U ≤ l),
          hG_inf_l, sup_bot_eq] at this
      exact hb_ne_U ((Γ.hU.le_iff.mp this).resolve_left hb.1)

    have hCb_not_GG' : ¬ C_b ≤ G ⊔ G' := by
      intro hCb_le
      have : C_b ≤ (G ⊔ Γ.U) ⊓ q := le_inf (hCb_le.trans hGG'_le_GU) hCb_le_q
      rw [sup_comm G _, sup_inf_assoc_of_le G (le_sup_left : Γ.U ≤ q),
          hG_inf_q, sup_bot_eq] at this
      exact hCb_not_m ((Γ.hU.le_iff.mp this).resolve_left hCb_atom.1 ▸ le_sup_left)

    have hC_not_bE : ¬ Γ.C ≤ b ⊔ Γ.E := by
      intro hC_le
      have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
        have : Γ.E ≤ Γ.O ⊔ Γ.C := Γ.hE_le_OC
        have hCE_le : Γ.C ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_right this
        have hCE_cov : Γ.C ⋖ Γ.C ⊔ Γ.E := atom_covBy_join Γ.hC Γ.hE_atom
          (fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m))
        have hOC_cov : Γ.C ⋖ Γ.C ⊔ Γ.O := atom_covBy_join Γ.hC Γ.hO
          (fun h => Γ.hC_not_l (h ▸ le_sup_left))
        rw [sup_comm] at hOC_cov
        exact (hOC_cov.eq_or_eq hCE_cov.lt.le hCE_le).resolve_left
          (ne_of_gt hCE_cov.lt)
      have hO_le_bE : Γ.O ≤ b ⊔ Γ.E := by
        have : Γ.O ⊔ Γ.C ≤ b ⊔ Γ.E := hCE_eq ▸ sup_le hC_le le_sup_right
        exact le_sup_left.trans this
      have hbE_inf_l : (b ⊔ Γ.E) ⊓ l = b := by
        rw [sup_comm, inf_comm]
        exact inf_sup_of_atom_not_le Γ.hE_atom Γ.hE_not_l hb_on
      have hO_le_b : Γ.O ≤ b := by
        have : Γ.O ≤ (b ⊔ Γ.E) ⊓ l := le_inf hO_le_bE le_sup_left
        rwa [hbE_inf_l] at this
      exact hb_ne_O ((hb.le_iff.mp hO_le_b).resolve_left Γ.hO.1).symm

    have hCb_not_Gb : ¬ C_b ≤ G ⊔ b := by
      intro hCb_le

      have hCb_le_Gb : b ⊔ C_b ≤ G ⊔ b := sup_le le_sup_right hCb_le
      have hCb_le_bE' : b ⊔ C_b ≤ b ⊔ Γ.E := h_bCb_eq_bE ▸ le_refl _
      have hGb_eq_bE : G ⊔ b = b ⊔ Γ.E := by
        have hcov1 := atom_covBy_join hb hG_atom hG_ne_b_raw.symm
        rw [sup_comm] at hcov1
        have hcov2 := atom_covBy_join hb Γ.hE_atom
          (fun h => Γ.hE_not_l (h ▸ hb_on))
        have hbCb_cov : b ⋖ b ⊔ C_b := atom_covBy_join hb hCb_atom hb_ne_Cb
        exact (hcov1.eq_or_eq hbCb_cov.lt.le hCb_le_Gb).resolve_left
          (ne_of_gt hbCb_cov.lt) |>.symm.trans
          ((hcov2.eq_or_eq hbCb_cov.lt.le hCb_le_bE').resolve_left
            (ne_of_gt hbCb_cov.lt))

      have hG_le_bE : G ≤ b ⊔ Γ.E := hGb_eq_bE ▸ le_sup_left
      have hG_le_meet : G ≤ (b ⊔ Γ.C) ⊓ (b ⊔ Γ.E) := le_inf hG_le_bC hG_le_bE
      rw [sup_inf_assoc_of_le Γ.C (le_sup_left : b ≤ b ⊔ Γ.E)] at hG_le_meet
      have hC_inf_bE : Γ.C ⊓ (b ⊔ Γ.E) = ⊥ :=
        (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => hC_not_bE (h ▸ inf_le_right))
      rw [hC_inf_bE, sup_bot_eq] at hG_le_meet
      exact hG_ne_b_raw ((hb.le_iff.mp hG_le_meet).resolve_left hG_atom.1)

    have hG'_ne_b' : G' ≠ parallelogram_completion G G' b m := by
      intro h_eq
      have hle : G' ≤ b ⊔ (G ⊔ G') ⊓ m :=
        h_eq.le.trans (by unfold parallelogram_completion; exact inf_le_left)
      have h1 : G' ≤ (b ⊔ (G ⊔ G') ⊓ m) ⊓ (G ⊔ G') := le_inf hle le_sup_right
      rw [sup_comm b _, sup_inf_assoc_of_le b
        (inf_le_left : (G ⊔ G') ⊓ m ≤ G ⊔ G')] at h1
      have hb_inf : b ⊓ (G ⊔ G') = ⊥ :=
        (hb.le_iff.mp inf_le_left).resolve_right (fun h => hb_not_GG' (h ▸ inf_le_right))
      rw [hb_inf, sup_bot_eq] at h1
      exact hG'_not_m (h1.trans inf_le_right)

    have hG'_ne_Cb' : G' ≠ parallelogram_completion G G' C_b m := by
      intro h_eq
      have hle : G' ≤ C_b ⊔ (G ⊔ G') ⊓ m :=
        h_eq.le.trans (by unfold parallelogram_completion; exact inf_le_left)
      have h1 : G' ≤ (C_b ⊔ (G ⊔ G') ⊓ m) ⊓ (G ⊔ G') := le_inf hle le_sup_right
      rw [sup_comm C_b _, sup_inf_assoc_of_le C_b
        (inf_le_left : (G ⊔ G') ⊓ m ≤ G ⊔ G')] at h1
      have hCb_inf : C_b ⊓ (G ⊔ G') = ⊥ :=
        (hCb_atom.le_iff.mp inf_le_left).resolve_right
          (fun h => hCb_not_GG' (h ▸ inf_le_right))
      rw [hCb_inf, sup_bot_eq] at h1
      exact hG'_not_m (h1.trans inf_le_right)
    have hb'_ne_Cb' : parallelogram_completion G G' b m ≠
                       parallelogram_completion G G' C_b m := by
      intro h_eq

      have hG_ne_U : G ≠ Γ.U := fun h => hG_not_m (h ▸ le_sup_left)
      have hGG'_eq_GU : G ⊔ G' = G ⊔ Γ.U :=
        ((atom_covBy_join hG_atom Γ.hU hG_ne_U).eq_or_eq
          (atom_covBy_join hG_atom hG'_atom hGG').lt.le hGG'_le_GU).resolve_left
          (ne_of_gt (atom_covBy_join hG_atom hG'_atom hGG').lt)
      have hG_inf_m : G ⊓ m = ⊥ :=
        (hG_atom.le_iff.mp inf_le_left).resolve_right
          (fun h => hG_not_m (h ▸ inf_le_right))
      have hd_eq_U : (G ⊔ G') ⊓ m = Γ.U := by
        rw [hGG'_eq_GU, sup_comm, sup_inf_assoc_of_le G (le_sup_left : Γ.U ≤ m),
            hG_inf_m, sup_bot_eq]

      have hCb_not_l : ¬ C_b ≤ l := by
        intro h
        have : C_b ≤ l ⊓ q := le_inf h hCb_le_q
        rw [hlq_eq_U] at this
        exact hCb_not_m ((Γ.hU.le_iff.mp this).resolve_left hCb_atom.1 ▸ le_sup_left)

      have hb'_le_bU : parallelogram_completion G G' b m ≤ b ⊔ Γ.U := by
        have h := show parallelogram_completion G G' b m ≤ b ⊔ (G ⊔ G') ⊓ m from by
          unfold parallelogram_completion; exact inf_le_left
        rwa [hd_eq_U] at h

      have hb'_le_CbU : parallelogram_completion G G' b m ≤ C_b ⊔ Γ.U := by
        have h := show parallelogram_completion G G' C_b m ≤ C_b ⊔ (G ⊔ G') ⊓ m from by
          unfold parallelogram_completion; exact inf_le_left
        rw [hd_eq_U] at h; exact h_eq.le.trans h

      have hbU_eq_l : b ⊔ Γ.U = l := by
        show b ⊔ Γ.U = Γ.O ⊔ Γ.U
        rw [sup_comm b, sup_comm Γ.O]
        exact ((atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm).eq_or_eq
          (atom_covBy_join Γ.hU hb (fun h => hb_ne_U h.symm)).lt.le
          (sup_le le_sup_left (hb_on.trans (sup_comm Γ.O Γ.U).le))).resolve_left
          (ne_of_gt (atom_covBy_join Γ.hU hb (fun h => hb_ne_U h.symm)).lt)

      have hb'_le_U : parallelogram_completion G G' b m ≤ Γ.U := by
        have hCbU_inf_l : (C_b ⊔ Γ.U) ⊓ l = Γ.U :=
          line_direction hCb_atom hCb_not_l (show Γ.U ≤ l from le_sup_right)
        calc parallelogram_completion G G' b m
            ≤ l ⊓ (C_b ⊔ Γ.U) := le_inf (hb'_le_bU.trans hbU_eq_l.le) hb'_le_CbU
          _ = (C_b ⊔ Γ.U) ⊓ l := inf_comm _ _
          _ = Γ.U := hCbU_inf_l

      have hb'_le_m : parallelogram_completion G G' b m ≤ m :=
        hb'_le_U.trans (le_sup_left : Γ.U ≤ m)

      have hb'_le_eb : parallelogram_completion G G' b m ≤ (G ⊔ b) ⊓ m := by
        have h1 : parallelogram_completion G G' b m ≤ G' ⊔ (G ⊔ b) ⊓ m := by
          unfold parallelogram_completion; exact inf_le_right
        have h2 := le_inf h1 hb'_le_m
        rwa [line_direction hG'_atom hG'_not_m (inf_le_right : (G ⊔ b) ⊓ m ≤ m)] at h2

      have hb'_le_eCb : parallelogram_completion G G' b m ≤ (G ⊔ C_b) ⊓ m := by
        have h1 : parallelogram_completion G G' C_b m ≤ G' ⊔ (G ⊔ C_b) ⊓ m := by
          unfold parallelogram_completion; exact inf_le_right
        have h2 := le_inf (h_eq.le.trans h1) hb'_le_m
        rwa [line_direction hG'_atom hG'_not_m (inf_le_right : (G ⊔ C_b) ⊓ m ≤ m)] at h2

      have heb_atom : IsAtom ((G ⊔ b) ⊓ m) :=
        line_meets_m_at_atom hG_atom hb hG_ne_b
          (sup_le hG_le_π (hb_on.trans le_sup_left)) hm_le_π hm_cov hG_not_m
      have heCb_atom : IsAtom ((G ⊔ C_b) ⊓ m) :=
        line_meets_m_at_atom hG_atom hCb_atom hG_ne_Cb
          (sup_le hG_le_π hCb_le_π) hm_le_π hm_cov hG_not_m
      have heb_ne_eCb : (G ⊔ b) ⊓ m ≠ (G ⊔ C_b) ⊓ m := by
        intro h_eq_dir
        have heb_le_GCb : (G ⊔ b) ⊓ m ≤ G ⊔ C_b := by
          calc (G ⊔ b) ⊓ m = (G ⊔ C_b) ⊓ m := h_eq_dir
            _ ≤ G ⊔ C_b := inf_le_left
        have heb_le_G : (G ⊔ b) ⊓ m ≤ G := by
          have h := le_inf (inf_le_left : (G ⊔ b) ⊓ m ≤ G ⊔ b) heb_le_GCb
          rwa [modular_intersection hG_atom hb hCb_atom hG_ne_b hG_ne_Cb hb_ne_Cb hCb_not_Gb] at h
        exact hG_not_m ((hG_atom.le_iff.mp heb_le_G).resolve_left heb_atom.1 ▸
          (inf_le_right : (G ⊔ b) ⊓ m ≤ m))

      have hb'_atom : IsAtom (parallelogram_completion G G' b m) :=
        parallelogram_completion_atom hG_atom hG'_atom hb
          hGG' hG_ne_b
          (fun h => hb_not_GG' ((le_of_eq h.symm).trans le_sup_right))
          hG_le_π hG'_le_π (hb_on.trans le_sup_left)
          hm_le_π hm_cov hm_line
          hG_not_m hG'_not_m hb_not_m hb_not_GG'

      have h_meet_bot : (G ⊔ b) ⊓ m ⊓ ((G ⊔ C_b) ⊓ m) = ⊥ := by
        rcases heb_atom.le_iff.mp (inf_le_left) with h | h
        · exact h
        · exact absurd ((heCb_atom.le_iff.mp
            (le_of_eq h.symm |>.trans inf_le_right)).resolve_left heb_atom.1) heb_ne_eCb
      exact hb'_atom.1 (le_antisymm
        (h_meet_bot.symm ▸ le_inf hb'_le_eb hb'_le_eCb) bot_le)

    have h_span : G ⊔ b ⊔ C_b = π := by
      apply le_antisymm
      · exact sup_le (sup_le hG_le_π (hb_on.trans le_sup_left)) hCb_le_π
      ·

        have hGb_eq_bC : G ⊔ b = b ⊔ Γ.C := by
          have hGb_le : G ⊔ b ≤ b ⊔ Γ.C := sup_le hG_le_bC le_sup_left
          have hcov1 : b ⋖ b ⊔ G := atom_covBy_join hb hG_atom hG_ne_b_raw.symm
          have hcov2 : b ⋖ b ⊔ Γ.C := atom_covBy_join hb Γ.hC hb_ne_C
          rw [sup_comm] at hcov1
          exact (hcov2.eq_or_eq hcov1.lt.le hGb_le).resolve_left (ne_of_gt hcov1.lt)
        have hC_le : Γ.C ≤ G ⊔ b ⊔ C_b :=
          (le_sup_right.trans hGb_eq_bC.symm.le).trans le_sup_left

        have hC_ne_Cb : Γ.C ≠ C_b := by
          intro h; exact hC_not_bE (h ▸ hCb_le_bE)
        have hCCb_eq_q : Γ.C ⊔ C_b = q := by
          have hCCb_le : Γ.C ⊔ C_b ≤ q := sup_le (le_sup_right : Γ.C ≤ Γ.U ⊔ Γ.C) hCb_le_q
          have hcov1 : Γ.C ⋖ Γ.C ⊔ C_b := atom_covBy_join Γ.hC hCb_atom hC_ne_Cb
          have hcov2 : Γ.C ⋖ q := by
            show Γ.C ⋖ Γ.U ⊔ Γ.C; rw [sup_comm]
            exact atom_covBy_join Γ.hC Γ.hU
              (fun h => Γ.hC_not_l (h ▸ le_sup_right))
          exact (hcov2.eq_or_eq hcov1.lt.le hCCb_le).resolve_left (ne_of_gt hcov1.lt)

        have hU_le : Γ.U ≤ G ⊔ b ⊔ C_b := by
          have : Γ.U ≤ q := le_sup_left
          exact this.trans (hCCb_eq_q ▸ sup_le hC_le le_sup_right)

        have hl_le : l ≤ G ⊔ b ⊔ C_b := by
          have hb_le : b ≤ G ⊔ b ⊔ C_b := le_sup_right.trans le_sup_left
          have hbU : b ⊔ Γ.U ≤ G ⊔ b ⊔ C_b := sup_le hb_le hU_le
          have hbU_eq_l : b ⊔ Γ.U = l := by
            have hcov1 : Γ.U ⋖ Γ.U ⊔ b := atom_covBy_join Γ.hU hb hb_ne_U.symm
            have hcov2 : Γ.U ⋖ l := by
              show Γ.U ⋖ Γ.O ⊔ Γ.U; rw [sup_comm]
              exact atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm
            have hbU_le : Γ.U ⊔ b ≤ l := sup_le le_sup_right hb_on
            exact (sup_comm Γ.U b).symm.trans
              ((hcov2.eq_or_eq hcov1.lt.le hbU_le).resolve_left (ne_of_gt hcov1.lt))
          rwa [hbU_eq_l] at hbU

        have hlC_eq_π : l ⊔ Γ.C = π := by
          have hlC_le : l ⊔ Γ.C ≤ π := sup_le le_sup_left Γ.hC_plane
          have hl_cov : l ⋖ π := by
            have hV_inf_l : Γ.V ⊓ l = ⊥ := by
              exact (Γ.hV.le_iff.mp inf_le_left).resolve_right
                (fun h => Γ.hV_off (h ▸ inf_le_right))
            show l ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
            rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = l ⊔ Γ.V from rfl]
            rw [sup_comm l Γ.V]
            exact covBy_sup_of_inf_covBy_left (hV_inf_l ▸ Γ.hV.bot_covBy)
          have hlC_gt : l < l ⊔ Γ.C := by
            apply lt_of_le_of_ne le_sup_left
            intro h
            have hC_le_l : Γ.C ≤ l := by
              have : l ⊔ Γ.C ≤ l := h.symm.le
              exact le_sup_right.trans this
            exact Γ.hC_not_l hC_le_l
          exact (hl_cov.eq_or_eq hlC_gt.le hlC_le).resolve_left (ne_of_gt hlC_gt)
        rw [← hlC_eq_π]
        exact sup_le hl_le hC_le

    have hwd1 : parallelogram_completion G G' b m = s := by

      set C_a := parallelogram_completion Γ.O a Γ.C m
      have hs_eq : s = parallelogram_completion Γ.C C_a b m := h_s_transl
      rw [hs_eq]

      change (b ⊔ (G ⊔ G') ⊓ m) ⊓ (G' ⊔ (G ⊔ b) ⊓ m) =
             (b ⊔ (Γ.C ⊔ C_a) ⊓ m) ⊓ (C_a ⊔ (Γ.C ⊔ b) ⊓ m)

      have hG_ne_U : G ≠ Γ.U := fun h => hG_not_m (h ▸ le_sup_left)
      have hGG'_eq_GU : G ⊔ G' = G ⊔ Γ.U :=
        ((atom_covBy_join hG_atom Γ.hU hG_ne_U).eq_or_eq
          (atom_covBy_join hG_atom hG'_atom hGG').lt.le hGG'_le_GU).resolve_left
          (ne_of_gt (atom_covBy_join hG_atom hG'_atom hGG').lt)
      have hG_inf_m : G ⊓ m = ⊥ :=
        (hG_atom.le_iff.mp inf_le_left).resolve_right
          (fun h => hG_not_m (h ▸ inf_le_right))
      have hGG'_dir : (G ⊔ G') ⊓ m = Γ.U := by
        rw [hGG'_eq_GU, sup_comm, sup_inf_assoc_of_le G (le_sup_left : Γ.U ≤ m),
            hG_inf_m, sup_bot_eq]

      have hGb_eq_bC : G ⊔ b = b ⊔ Γ.C := by
        have hcov1 : b ⋖ b ⊔ G := atom_covBy_join hb hG_atom hG_ne_b.symm
        rw [sup_comm] at hcov1
        exact ((atom_covBy_join hb Γ.hC hb_ne_C).eq_or_eq hcov1.lt.le
          (sup_le hG_le_bC le_sup_left)).resolve_left (ne_of_gt hcov1.lt)

      have hCa_le_CU : C_a ≤ Γ.C ⊔ Γ.U := by
        have h1 : C_a ≤ Γ.C ⊔ (Γ.O ⊔ a) ⊓ m := by
          show parallelogram_completion Γ.O a Γ.C m ≤ _
          unfold parallelogram_completion; exact inf_le_left
        exact h1.trans (sup_le le_sup_left
          (by rw [hOa_eq_l, Γ.l_inf_m_eq_U]; exact le_sup_right))
      have hC_ne_Ca : Γ.C ≠ C_a := by
        intro h_eq
        have hCa_le2 : C_a ≤ a ⊔ (Γ.O ⊔ Γ.C) ⊓ m := by
          show parallelogram_completion Γ.O a Γ.C m ≤ _
          unfold parallelogram_completion; exact inf_le_right
        have hC_le_both : Γ.C ≤ ((Γ.O ⊔ Γ.C) ⊓ m ⊔ a) ⊓ (Γ.O ⊔ Γ.C) :=
          le_inf (sup_comm a _ ▸ (h_eq ▸ hCa_le2)) le_sup_right
        rw [sup_inf_assoc_of_le a (inf_le_left : (Γ.O ⊔ Γ.C) ⊓ m ≤ Γ.O ⊔ Γ.C)]
          at hC_le_both
        have ha_not_OC : ¬ a ≤ Γ.O ⊔ Γ.C := by
          intro ha_le
          have hU_ne_C : Γ.U ≠ Γ.C := fun h => Γ.hC_not_m (h ▸ le_sup_left)
          have h_lOC : l ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
            modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU hOC hU_ne_C Γ.hC_not_l
          have ha_le_O : a ≤ Γ.O := by
            have := le_inf ha_on ha_le; rw [h_lOC] at this; exact this
          exact ha_ne_O ((Γ.hO.le_iff.mp ha_le_O).resolve_left ha.1)
        have : a ⊓ (Γ.O ⊔ Γ.C) = ⊥ :=
          (ha.le_iff.mp inf_le_left).resolve_right
            (fun h => ha_not_OC (h ▸ inf_le_right))
        rw [this, sup_bot_eq] at hC_le_both
        exact Γ.hC_not_m (hC_le_both.trans inf_le_right)

      have hO_ne_G : Γ.O ≠ G := fun h => hG_not_l (h ▸ le_sup_left)
      have hCa_atom : IsAtom C_a :=
        parallelogram_completion_atom Γ.hO ha Γ.hC
          (fun h => ha_ne_O h.symm) hOC
          (fun h => Γ.hC_not_l (h ▸ ha_on))
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) Γ.hC_plane
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m Γ.hC_not_m
          (fun h => Γ.hC_not_l (h.trans hOa_eq_l.le))

      have hCa_not_m : ¬ C_a ≤ m := by
        intro hCa_m

        have hCa_le_U : C_a ≤ Γ.U := by
          have h : C_a ≤ (Γ.C ⊔ Γ.U) ⊓ m := le_inf hCa_le_CU hCa_m
          rw [sup_comm, sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ m)] at h
          have hCm : Γ.C ⊓ m = ⊥ :=
            (Γ.hC.le_iff.mp inf_le_left).resolve_right
              (fun h => Γ.hC_not_m (h ▸ inf_le_right))
          rwa [hCm, sup_bot_eq] at h

        have hCa_eq_U : C_a = Γ.U :=
          (Γ.hU.le_iff.mp hCa_le_U).resolve_left hCa_atom.1

        have hCa_le2 : C_a ≤ a ⊔ (Γ.O ⊔ Γ.C) ⊓ m := by
          show parallelogram_completion Γ.O a Γ.C m ≤ _
          unfold parallelogram_completion; exact inf_le_right

        have hU_le_E : Γ.U ≤ (Γ.O ⊔ Γ.C) ⊓ m := by
          have hdir : (a ⊔ (Γ.O ⊔ Γ.C) ⊓ m) ⊓ m = (Γ.O ⊔ Γ.C) ⊓ m :=
            line_direction ha ha_not_m (inf_le_right : (Γ.O ⊔ Γ.C) ⊓ m ≤ m)
          have : Γ.U ≤ (a ⊔ (Γ.O ⊔ Γ.C) ⊓ m) ⊓ m :=
            le_inf (hCa_eq_U ▸ hCa_le2) (le_sup_left : Γ.U ≤ m)
          rwa [hdir] at this

        exact Γ.hEU ((Γ.hE_atom.le_iff.mp hU_le_E).resolve_left Γ.hU.1).symm

      have hCCa_eq_CU : Γ.C ⊔ C_a = Γ.C ⊔ Γ.U := by
        have hcov1 : Γ.C ⋖ Γ.C ⊔ C_a := atom_covBy_join Γ.hC hCa_atom hC_ne_Ca
        have hcov2 : Γ.C ⋖ Γ.C ⊔ Γ.U := atom_covBy_join Γ.hC Γ.hU
          (fun h => Γ.hC_not_m (h ▸ le_sup_left))
        exact (hcov2.eq_or_eq hcov1.lt.le
          (sup_le le_sup_left hCa_le_CU)).resolve_left (ne_of_gt hcov1.lt)
      have hCCa_dir : (Γ.C ⊔ C_a) ⊓ m = Γ.U := by
        rw [hCCa_eq_CU, sup_comm, sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ m)]
        have : Γ.C ⊓ m = ⊥ :=
          (Γ.hC.le_iff.mp inf_le_left).resolve_right
            (fun h => Γ.hC_not_m (h ▸ inf_le_right))
        rw [this, sup_bot_eq]

      rw [hGG'_dir, hCCa_dir, hGb_eq_bC, sup_comm Γ.C b]

      have hsuff : G' ⊔ (b ⊔ Γ.C) ⊓ m = C_a ⊔ (b ⊔ Γ.C) ⊓ m := by

        have ha_ne_G' : a ≠ G' := by
          intro h_eq
          have : a ≤ (G ⊔ Γ.U) ⊓ l := le_inf (h_eq ▸ hG'_le_GU) ha_on
          rw [sup_comm G _, sup_inf_assoc_of_le G (le_sup_right : Γ.U ≤ l),
              hG_inf_l, sup_bot_eq] at this
          exact ha_ne_U ((Γ.hU.le_iff.mp this).resolve_left ha.1)

        have ha_ne_Ca : a ≠ C_a := by
          intro h_eq
          have : a ≤ l ⊓ q := le_inf ha_on
            ((h_eq ▸ hCa_le_CU).trans (sup_comm Γ.C Γ.U).le)
          rw [hlq_eq_U] at this
          exact ha_ne_U ((Γ.hU.le_iff.mp this).resolve_left ha.1)

        have hG'_ne_Ca : G' ≠ C_a := by
          intro h_eq
          have hC_not_GU : ¬ Γ.C ≤ G ⊔ Γ.U := by
            intro hC_le
            have : Γ.C ≤ (G ⊔ Γ.U) ⊓ q := le_inf hC_le (le_sup_right : Γ.C ≤ q)
            rw [sup_comm G _, sup_inf_assoc_of_le G (le_sup_left : Γ.U ≤ q),
                hG_inf_q, sup_bot_eq] at this
            exact Γ.hC_not_m ((Γ.hU.le_iff.mp this).resolve_left Γ.hC.1 ▸ le_sup_left)
          have : G' ≤ (Γ.C ⊔ Γ.U) ⊓ (G ⊔ Γ.U) :=
            le_inf (h_eq ▸ hCa_le_CU) hG'_le_GU
          rw [sup_comm Γ.C _, sup_inf_assoc_of_le Γ.C (le_sup_right : Γ.U ≤ G ⊔ Γ.U)]
            at this
          have hC_inf_GU : Γ.C ⊓ (G ⊔ Γ.U) = ⊥ :=
            (Γ.hC.le_iff.mp inf_le_left).resolve_right
              (fun h => hC_not_GU (h ▸ inf_le_right))
          rw [hC_inf_GU, sup_bot_eq] at this
          exact hG'_not_m (this.trans (le_sup_left : Γ.U ≤ m))

        have hC_not_OG : ¬ Γ.C ≤ Γ.O ⊔ G := by
          intro hC_le

          have hGC_eq_bC : G ⊔ Γ.C = b ⊔ Γ.C := by
            have hcov : G ⋖ b ⊔ Γ.C := by
              have := atom_covBy_join hG_atom hb hG_ne_b; rwa [hGb_eq_bC] at this
            exact (hcov.eq_or_eq le_sup_left (sup_le hG_le_bC le_sup_right)).resolve_left
              (ne_of_gt (lt_of_le_of_ne le_sup_left
                (fun h => hG_ne_C ((hG_atom.le_iff.mp
                  (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm)))

          have hOG_eq_π : Γ.O ⊔ G = π := by
            have h_eq : Γ.O ⊔ G ⊔ Γ.C = l ⊔ Γ.C := by
              rw [sup_assoc, hGC_eq_bC, ← sup_assoc, hOb_eq_l]
            have h_col : Γ.O ⊔ G ⊔ Γ.C = Γ.O ⊔ G :=
              le_antisymm (sup_le le_rfl hC_le) le_sup_left

            have hl_cov_π : l ⋖ π := by
              have hV_inf_l : Γ.V ⊓ l = ⊥ :=
                (Γ.hV.le_iff.mp inf_le_left).resolve_right
                  (fun h => Γ.hV_off (h ▸ inf_le_right))
              show l ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
              rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = l ⊔ Γ.V from rfl, sup_comm l Γ.V]
              exact covBy_sup_of_inf_covBy_left (hV_inf_l ▸ Γ.hV.bot_covBy)
            have hlC_eq_π : l ⊔ Γ.C = π := by
              have hlC_gt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
                (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
              exact (hl_cov_π.eq_or_eq hlC_gt.le
                (sup_le le_sup_left Γ.hC_plane)).resolve_left hlC_gt.ne'
            rw [← h_col, h_eq, hlC_eq_π]

          have hO_lt_l : Γ.O < l := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hOU ((Γ.hO.le_iff.mp
              (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1).symm)
          exact hG_not_l (((atom_covBy_join Γ.hO hG_atom hO_ne_G).eq_or_eq hO_lt_l.le
            (hOG_eq_π ▸ le_sup_left)).resolve_left hO_lt_l.ne' ▸ le_sup_right)

        have hOGC_span : Γ.O ⊔ G ⊔ Γ.C = π := by
          have hGC_eq_bC : G ⊔ Γ.C = b ⊔ Γ.C := by
            have hcov : G ⋖ b ⊔ Γ.C := by
              have := atom_covBy_join hG_atom hb hG_ne_b; rwa [hGb_eq_bC] at this
            exact (hcov.eq_or_eq le_sup_left (sup_le hG_le_bC le_sup_right)).resolve_left
              (ne_of_gt (lt_of_le_of_ne le_sup_left
                (fun h => hG_ne_C ((hG_atom.le_iff.mp
                  (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm)))
          rw [sup_assoc, hGC_eq_bC, ← sup_assoc, hOb_eq_l]
          have hl_cov_π : l ⋖ π := by
            have hV_inf_l : Γ.V ⊓ l = ⊥ :=
              (Γ.hV.le_iff.mp inf_le_left).resolve_right
                (fun h => Γ.hV_off (h ▸ inf_le_right))
            show l ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
            rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = l ⊔ Γ.V from rfl, sup_comm l Γ.V]
            exact covBy_sup_of_inf_covBy_left (hV_inf_l ▸ Γ.hV.bot_covBy)
          have hlC_gt : l < l ⊔ Γ.C := lt_of_le_of_ne le_sup_left
            (fun h => Γ.hC_not_l (le_sup_right.trans h.symm.le))
          exact (hl_cov_π.eq_or_eq hlC_gt.le
            (sup_le le_sup_left Γ.hC_plane)).resolve_left hlC_gt.ne'

        have hCa_le_π : C_a ≤ π :=
          hCa_le_CU.trans (sup_le Γ.hC_plane (le_sup_right.trans le_sup_left))

        have hcp := cross_parallelism Γ.hO ha hG_atom Γ.hC
          (fun h => ha_ne_O h.symm) hO_ne_G hOC hG_ne_C
          ha_ne_G' ha_ne_Ca hG'_ne_Ca
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hG_le_π Γ.hC_plane
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m hG_not_m Γ.hC_not_m
          (fun h => hG_not_l (h.trans hOa_eq_l.le))
          (fun h => Γ.hC_not_l (h.trans hOa_eq_l.le))
          hC_not_OG
          hOGC_span
          R hR hR_not h_irred

        have hGC_eq_bC : G ⊔ Γ.C = b ⊔ Γ.C := by
          have hcov : G ⋖ b ⊔ Γ.C := by
            have := atom_covBy_join hG_atom hb hG_ne_b; rwa [hGb_eq_bC] at this
          exact (hcov.eq_or_eq le_sup_left (sup_le hG_le_bC le_sup_right)).resolve_left
            (ne_of_gt (lt_of_le_of_ne le_sup_left
              (fun h => hG_ne_C ((hG_atom.le_iff.mp
                (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm)))

        have he_eq : (b ⊔ Γ.C) ⊓ m = (G' ⊔ C_a) ⊓ m := hGC_eq_bC ▸ hcp
        have he_le : (b ⊔ Γ.C) ⊓ m ≤ G' ⊔ C_a := he_eq ▸ inf_le_left

        have he_ne_G' : (b ⊔ Γ.C) ⊓ m ≠ G' := fun h => hG'_not_m (h ▸ inf_le_right)
        have he_ne_Ca : (b ⊔ Γ.C) ⊓ m ≠ C_a := fun h => hCa_not_m (h ▸ inf_le_right)
        have he_atom : IsAtom ((b ⊔ Γ.C) ⊓ m) := line_meets_m_at_atom hb Γ.hC hb_ne_C
          (sup_le (hb_on.trans le_sup_left) Γ.hC_plane) hm_le_π hm_cov hb_not_m

        have hG'_lt : G' < G' ⊔ (b ⊔ Γ.C) ⊓ m := lt_of_le_of_ne le_sup_left
          (fun h => he_ne_G' ((hG'_atom.le_iff.mp
            (le_sup_right.trans h.symm.le)).resolve_left he_atom.1))

        have hCa_lt : C_a < C_a ⊔ (b ⊔ Γ.C) ⊓ m := lt_of_le_of_ne le_sup_left
          (fun h => he_ne_Ca ((hCa_atom.le_iff.mp
            (le_sup_right.trans h.symm.le)).resolve_left he_atom.1))

        have hG'e_eq : G' ⊔ (b ⊔ Γ.C) ⊓ m = G' ⊔ C_a :=
          ((atom_covBy_join hG'_atom hCa_atom hG'_ne_Ca).eq_or_eq hG'_lt.le
            (sup_le le_sup_left he_le)).resolve_left hG'_lt.ne'

        have hCae_le : C_a ⊔ (b ⊔ Γ.C) ⊓ m ≤ C_a ⊔ G' :=
          sup_le le_sup_left (he_le.trans (sup_comm G' C_a).le)
        have hCae_eq : C_a ⊔ (b ⊔ Γ.C) ⊓ m = C_a ⊔ G' :=
          ((atom_covBy_join hCa_atom hG'_atom hG'_ne_Ca.symm).eq_or_eq
            hCa_lt.le hCae_le).resolve_left hCa_lt.ne'

        exact hG'e_eq.trans ((sup_comm G' C_a).trans hCae_eq.symm)
      rw [hsuff]

    have hwd2 : parallelogram_completion G G' C_b m = τ_a_C_b := by

      change (C_b ⊔ (G ⊔ G') ⊓ m) ⊓ (G' ⊔ (G ⊔ C_b) ⊓ m) =
             (C_b ⊔ (Γ.O ⊔ a) ⊓ m) ⊓ (a ⊔ (Γ.O ⊔ C_b) ⊓ m)
      have hO_ne_G : Γ.O ≠ G := fun h => hG_not_l (h ▸ le_sup_left)
      have hO_ne_Cb : Γ.O ≠ C_b := by
        intro h
        have hO_le_q : Γ.O ≤ q := h ▸ hCb_le_q
        exact Γ.hOU ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf le_sup_left hO_le_q)).resolve_left Γ.hO.1)

      have hG_ne_U : G ≠ Γ.U := fun h => hG_not_m (h ▸ le_sup_left)
      have hGG'_eq_GU : G ⊔ G' = G ⊔ Γ.U := by
        have hcov1 : G ⋖ G ⊔ G' := atom_covBy_join hG_atom hG'_atom hGG'
        have hcov2 : G ⋖ G ⊔ Γ.U := atom_covBy_join hG_atom Γ.hU hG_ne_U
        exact (hcov2.eq_or_eq hcov1.lt.le hGG'_le_GU).resolve_left
          (ne_of_gt hcov1.lt)
      have hGG'_inf_m : (G ⊔ G') ⊓ m = Γ.U := by
        rw [hGG'_eq_GU, sup_comm]
        rw [sup_inf_assoc_of_le G (le_sup_left : Γ.U ≤ m)]
        have : G ⊓ m = ⊥ :=
          (hG_atom.le_iff.mp inf_le_left).resolve_right (fun h => hG_not_m (h ▸ inf_le_right))
        rw [this, sup_bot_eq]
      have hOa_inf_m : (Γ.O ⊔ a) ⊓ m = Γ.U := by
        rw [hOa_eq_l]; exact Γ.l_inf_m_eq_U
      have h_dir : (G ⊔ G') ⊓ m = (Γ.O ⊔ a) ⊓ m := by
        rw [hGG'_inf_m, hOa_inf_m]
      by_cases hCb_OG : C_b ≤ Γ.O ⊔ G
      ·

        have hOCb_eq : Γ.O ⊔ C_b = Γ.O ⊔ G := by
          have hle : Γ.O ⊔ C_b ≤ Γ.O ⊔ G := sup_le le_sup_left hCb_OG
          have hcov1 : Γ.O ⋖ Γ.O ⊔ C_b := atom_covBy_join Γ.hO hCb_atom hO_ne_Cb
          have hcov2 : Γ.O ⋖ Γ.O ⊔ G := atom_covBy_join Γ.hO hG_atom hO_ne_G
          exact (hcov2.eq_or_eq hcov1.lt.le hle).resolve_left (ne_of_gt hcov1.lt)
        have hGCb_eq : G ⊔ C_b = Γ.O ⊔ G := by
          have hle : G ⊔ C_b ≤ Γ.O ⊔ G := sup_le le_sup_right hCb_OG
          have hcov1 : G ⋖ G ⊔ C_b := atom_covBy_join hG_atom hCb_atom hG_ne_Cb
          have hcov2 : G ⋖ Γ.O ⊔ G := by
            rw [sup_comm]; exact atom_covBy_join hG_atom Γ.hO hO_ne_G.symm
          exact (hcov2.eq_or_eq hcov1.lt.le hle).resolve_left (ne_of_gt hcov1.lt)

        set f := (Γ.O ⊔ G) ⊓ m
        have hG'_le_af : G' ≤ a ⊔ f := by
          show parallelogram_completion Γ.O a G m ≤ a ⊔ f
          unfold parallelogram_completion
          rw [hOa_inf_m]
          exact inf_le_right

        have hf_atom : IsAtom f := line_meets_m_at_atom Γ.hO hG_atom hO_ne_G
          (sup_le (le_sup_left.trans le_sup_left) hG_le_π)
          (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
          hm_cov Γ.hO_not_m

        have hG'_ne_f : G' ≠ f := fun h => hG'_not_m (h ▸ inf_le_right)
        have ha_ne_f : a ≠ f := fun h => ha_not_m (h ▸ inf_le_right)
        have hG'f_eq_af : G' ⊔ f = a ⊔ f := by
          have hle : G' ⊔ f ≤ a ⊔ f := sup_le hG'_le_af le_sup_right
          have hcov1 : f ⋖ G' ⊔ f := by
            have := atom_covBy_join hf_atom hG'_atom hG'_ne_f.symm; rwa [sup_comm] at this
          have hcov2 : f ⋖ a ⊔ f := by
            have := atom_covBy_join hf_atom ha ha_ne_f.symm; rwa [sup_comm] at this
          exact (hcov2.eq_or_eq hcov1.lt.le hle).resolve_left hcov1.lt.ne'

        have h_line : G' ⊔ (G ⊔ C_b) ⊓ m = a ⊔ (Γ.O ⊔ C_b) ⊓ m := by
          rw [hGCb_eq, hOCb_eq]; exact hG'f_eq_af
        rw [h_dir, h_line]
      ·

        have ha_ne_G : a ≠ G := fun h => hG_not_l (h ▸ ha_on)
        have hCb_not_l' : ¬ C_b ≤ l := by
          intro h
          have : C_b ≤ l ⊓ q := le_inf h hCb_le_q
          rw [hlq_eq_U] at this
          exact hCb_not_m ((Γ.hU.le_iff.mp this).resolve_left hCb_atom.1 ▸ le_sup_left)
        have ha_ne_Cb : a ≠ C_b := fun h => hCb_not_l' (h ▸ ha_on)
        have hG_not_OCb : ¬ G ≤ Γ.O ⊔ C_b := by
          intro hG_le
          exact hCb_OG (le_sup_right.trans
            (((atom_covBy_join Γ.hO hCb_atom hO_ne_Cb).eq_or_eq
              (atom_covBy_join Γ.hO hG_atom hO_ne_G).lt.le
              (sup_le le_sup_left hG_le)).resolve_left
              (ne_of_gt (atom_covBy_join Γ.hO hG_atom hO_ne_G).lt)).symm.le)

        have hOG_Cb_span : Γ.O ⊔ G ⊔ C_b = π := by
          have hCb_inf_OG : C_b ⊓ (Γ.O ⊔ G) = ⊥ :=
            (hCb_atom.le_iff.mp inf_le_left).resolve_right
              (fun h => hCb_OG (h ▸ inf_le_right))
          have hd_atom : IsAtom ((Γ.O ⊔ G) ⊓ m) :=
            line_meets_m_at_atom Γ.hO hG_atom hO_ne_G
              (sup_le (le_sup_left.trans le_sup_left) hG_le_π)
              hm_le_π hm_cov Γ.hO_not_m
          have hπ_eq_Om : π = Γ.O ⊔ m := sup_assoc Γ.O Γ.U Γ.V
          have hm_OG_eq_π : m ⊔ (Γ.O ⊔ G) = π := by
            apply le_antisymm
            · exact sup_le hm_le_π (sup_le (le_sup_left.trans le_sup_left) hG_le_π)
            · rw [hπ_eq_Om]
              exact sup_le (le_sup_left.trans le_sup_right) le_sup_left

          have hOG_cov_π : Γ.O ⊔ G ⋖ π := by
            have hd_cov_m := hm_line _ hd_atom inf_le_right
            have h := covBy_sup_of_inf_covBy_left
              (show m ⊓ (Γ.O ⊔ G) ⋖ m from inf_comm m _ ▸ hd_cov_m)
            rwa [hm_OG_eq_π] at h

          have hOG_lt : Γ.O ⊔ G < Γ.O ⊔ G ⊔ C_b :=
            lt_of_le_of_ne le_sup_left
              (fun h => hCb_OG (le_sup_right.trans h.symm.le))
          exact (hOG_cov_π.eq_or_eq hOG_lt.le
            (sup_le (sup_le (le_sup_left.trans le_sup_left) hG_le_π) hCb_le_π)).resolve_left
            hOG_lt.ne'

        show parallelogram_completion G G' C_b m = τ_a_C_b
        exact (parallelogram_completion_well_defined Γ.hO ha hG_atom hCb_atom
          (fun h => ha_ne_O h.symm) hO_ne_G hO_ne_Cb ha_ne_G ha_ne_Cb hG_ne_Cb
          (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left) hG_le_π hCb_le_π
          hm_le_π hm_cov hm_line
          Γ.hO_not_m ha_not_m hG_not_m hCb_not_m
          (fun h => hG_not_l (hOa_eq_l ▸ h))
          (fun h => hCb_not_l' (hOa_eq_l ▸ h))
          hCb_OG hG_not_OCb hCb_not_GG'
          hOG_Cb_span
          R hR hR_not h_irred).symm

    have hcp := cross_parallelism hG_atom hG'_atom hb hCb_atom
      hGG' hG_ne_b hG_ne_Cb hb_ne_Cb
      hG'_ne_b' hG'_ne_Cb' hb'_ne_Cb'
      hG_le_π hG'_le_π (hb_on.trans le_sup_left) hCb_le_π
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hm_cov hm_line
      hG_not_m hG'_not_m hb_not_m hCb_not_m
      hb_not_GG' hCb_not_GG' hCb_not_Gb
      h_span
      R hR hR_not h_irred

    rw [hwd1, hwd2] at hcp

    exact hcp.symm.trans h_bCb_dir
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hs_atom : IsAtom s :=
    coord_add_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
  have hs_on_l : s ≤ l := by
    show coord_add Γ a b ≤ Γ.O ⊔ Γ.U
    exact inf_le_right

  have hO_not_q : ¬ Γ.O ≤ q := fun h =>
    Γ.hOU ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf le_sup_left h)).resolve_left Γ.hO.1)
  have ha_not_q : ¬ a ≤ q := fun h =>
    ha_ne_U ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf ha_on h)).resolve_left ha.1)
  have hO_ne_Cb : Γ.O ≠ C_b := fun h => hO_not_q (h ▸ hCb_le_q)
  have ha_ne_Cb : a ≠ C_b := fun h => ha_not_q (h ▸ hCb_le_q)
  have hCb_not_l : ¬ C_b ≤ l := fun h => by

    have : C_b ≤ l ⊓ q := le_inf h hCb_le_q
    rw [hlq_eq_U] at this
    exact hCb_not_m ((Γ.hU.le_iff.mp this).resolve_left hCb_atom.1 ▸ le_sup_left)
  have hτ_atom : IsAtom τ_a_C_b :=
    parallelogram_completion_atom Γ.hO ha hCb_atom
      (fun h => ha_ne_O h.symm) hO_ne_Cb ha_ne_Cb
      (le_sup_left.trans le_sup_left) (ha_on.trans le_sup_left)
      (hCb_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane))
      hm_le_π hm_cov hm_line
      Γ.hO_not_m ha_not_m hCb_not_m
      (fun h => hCb_not_l (h.trans (hOa_eq_l ▸ le_refl l)))

  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hOE_eq_OC : Γ.O ⊔ Γ.E = Γ.O ⊔ Γ.C := by
    have hCE : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
    have h_lt : Γ.O < Γ.O ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => CoordSystem.hOE ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    exact ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq h_lt.le
      (sup_le le_sup_left Γ.hE_le_OC)).resolve_left (ne_of_gt h_lt)

  by_cases hs_eq_O : s = Γ.O
  ·

    have hE_le_Oτ : Γ.E ≤ Γ.O ⊔ τ_a_C_b := by
      have := h_cross; rw [hs_eq_O] at this; exact this ▸ inf_le_left

    have hO_ne_τ : Γ.O ≠ τ_a_C_b := fun h => hO_not_q (h ▸ h_τ_le_q)
    have hOC_le_Oτ : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ τ_a_C_b :=
      hOE_eq_OC ▸ sup_le le_sup_left hE_le_Oτ

    have hOτ_eq_OC : Γ.O ⊔ τ_a_C_b = Γ.O ⊔ Γ.C := by
      have hOC_lt : Γ.O < Γ.O ⊔ Γ.C := lt_of_le_of_ne le_sup_left
        (fun h => hOC ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hC.1).symm)
      exact ((atom_covBy_join Γ.hO hτ_atom hO_ne_τ).eq_or_eq hOC_lt.le
        hOC_le_Oτ).resolve_left (ne_of_gt hOC_lt) |>.symm

    have hτ_le_C : τ_a_C_b ≤ Γ.C := by
      have hτ_le_OC_q : τ_a_C_b ≤ (Γ.O ⊔ Γ.C) ⊓ q :=
        le_inf (hOτ_eq_OC ▸ le_sup_right) h_τ_le_q

      have hOC_inf_q : (Γ.O ⊔ Γ.C) ⊓ q = Γ.C := by
        have hO_inf_q : Γ.O ⊓ q = ⊥ :=
          (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => hO_not_q (h ▸ inf_le_right))
        calc (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.C)
            = (Γ.C ⊔ Γ.O) ⊓ (Γ.C ⊔ Γ.U) := by rw [sup_comm Γ.O Γ.C, sup_comm Γ.U Γ.C]
          _ = Γ.C ⊔ Γ.O ⊓ (Γ.C ⊔ Γ.U) :=
              sup_inf_assoc_of_le Γ.O (le_sup_left : Γ.C ≤ Γ.C ⊔ Γ.U)
          _ = Γ.C ⊔ Γ.O ⊓ q := by rw [show Γ.C ⊔ Γ.U = q from sup_comm Γ.C Γ.U]
          _ = Γ.C := by rw [hO_inf_q, sup_bot_eq]
      exact hOC_inf_q ▸ hτ_le_OC_q
    have hτ_eq_C : τ_a_C_b = Γ.C :=
      (Γ.hC.le_iff.mp hτ_le_C).resolve_left hτ_atom.1

    have hCs_eq_C : C_s = Γ.C := by
      show parallelogram_completion Γ.O s Γ.C m = Γ.C
      rw [hs_eq_O]; unfold parallelogram_completion
      have hO_inf_m : Γ.O ⊓ m = ⊥ :=
        (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
      simp only [sup_idem, hO_inf_m, sup_bot_eq]

      rw [show (Γ.O ⊔ Γ.C) ⊓ m = Γ.E from rfl, hOE_eq_OC]
      exact inf_eq_left.mpr le_sup_right
    exact hτ_eq_C.trans hCs_eq_C.symm

  ·
    have hs_ne_O : s ≠ Γ.O := hs_eq_O

    have hs_ne_τ : s ≠ τ_a_C_b := by
      intro h
      have hτ_le_U : τ_a_C_b ≤ Γ.U := by
        rw [← hlq_eq_U]; exact le_inf (h ▸ hs_on_l) h_τ_le_q
      have hτ_eq_U := (Γ.hU.le_iff.mp hτ_le_U).resolve_left hτ_atom.1
      have hτ_le_ad : τ_a_C_b ≤ a ⊔ (Γ.O ⊔ C_b) ⊓ m := by
        show parallelogram_completion Γ.O a C_b m ≤ _
        unfold parallelogram_completion; exact inf_le_right
      have hU_le_d : Γ.U ≤ (Γ.O ⊔ C_b) ⊓ m := by
        have : Γ.U ≤ (a ⊔ (Γ.O ⊔ C_b) ⊓ m) ⊓ m :=
          le_inf (hτ_eq_U ▸ hτ_le_ad) (le_sup_left : Γ.U ≤ m)
        rwa [line_direction ha ha_not_m inf_le_right] at this
      have hl_le_OCb : l ≤ Γ.O ⊔ C_b := sup_le le_sup_left (hU_le_d.trans inf_le_left)
      rcases (atom_covBy_join Γ.hO hCb_atom hO_ne_Cb).eq_or_eq le_sup_left hl_le_OCb with h | h
      · exact absurd h (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)
      · exact hCb_not_l (le_sup_right.trans h.symm.le)

    have hs_not_m : ¬ s ≤ m := by
      intro h_sm
      have hs_eq_U : s = Γ.U :=
        (Γ.hU.le_iff.mp (Γ.l_inf_m_eq_U ▸ le_inf hs_on_l h_sm)).resolve_left hs_atom.1
      have hτ_ne_U : τ_a_C_b ≠ Γ.U :=
        fun hτU => hs_ne_τ (hs_eq_U.trans hτU.symm)
      have hUτ_dir : (Γ.U ⊔ τ_a_C_b) ⊓ m = Γ.E := by
        have := h_cross; rwa [hs_eq_U] at this
      by_cases hτm : τ_a_C_b ≤ m
      ·
        rw [inf_eq_left.mpr (sup_le le_sup_left hτm)] at hUτ_dir
        exact Γ.hEU ((Γ.hE_atom.le_iff.mp
          (hUτ_dir ▸ (atom_covBy_join Γ.hU hτ_atom hτ_ne_U.symm).lt.le)).resolve_left Γ.hU.1).symm
      ·
        rw [show Γ.U ⊔ τ_a_C_b = τ_a_C_b ⊔ Γ.U from sup_comm _ _,
            line_direction hτ_atom hτm (le_sup_left : Γ.U ≤ m)] at hUτ_dir
        exact Γ.hEU hUτ_dir.symm
    have hs_ne_C : s ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hs_on_l)
    have hOs_eq_l : Γ.O ⊔ s = l := by
      have h_lt : Γ.O < Γ.O ⊔ s := lt_of_le_of_ne le_sup_left
        (fun h => hs_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          hs_atom.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hs_on_l)).resolve_left (ne_of_gt h_lt)
    have hCs_atom : IsAtom C_s :=
      parallelogram_completion_atom Γ.hO hs_atom Γ.hC hs_ne_O.symm hOC hs_ne_C
        (le_sup_left.trans le_sup_left) (hs_on_l.trans le_sup_left) Γ.hC_plane
        hm_le_π hm_cov hm_line
        Γ.hO_not_m hs_not_m Γ.hC_not_m
        (fun h => Γ.hC_not_l (h.trans (hOs_eq_l ▸ le_refl l)))

    have hE_le : Γ.E ≤ s ⊔ τ_a_C_b := h_cross ▸ inf_le_left
    have hsE_le_sτ : s ⊔ Γ.E ≤ s ⊔ τ_a_C_b := sup_le le_sup_left hE_le

    have hs_ne_E : s ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hs_on_l)
    have h_sE_eq_sτ : s ⊔ Γ.E = s ⊔ τ_a_C_b := by
      have h_lt : s < s ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h => hs_ne_E ((hs_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          Γ.hE_atom.1).symm)
      exact ((atom_covBy_join hs_atom hτ_atom hs_ne_τ).eq_or_eq h_lt.le
        hsE_le_sτ).resolve_left (ne_of_gt h_lt)
    have h_τ_le_sE : τ_a_C_b ≤ s ⊔ Γ.E := h_sE_eq_sτ ▸ le_sup_right

    have h_τ_le_Cs : τ_a_C_b ≤ C_s := by
      show τ_a_C_b ≤ (Γ.C ⊔ (Γ.O ⊔ s) ⊓ m) ⊓ (s ⊔ (Γ.O ⊔ Γ.C) ⊓ m)
      rw [hOs_eq_l, Γ.l_inf_m_eq_U, sup_comm Γ.C Γ.U]
      exact le_inf h_τ_le_q h_τ_le_sE
    exact (hCs_atom.le_iff.mp h_τ_le_Cs).resolve_left hτ_atom.1

/-- **Doubling key-identity** `τ_a(C_a) = C_{a+a}` (= `key_identity Γ a a`).

Obtained from `key_identity_core` by feeding it the fresh general-position point
`(d ⊔ Γ.E) ⊓ (a ⊔ Γ.C)` (from `dbl_aux_point`, `d ≠ a` any other good atom) as the
witness `G`, and the diagonal translation identity `coord_add_eq_translation_diag`
as `h_s_transl`.  The auxiliary `d` seeds only the fresh point. -/
theorem dbl_key_identity (Γ : CoordSystem L) (a d : L)
    (ha : IsAtom a) (hd : IsAtom d)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hd_on : d ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hd_ne_O : d ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hd_ne_U : d ≠ Γ.U)
    (had : a ≠ d)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    parallelogram_completion Γ.O a
        (parallelogram_completion Γ.O a Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_add Γ a a) Γ.C (Γ.U ⊔ Γ.V) := by
  obtain ⟨hP_atom, hP_π, hP_not_l, hP_not_m, hP_not_q, hP_le_aC⟩ :=
    dbl_aux_point Γ a d ha hd ha_on hd_on ha_ne_O hd_ne_O ha_ne_U hd_ne_U had
  have hP_ne_a : (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≠ a := fun h => hP_not_l (h.symm ▸ ha_on)
  have hP_ne_C : (d ⊔ Γ.E) ⊓ (a ⊔ Γ.C) ≠ Γ.C :=
    fun h => hP_not_q (le_of_eq h |>.trans le_sup_right)
  exact key_identity_core Γ a a ha ha ha_on ha_on ha_ne_O ha_ne_O ha_ne_U ha_ne_U
    ((d ⊔ Γ.E) ⊓ (a ⊔ Γ.C)) hP_atom hP_le_aC hP_ne_a hP_ne_C hP_not_l hP_not_q hP_not_m
    (coord_add_eq_translation_diag Γ a ha ha_on ha_ne_O ha_ne_U)
    R hR hR_not h_irred

/-- **Generic branch of the doubling wall** (`a + a ≠ Γ.O`, i.e. characteristic ≠ 2).

Composes `dbl_key_identity` (as `h_ki_ab`) with `beta_step_core` (fed the fresh
point from `dbl_aux_point`), taking the fresh-point seed `d := a + a` itself, which
is a good atom distinct from `a` precisely because `a ≠ Γ.O`. -/
theorem dbl_beta_generic (Γ : CoordSystem L) (a c : L)
    (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hs_ne_O : coord_add Γ a a ≠ Γ.O)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    parallelogram_completion Γ.O (coord_add Γ a a)
        (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O a
          (parallelogram_completion Γ.O a
            (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) := by
  have hs_atom : IsAtom (coord_add Γ a a) :=
    coord_add_atom Γ a a ha ha ha_on ha_on ha_ne_O ha_ne_O ha_ne_U ha_ne_U
  have hs_on : coord_add Γ a a ≤ Γ.O ⊔ Γ.U := inf_le_right
  have hs_ne_U : coord_add Γ a a ≠ Γ.U :=
    coord_add_ne_U' Γ a a ha ha ha_on ha_on ha_ne_O ha_ne_U ha_ne_U
  have has : a ≠ coord_add Γ a a := by
    intro h
    have h2 : coord_add Γ a Γ.O = coord_add Γ a a :=
      (coord_add_right_zero Γ a ha ha_on).trans h
    exact ha_ne_O (coord_add_left_cancel Γ a Γ.O a ha Γ.hO ha ha_on le_sup_left ha_on
      ha_ne_U h2).symm
  have h_ki : parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O a Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_add Γ a a) Γ.C (Γ.U ⊔ Γ.V) :=
    dbl_key_identity Γ a (coord_add Γ a a) ha hs_atom ha_on hs_on ha_ne_O hs_ne_O
      ha_ne_U hs_ne_U has R hR hR_not h_irred
  obtain ⟨hP_atom, hP_π, hP_not_l, hP_not_m, hP_not_q, hP_le_aC⟩ :=
    dbl_aux_point Γ a (coord_add Γ a a) ha hs_atom ha_on hs_on ha_ne_O hs_ne_O
      ha_ne_U hs_ne_U has
  exact beta_step_core Γ a a c ha ha hc ha_on ha_on hc_on ha_ne_O ha_ne_O hc_ne_O
    ha_ne_U ha_ne_U hc_ne_U hs_ne_O hs_ne_U
    ((coord_add Γ a a ⊔ Γ.E) ⊓ (a ⊔ Γ.C)) hP_atom hP_π hP_not_l hP_not_m hP_not_q hP_le_aC
    h_ki R hR hR_not h_irred

/-- **Doubling associativity core, char ≠ 2** (lattice level).
`(a+a)+c = a+(a+c)` for good atoms `a, c` on `l`, given `a + a ≠ Γ.O`.  Composes
three ordinary `key_identity` applications with the C-tower recovery `recover_std`
and the proven doubling β-step `dbl_beta_generic`; the summand-coincidence obstruction
lives entirely inside `dbl_beta_generic`. -/
theorem coord_double_left_generic' (Γ : CoordSystem L) (a c : L)
    (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hac : a ≠ c)
    (hs_ne_O : coord_add Γ a a ≠ Γ.O)
    (hsc : coord_add Γ a a ≠ c)
    (ht_ne_O : coord_add Γ a c ≠ Γ.O)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ (coord_add Γ a a) c = coord_add Γ a (coord_add Γ a c) := by
  set m := Γ.U ⊔ Γ.V with hm
  set s := coord_add Γ a a with hs
  set t := coord_add Γ a c with ht
  set C_c := parallelogram_completion Γ.O c Γ.C m with hCc
  have hs_atom : IsAtom s := coord_add_atom Γ a a ha ha ha_on ha_on ha_ne_O ha_ne_O ha_ne_U ha_ne_U
  have ht_atom : IsAtom t := coord_add_atom Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U
  have hs_on : s ≤ Γ.O ⊔ Γ.U := inf_le_right
  have ht_on : t ≤ Γ.O ⊔ Γ.U := inf_le_right
  have hs_ne_U : s ≠ Γ.U := coord_add_ne_U' Γ a a ha ha ha_on ha_on ha_ne_O ha_ne_U ha_ne_U
  have ht_ne_U : t ≠ Γ.U := coord_add_ne_U' Γ a c ha hc ha_on hc_on hc_ne_O ha_ne_U hc_ne_U
  have hat : a ≠ t := by
    intro h
    have h_eq : coord_add Γ a c = coord_add Γ a Γ.O :=
      h.symm.trans (coord_add_right_zero Γ a ha ha_on).symm
    exact hc_ne_O (coord_add_left_cancel Γ a c Γ.O ha hc Γ.hO ha_on hc_on le_sup_left ha_ne_U h_eq)
  have hSC_atom : IsAtom (coord_add Γ s c) :=
    coord_add_atom Γ s c hs_atom hc hs_on hc_on hs_ne_O hc_ne_O hs_ne_U hc_ne_U
  have hAT_atom : IsAtom (coord_add Γ a t) :=
    coord_add_atom Γ a t ha ht_atom ha_on ht_on ha_ne_O ht_ne_O ha_ne_U ht_ne_U
  rw [← recover_std Γ (coord_add Γ s c) hSC_atom inf_le_right,
      ← recover_std Γ (coord_add Γ a t) hAT_atom inf_le_right]
  suffices hXY : parallelogram_completion Γ.O (coord_add Γ s c) Γ.C m
      = parallelogram_completion Γ.O (coord_add Γ a t) Γ.C m by rw [hXY]
  have ki_sc : parallelogram_completion Γ.O s C_c m
      = parallelogram_completion Γ.O (coord_add Γ s c) Γ.C m :=
    key_identity Γ s c hs_atom hc hs_on hc_on hs_ne_O hc_ne_O hs_ne_U hc_ne_U hsc
      R hR hR_not h_irred
  have ki_ac : parallelogram_completion Γ.O a C_c m
      = parallelogram_completion Γ.O t Γ.C m :=
    key_identity Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U hac
      R hR hR_not h_irred
  have ki_at : parallelogram_completion Γ.O a (parallelogram_completion Γ.O t Γ.C m) m
      = parallelogram_completion Γ.O (coord_add Γ a t) Γ.C m :=
    key_identity Γ a t ha ht_atom ha_on ht_on ha_ne_O ht_ne_O ha_ne_U ht_ne_U hat
      R hR hR_not h_irred
  have hbeta : parallelogram_completion Γ.O s C_c m
      = parallelogram_completion Γ.O a (parallelogram_completion Γ.O a C_c m) m :=
    dbl_beta_generic Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U hs_ne_O
      R hR hR_not h_irred
  calc parallelogram_completion Γ.O (coord_add Γ s c) Γ.C m
      = parallelogram_completion Γ.O s C_c m := ki_sc.symm
    _ = parallelogram_completion Γ.O a (parallelogram_completion Γ.O a C_c m) m := hbeta
    _ = parallelogram_completion Γ.O a (parallelogram_completion Γ.O t Γ.C m) m := by rw [ki_ac]
    _ = parallelogram_completion Γ.O (coord_add Γ a t) Γ.C m := ki_at

/-- **C-tower facts.**  For a good atom `b` on `l` (`≠ O`, `≠ U`), the C-tower
`C_b = pc Γ.O b Γ.C m` is an atom off `l`, off `m`, on `q = Γ.U ⊔ Γ.C`, in `π`. -/
theorem C_tower_facts (Γ : CoordSystem L) (b : L) (hb : IsAtom b)
    (hb_on : b ≤ Γ.O ⊔ Γ.U) (hb_ne_O : b ≠ Γ.O) (hb_ne_U : b ≠ Γ.U) :
    IsAtom (parallelogram_completion Γ.O b Γ.C (Γ.U ⊔ Γ.V))
    ∧ ¬ parallelogram_completion Γ.O b Γ.C (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U
    ∧ ¬ parallelogram_completion Γ.O b Γ.C (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V
    ∧ parallelogram_completion Γ.O b Γ.C (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.C
    ∧ parallelogram_completion Γ.O b Γ.C (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := by
  set l := Γ.O ⊔ Γ.U
  set m := Γ.U ⊔ Γ.V
  set q := Γ.U ⊔ Γ.C
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set C_b := parallelogram_completion Γ.O b Γ.C m with hCb_def
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hb_not_m : ¬ b ≤ m := fun h => hb_ne_U (Γ.atom_on_both_eq_U hb hb_on h)
  have hOb_eq_l : Γ.O ⊔ b = l := by
    have h_lt : Γ.O < Γ.O ⊔ b := lt_of_le_of_ne le_sup_left
      (fun h => hb_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hb.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
      (sup_le le_sup_left hb_on)).resolve_left (ne_of_gt h_lt)
  have hm_cov : m ⋖ π := by
    show Γ.U ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
    have hO_inf_m : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
    rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = Γ.O ⊔ (Γ.U ⊔ Γ.V) from sup_assoc _ _ _]
    exact covBy_sup_of_inf_covBy_left (hO_inf_m ▸ Γ.hO.bot_covBy)
  have hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m := fun x hx hle =>
    line_covers_its_atoms Γ.hU Γ.hV hUV hx hle
  have hlq_eq_U : l ⊓ q = Γ.U := by
    show (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U
    rw [sup_comm Γ.O Γ.U]
    have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm hUC hOC
      (fun h => Γ.hC_not_l (le_trans h (by rw [sup_comm])))
  have hCb_atom : IsAtom C_b :=
    parallelogram_completion_atom Γ.hO hb Γ.hC
      (fun h => hb_ne_O h.symm)
      hOC (fun h => Γ.hC_not_l (h ▸ hb_on))
      (le_sup_left.trans le_sup_left) (hb_on.trans le_sup_left) Γ.hC_plane
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hm_cov hm_line
      Γ.hO_not_m hb_not_m Γ.hC_not_m
      (fun h => Γ.hC_not_l (h.trans (hOb_eq_l ▸ le_refl l)))
  have hCb_le_bE : C_b ≤ b ⊔ Γ.E := (inf_le_right : C_b ≤ b ⊔ (Γ.O ⊔ Γ.C) ⊓ m)
  have hCb_le_q : C_b ≤ q := by
    have : C_b ≤ Γ.C ⊔ (Γ.O ⊔ b) ⊓ m := inf_le_left
    rw [hOb_eq_l, Γ.l_inf_m_eq_U] at this
    exact this.trans (sup_comm Γ.C Γ.U ▸ le_refl q)
  have hb_ne_Cb : b ≠ C_b := by
    intro h
    have hb_le_q : b ≤ q := h ▸ hCb_le_q
    have hb_le_lq : b ≤ l ⊓ q := le_inf hb_on hb_le_q
    rw [hlq_eq_U] at hb_le_lq
    exact hb_ne_U ((Γ.hU.le_iff.mp hb_le_lq).resolve_left hb.1)
  have hCb_not_m : ¬ C_b ≤ m := by
    intro hCb_m
    have h_bE_dir : (b ⊔ Γ.E) ⊓ m = Γ.E := line_direction hb hb_not_m Γ.hE_on_m
    have hCb_le_E : C_b ≤ Γ.E := by
      have : C_b ≤ (b ⊔ Γ.E) ⊓ m := le_inf hCb_le_bE hCb_m
      rwa [h_bE_dir] at this
    have hCb_eq_E : C_b = Γ.E := (Γ.hE_atom.le_iff.mp hCb_le_E).resolve_left hCb_atom.1
    have hE_le_qm : Γ.E ≤ q ⊓ m := le_inf (hCb_eq_E ▸ hCb_le_q) Γ.hE_on_m
    have hqm_eq : q ⊓ m = Γ.U := by
      show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
      rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
      have hC_inf_m : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
        (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
      rw [hC_inf_m, sup_bot_eq]
    rw [hqm_eq] at hE_le_qm
    exact Γ.hEU ((Γ.hU.le_iff.mp hE_le_qm).resolve_left Γ.hE_atom.1)
  have hCb_not_l : ¬ C_b ≤ l := by
    intro h
    exact hCb_not_m ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf h hCb_le_q)).resolve_left
      hCb_atom.1 ▸ (le_sup_left : Γ.U ≤ m))
  have hCb_le_π : C_b ≤ π :=
    hCb_le_q.trans (sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane)
  exact ⟨hCb_atom, hCb_not_l, hCb_not_m, hCb_le_q, hCb_le_π⟩

/-- **Grounding (left).**  `T[O,a] C_n = Γ.C`, i.e. `pc Γ.O a C_n m = Γ.C`, where
`n = coord_neg Γ a` and `C_n = pc Γ.O n Γ.C m`.  From `key_identity(a,n)`,
`coord_add_left_neg` (`a + n = O`), and `C_O_eq_C`. -/
theorem grounding_left (Γ : CoordSystem L) (a : L)
    (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (han : a ≠ coord_neg Γ a)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) = Γ.C := by
  have hn_atom := coord_neg_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hn_on := coord_neg_on_l Γ a
  have hn_ne_O := coord_neg_ne_O Γ ha ha_on ha_ne_O ha_ne_U
  have hn_ne_U := coord_neg_ne_U Γ ha ha_on ha_ne_O ha_ne_U
  have hki := key_identity Γ a (coord_neg Γ a) ha hn_atom ha_on hn_on ha_ne_O hn_ne_O
    ha_ne_U hn_ne_U han R hR hR_not h_irred
  have h_an : coord_add Γ a (coord_neg Γ a) = Γ.O :=
    coord_add_left_neg Γ a ha ha_on ha_ne_O ha_ne_U R hR hR_not h_irred
  rw [hki, h_an, C_O_eq_C Γ]

/-- **Grounding (right).**  `T[n,O] C_n = Γ.C`, i.e. `pc n Γ.O C_n m = Γ.C`, where
`n = coord_neg Γ a` and `C_n = pc Γ.O n Γ.C m`.  This is `reverse_completion` with
`P = Γ.O, P' = n, Q = Γ.C` (since `C_n = pc Γ.O n Γ.C m`). -/
theorem grounding_right (Γ : CoordSystem L) (a : L)
    (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U) :
    parallelogram_completion (coord_neg Γ a) Γ.O
      (parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) = Γ.C := by
  have hn_atom := coord_neg_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hn_on := coord_neg_on_l Γ a
  have hn_ne_O := coord_neg_ne_O Γ ha ha_on ha_ne_O ha_ne_U
  have hn_ne_U := coord_neg_ne_U Γ ha ha_on ha_ne_O ha_ne_U
  set m := Γ.U ⊔ Γ.V
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hm_cov : m ⋖ π := by
    show Γ.U ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
    have hO_inf_m : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
    rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = Γ.O ⊔ (Γ.U ⊔ Γ.V) from sup_assoc _ _ _]
    exact covBy_sup_of_inf_covBy_left (hO_inf_m ▸ Γ.hO.bot_covBy)
  have hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m := fun x hx hle =>
    line_covers_its_atoms Γ.hU Γ.hV hUV hx hle
  have hn_not_m : ¬ coord_neg Γ a ≤ m := fun h => hn_ne_U (Γ.atom_on_both_eq_U hn_atom hn_on h)
  have hO_ne_n : Γ.O ≠ coord_neg Γ a := fun h => hn_ne_O h.symm
  have hO_ne_C : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hn_ne_C : coord_neg Γ a ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hn_on)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  exact reverse_completion Γ.hO hn_atom Γ.hC hO_ne_n hO_ne_C hn_ne_C
    (le_sup_left.trans le_sup_left) (hn_on.trans le_sup_left) Γ.hC_plane
    hm_le_π hm_cov hm_line Γ.hO_not_m hn_not_m Γ.hC_not_m
    (fun h => Γ.hC_not_l (h.trans (sup_le le_sup_left hn_on)))

omit [ComplementedLattice L] [IsAtomistic L] in
/-- Non-collinearity is symmetric in the two non-base points. -/
theorem noncol_symm {P X Y : L} (hP : IsAtom P) (hX : IsAtom X) (hY : IsAtom Y)
    (hPX : P ≠ X) (hPY : P ≠ Y) (h : ¬ Y ≤ P ⊔ X) : ¬ X ≤ P ⊔ Y := by
  intro hX_le
  have hPX_le : P ⊔ X ≤ P ⊔ Y := sup_le le_sup_left hX_le
  have hcovX : P ⋖ P ⊔ X := atom_covBy_join hP hX hPX
  have hcovY : P ⋖ P ⊔ Y := atom_covBy_join hP hY hPY
  have heq : P ⊔ X = P ⊔ Y := (hcovY.eq_or_eq hcovX.lt.le hPX_le).resolve_left (ne_of_gt hcovX.lt)
  exact h (heq ▸ le_sup_right)

/-- **The base-change involution** (`hinv` / RESIDUAL 4 of `coord_inv_absorb`).

`T[O,a] (T[O,n] C_c) = C_c`, where `n = coord_neg Γ a`, `C_c = pc Γ.O c Γ.C m`.
Executes the documented four-`well_defined` route through a general-position witness
`R₀` (whose non-degeneracy is supplied as hypotheses; the geometric core — the four
`parallelogram_completion_well_defined` discharges — is proved here). -/
theorem base_change_hinv (Γ : CoordSystem L) (a c : L)
    (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (han : a ≠ coord_neg Γ a)
    (R₀ : L) (hR0 : IsAtom R₀) (hR0_π : R₀ ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hR0_l : ¬ R₀ ≤ Γ.O ⊔ Γ.U) (hR0_m : ¬ R₀ ≤ Γ.U ⊔ Γ.V)
    (hR0_ℓ₁ : ¬ R₀ ≤ parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V) ⊔ Γ.C)
    (hR0_OCn : ¬ R₀ ≤ Γ.O ⊔ parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V))
    (hR0_nCn : ¬ R₀ ≤ coord_neg Γ a ⊔ parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V))
    (span_A : Γ.O ⊔ parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V) ⊔ R₀
      = Γ.O ⊔ Γ.U ⊔ Γ.V)
    (span_B : coord_neg Γ a ⊔ parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V) ⊔ R₀
      = Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hCt_l : ¬ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U)
    (hCt_m : ¬ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V)
    (hCt_π : parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hR0_OCt : ¬ R₀ ≤ Γ.O ⊔ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V))
    (hR0_nCt : ¬ R₀ ≤ coord_neg Γ a ⊔ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V))
    (hCt_ℓ₂ : ¬ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      ≤ R₀ ⊔ parallelogram_completion Γ.O a R₀ (Γ.U ⊔ Γ.V))
    (span_C : Γ.O ⊔ R₀ ⊔ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) = Γ.O ⊔ Γ.U ⊔ Γ.V)
    (span_D : coord_neg Γ a ⊔ R₀ ⊔ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) = Γ.O ⊔ Γ.U ⊔ Γ.V)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O (coord_neg Γ a)
        (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V) := by
  set m := Γ.U ⊔ Γ.V with hm
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ
  set n := coord_neg Γ a with hn
  have hn_atom : IsAtom n := coord_neg_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hn_on : n ≤ Γ.O ⊔ Γ.U := coord_neg_on_l Γ a
  have hn_ne_O : n ≠ Γ.O := coord_neg_ne_O Γ ha ha_on ha_ne_O ha_ne_U
  have hn_ne_U : n ≠ Γ.U := coord_neg_ne_U Γ ha ha_on ha_ne_O ha_ne_U
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hm_cov : m ⋖ π := by
    show Γ.U ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
    have hO_inf_m : Γ.O ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hO.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hO_not_m (h ▸ inf_le_right))
    rw [show Γ.O ⊔ Γ.U ⊔ Γ.V = Γ.O ⊔ (Γ.U ⊔ Γ.V) from sup_assoc _ _ _]
    exact covBy_sup_of_inf_covBy_left (hO_inf_m ▸ Γ.hO.bot_covBy)
  have hm_line : ∀ x, IsAtom x → x ≤ m → x ⋖ m := fun x hx hle =>
    line_covers_its_atoms Γ.hU Γ.hV hUV hx hle
  have ha_not_m : ¬ a ≤ m := fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have hn_not_m : ¬ n ≤ m := fun h => hn_ne_U (Γ.atom_on_both_eq_U hn_atom hn_on h)
  have hO_le_π : Γ.O ≤ π := le_sup_left.trans le_sup_left
  have ha_le_π : a ≤ π := ha_on.trans le_sup_left
  have hn_le_π : n ≤ π := hn_on.trans le_sup_left
  obtain ⟨hCc_atom, hCc_not_l, hCc_not_m, _, hCc_π⟩ := C_tower_facts Γ c hc hc_on hc_ne_O hc_ne_U
  obtain ⟨hCn_atom, hCn_not_l, hCn_not_m, _, hCn_π⟩ :=
    C_tower_facts Γ n hn_atom hn_on hn_ne_O hn_ne_U
  set C_c := parallelogram_completion Γ.O c Γ.C m with hCc_def
  set C_n := parallelogram_completion Γ.O n Γ.C m with hCn_def
  set C_t := parallelogram_completion Γ.O n C_c m with hCt_def
  set R₀' := parallelogram_completion Γ.O a R₀ m with hR0'_def
  have hgl : parallelogram_completion Γ.O a C_n m = Γ.C :=
    grounding_left Γ a ha ha_on ha_ne_O ha_ne_U han R hR hR_not h_irred
  have hgr : parallelogram_completion n Γ.O C_n m = Γ.C :=
    grounding_right Γ a ha ha_on ha_ne_O ha_ne_U
  have hOn_ne : Γ.O ≠ n := fun h => hn_ne_O h.symm
  have hn_ne_Cc : n ≠ C_c := fun h => hCc_not_l (h ▸ hn_on)
  have hCt_atom : IsAtom C_t :=
    parallelogram_completion_atom Γ.hO hn_atom hCc_atom hOn_ne
      (fun h => hCc_not_l (h ▸ le_sup_left)) hn_ne_Cc
      hO_le_π hn_le_π hCc_π hm_le_π hm_cov hm_line Γ.hO_not_m hn_not_m hCc_not_m
      (fun h => hCc_not_l (h.trans (by
        have hOn : Γ.O ⊔ n = Γ.O ⊔ Γ.U := by
          have h_lt : Γ.O < Γ.O ⊔ n := lt_of_le_of_ne le_sup_left
            (fun hh => hn_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left hn_atom.1))
          exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
            (sup_le le_sup_left hn_on)).resolve_left (ne_of_gt h_lt)
        exact hOn.le)))
  have hR0_ne_O : Γ.O ≠ R₀ := fun h => hR0_l (h ▸ le_sup_left)
  have ha_ne_R0 : a ≠ R₀ := fun h => hR0_l (h ▸ ha_on)
  have hR0'_atom : IsAtom R₀' :=
    parallelogram_completion_atom Γ.hO ha hR0 (fun h => ha_ne_O h.symm)
      hR0_ne_O ha_ne_R0 hO_le_π ha_le_π hR0_π hm_le_π hm_cov hm_line
      Γ.hO_not_m ha_not_m hR0_m
      (by
        have hOa : Γ.O ⊔ a = Γ.O ⊔ Γ.U := by
          have h_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
            (fun hh => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
              ha.1))
          exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
            (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt h_lt)
        rw [hOa]; exact hR0_l)
  have hO_ne_a : Γ.O ≠ a := fun h => ha_ne_O h.symm
  have hO_ne_Cn : Γ.O ≠ C_n := fun h => hCn_not_l (h ▸ le_sup_left)
  have hO_ne_Ct : Γ.O ≠ C_t := fun h => hCt_l (h ▸ le_sup_left)
  have ha_ne_Cn : a ≠ C_n := fun h => hCn_not_l (h ▸ ha_on)
  have ha_ne_Ct : a ≠ C_t := fun h => hCt_l (h ▸ ha_on)
  have hn_ne_Cn : n ≠ C_n := fun h => hCn_not_l (h ▸ hn_on)
  have hn_ne_R0 : n ≠ R₀ := fun h => hR0_l (h ▸ hn_on)
  have hn_ne_Ct : n ≠ C_t := fun h => hCt_l (h ▸ hn_on)
  have hO_ne_R0 : Γ.O ≠ R₀ := hR0_ne_O
  have hCn_ne_R0 : C_n ≠ R₀ := fun h => hR0_ℓ₁ (h ▸ le_sup_left)
  have hR0_ne_Ct : R₀ ≠ C_t := fun h => hCt_ℓ₂ (h ▸ le_sup_left)
  have hCn_OR0 : ¬ C_n ≤ Γ.O ⊔ R₀ := noncol_symm Γ.hO hCn_atom hR0 hO_ne_Cn hO_ne_R0 hR0_OCn
  have hCn_nR0 : ¬ C_n ≤ n ⊔ R₀ := noncol_symm hn_atom hCn_atom hR0 hn_ne_Cn hn_ne_R0 hR0_nCn
  have hR0_OCt' : ¬ C_t ≤ Γ.O ⊔ R₀ := noncol_symm Γ.hO hCt_atom hR0 hO_ne_Ct hO_ne_R0 hR0_OCt
  have hR0_nCt' : ¬ C_t ≤ n ⊔ R₀ := noncol_symm hn_atom hCt_atom hR0 hn_ne_Ct hn_ne_R0 hR0_nCt
  have hA : parallelogram_completion Γ.O a R₀ m = parallelogram_completion C_n Γ.C R₀ m := by
    have := parallelogram_completion_well_defined
      (P := Γ.O) (P' := a) (Q := C_n) (R := R₀) (m := m) (π := π)
      Γ.hO ha hCn_atom hR0
      hO_ne_a hO_ne_Cn hO_ne_R0 ha_ne_Cn ha_ne_R0 hCn_ne_R0
      hO_le_π ha_le_π hCn_π hR0_π hm_le_π hm_cov hm_line
      Γ.hO_not_m ha_not_m hCn_not_m hR0_m
      (fun h => hCn_not_l ((show Γ.O ⊔ a = Γ.O ⊔ Γ.U from by
        have h_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
          (fun hh => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left ha.1))
        exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
          (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt h_lt)) ▸ h))
      (fun h => hR0_l ((show Γ.O ⊔ a = Γ.O ⊔ Γ.U from by
        have h_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
          (fun hh => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left ha.1))
        exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
          (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt h_lt)) ▸ h))
      hR0_OCn hCn_OR0
      (by rw [hgl]; exact hR0_ℓ₁)
      span_A R hR hR_not h_irred
    rw [this, hgl]
  have hB : parallelogram_completion n Γ.O R₀ m = parallelogram_completion C_n Γ.C R₀ m := by
    have hnO : n ⊔ Γ.O = Γ.O ⊔ Γ.U := by
      rw [sup_comm]
      have h_lt : Γ.O < Γ.O ⊔ n := lt_of_le_of_ne le_sup_left
        (fun hh => hn_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left hn_atom.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hn_on)).resolve_left (ne_of_gt h_lt)
    have := parallelogram_completion_well_defined
      (P := n) (P' := Γ.O) (Q := C_n) (R := R₀) (m := m) (π := π)
      hn_atom Γ.hO hCn_atom hR0
      hOn_ne.symm hn_ne_Cn hn_ne_R0 hO_ne_Cn hO_ne_R0 hCn_ne_R0
      hn_le_π hO_le_π hCn_π hR0_π hm_le_π hm_cov hm_line
      hn_not_m Γ.hO_not_m hCn_not_m hR0_m
      (fun h => hCn_not_l (hnO ▸ h)) (fun h => hR0_l (hnO ▸ h))
      hR0_nCn hCn_nR0
      (by rw [hgr]; exact hR0_ℓ₁)
      span_B R hR hR_not h_irred
    rw [this, hgr]
  have hR0'_agree : parallelogram_completion n Γ.O R₀ m = R₀' := by rw [hB, ← hA]
  have hOa_l : Γ.O ⊔ a = Γ.O ⊔ Γ.U := by
    have h_lt : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
      (fun hh => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left ha.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
      (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt h_lt)
  have hnO_l : n ⊔ Γ.O = Γ.O ⊔ Γ.U := by
    rw [sup_comm]
    have h_lt : Γ.O < Γ.O ⊔ n := lt_of_le_of_ne le_sup_left
      (fun hh => hn_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left hn_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
      (sup_le le_sup_left hn_on)).resolve_left (ne_of_gt h_lt)
  have hC : parallelogram_completion Γ.O a C_t m = parallelogram_completion R₀ R₀' C_t m := by
    have := parallelogram_completion_well_defined
      (P := Γ.O) (P' := a) (Q := R₀) (R := C_t) (m := m) (π := π)
      Γ.hO ha hR0 hCt_atom
      hO_ne_a hO_ne_R0 hO_ne_Ct ha_ne_R0 ha_ne_Ct hR0_ne_Ct
      hO_le_π ha_le_π hR0_π hCt_π hm_le_π hm_cov hm_line
      Γ.hO_not_m ha_not_m hR0_m hCt_m
      (fun h => hR0_l (hOa_l ▸ h)) (fun h => hCt_l (hOa_l ▸ h))
      hR0_OCt' hR0_OCt hCt_ℓ₂
      span_C R hR hR_not h_irred
    rw [this]
  have hD : parallelogram_completion n Γ.O C_t m = parallelogram_completion R₀ R₀' C_t m := by
    have := parallelogram_completion_well_defined
      (P := n) (P' := Γ.O) (Q := R₀) (R := C_t) (m := m) (π := π)
      hn_atom Γ.hO hR0 hCt_atom
      hOn_ne.symm hn_ne_R0 hn_ne_Ct hO_ne_R0 hO_ne_Ct hR0_ne_Ct
      hn_le_π hO_le_π hR0_π hCt_π hm_le_π hm_cov hm_line
      hn_not_m Γ.hO_not_m hR0_m hCt_m
      (fun h => hR0_l (hnO_l ▸ h)) (fun h => hCt_l (hnO_l ▸ h))
      hR0_nCt' hR0_nCt
      (by rw [hR0'_agree]; exact hCt_ℓ₂)
      span_D R hR hR_not h_irred
    rw [this, hR0'_agree]
  have hstar : parallelogram_completion Γ.O a C_t m = parallelogram_completion n Γ.O C_t m := by
    rw [hC, hD]
  have hrev : parallelogram_completion n Γ.O C_t m = C_c := by
    have hOc_l : Γ.O ⊔ c = Γ.O ⊔ Γ.U := by
      have h_lt : Γ.O < Γ.O ⊔ c := lt_of_le_of_ne le_sup_left
        (fun hh => hc_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left hc.1))
      exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
        (sup_le le_sup_left hc_on)).resolve_left (ne_of_gt h_lt)
    have hCc_ne_O : Γ.O ≠ C_c := fun h => hCc_not_l (h ▸ le_sup_left)
    have hn_ne_Cc' : n ≠ C_c := hn_ne_Cc
    exact reverse_completion Γ.hO hn_atom hCc_atom hOn_ne hCc_ne_O hn_ne_Cc'
      hO_le_π hn_le_π hCc_π hm_le_π hm_cov hm_line Γ.hO_not_m hn_not_m hCc_not_m
      (fun h => hCc_not_l (h.trans (sup_le le_sup_left hn_on)))
  rw [hstar, hrev]

/-- **Inverse absorption — geometric core (generic branch).**
`coord_add Γ a (coord_add Γ (coord_neg Γ a) c) = c`, given the general-position witness
`R₀`.  Mirrors the reduction inside `coord_inv_absorb`: `recover_std` + two `key_identity`
applications reduce the goal to the involution `base_change_hinv`. -/
theorem inv_absorb_core (Γ : CoordSystem L) (a c : L)
    (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hca : c ≠ a) (han : a ≠ coord_neg Γ a) (hcn : c ≠ coord_neg Γ a)
    (hat : a ≠ coord_add Γ (coord_neg Γ a) c)
    (R₀ : L) (hR0 : IsAtom R₀) (hR0_π : R₀ ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hR0_l : ¬ R₀ ≤ Γ.O ⊔ Γ.U) (hR0_m : ¬ R₀ ≤ Γ.U ⊔ Γ.V)
    (hR0_ℓ₁ : ¬ R₀ ≤ parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V) ⊔ Γ.C)
    (hR0_OCn : ¬ R₀ ≤ Γ.O ⊔ parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V))
    (hR0_nCn : ¬ R₀ ≤ coord_neg Γ a ⊔ parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V))
    (span_A : Γ.O ⊔ parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V) ⊔ R₀
      = Γ.O ⊔ Γ.U ⊔ Γ.V)
    (span_B : coord_neg Γ a ⊔ parallelogram_completion Γ.O (coord_neg Γ a) Γ.C (Γ.U ⊔ Γ.V) ⊔ R₀
      = Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hCt_l : ¬ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U)
    (hCt_m : ¬ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V)
    (hCt_π : parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hR0_OCt : ¬ R₀ ≤ Γ.O ⊔ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V))
    (hR0_nCt : ¬ R₀ ≤ coord_neg Γ a ⊔ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V))
    (hCt_ℓ₂ : ¬ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      ≤ R₀ ⊔ parallelogram_completion Γ.O a R₀ (Γ.U ⊔ Γ.V))
    (span_C : Γ.O ⊔ R₀ ⊔ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) = Γ.O ⊔ Γ.U ⊔ Γ.V)
    (span_D : coord_neg Γ a ⊔ R₀ ⊔ parallelogram_completion Γ.O (coord_neg Γ a)
      (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) = Γ.O ⊔ Γ.U ⊔ Γ.V)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ a (coord_add Γ (coord_neg Γ a) c) = c := by
  have hn_atom : IsAtom (coord_neg Γ a) := coord_neg_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hn_on : coord_neg Γ a ≤ Γ.O ⊔ Γ.U := coord_neg_on_l Γ a
  have hn_ne_O : coord_neg Γ a ≠ Γ.O := coord_neg_ne_O Γ ha ha_on ha_ne_O ha_ne_U
  have hn_ne_U : coord_neg Γ a ≠ Γ.U := coord_neg_ne_U Γ ha ha_on ha_ne_O ha_ne_U
  set t := coord_add Γ (coord_neg Γ a) c with ht_def
  have ht_atom : IsAtom t :=
    coord_add_atom Γ (coord_neg Γ a) c hn_atom hc hn_on hc_on hn_ne_O hc_ne_O hn_ne_U hc_ne_U
  have ht_on : t ≤ Γ.O ⊔ Γ.U := inf_le_right
  have ht_ne_U : t ≠ Γ.U :=
    coord_add_ne_U' Γ (coord_neg Γ a) c hn_atom hc hn_on hc_on hc_ne_O hn_ne_U hc_ne_U
  have ht_ne_O : t ≠ Γ.O := by
    intro h
    have h_na : coord_add Γ (coord_neg Γ a) a = Γ.O := by
      rw [coord_add_comm Γ (coord_neg Γ a) a hn_atom ha hn_on ha_on hn_ne_O ha_ne_O
        hn_ne_U ha_ne_U (Ne.symm han) R hR hR_not h_irred]
      exact coord_add_left_neg Γ a ha ha_on ha_ne_O ha_ne_U R hR hR_not h_irred
    have hh : coord_add Γ (coord_neg Γ a) c = coord_add Γ (coord_neg Γ a) a := h.trans h_na.symm
    exact hca (coord_add_left_cancel Γ (coord_neg Γ a) c a hn_atom hc ha hn_on hc_on ha_on
      hn_ne_U hh)
  have hki_nc := key_identity Γ (coord_neg Γ a) c hn_atom hc hn_on hc_on hn_ne_O hc_ne_O
    hn_ne_U hc_ne_U (Ne.symm hcn) R hR hR_not h_irred
  have hki_at := key_identity Γ a t ha ht_atom ha_on ht_on ha_ne_O ht_ne_O ha_ne_U ht_ne_U
    hat R hR hR_not h_irred
  have hLHS_atom : IsAtom (coord_add Γ a t) :=
    coord_add_atom Γ a t ha ht_atom ha_on ht_on ha_ne_O ht_ne_O ha_ne_U ht_ne_U
  show coord_add Γ a t = c
  rw [← recover_std Γ (coord_add Γ a t) hLHS_atom inf_le_right,
      ← recover_std Γ c hc hc_on]
  have hstep : parallelogram_completion Γ.O (coord_add Γ a t) Γ.C (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O a
          (parallelogram_completion Γ.O (coord_neg Γ a)
            (parallelogram_completion Γ.O c Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) := by
    rw [← hki_at]; congr 1; exact hki_nc.symm
  have hinv := base_change_hinv Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U han
    R₀ hR0 hR0_π hR0_l hR0_m hR0_ℓ₁ hR0_OCn hR0_nCn span_A span_B
    hCt_l hCt_m hCt_π hR0_OCt hR0_nCt hCt_ℓ₂ span_C span_D R hR hR_not h_irred
  rw [hstep, hinv]

/-- The auxiliary line `q = Γ.U ⊔ Γ.C` is covered by the plane. -/
theorem q_covBy_π (Γ : CoordSystem L) :
    (Γ.U ⊔ Γ.C) ⋖ (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hqm_eq_U : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have hC_inf_m : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [hC_inf_m, sup_bot_eq]
  have hV_not_q : ¬ Γ.V ≤ Γ.U ⊔ Γ.C := fun hle =>
    hUV ((Γ.hU.le_iff.mp (hqm_eq_U ▸ le_inf hle le_sup_right)).resolve_left Γ.hV.1).symm
  have hV_disj_q : Γ.V ⊓ (Γ.U ⊔ Γ.C) = ⊥ :=
    (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => hV_not_q (h ▸ inf_le_right))
  have hVq_eq_π : Γ.V ⊔ (Γ.U ⊔ Γ.C) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h1 : Γ.V ⊔ (Γ.U ⊔ Γ.C) = (Γ.U ⊔ Γ.V) ⊔ Γ.C := by ac_rfl
    rw [h1, Γ.m_sup_C_eq_π]
  exact hVq_eq_π ▸ covBy_sup_of_inf_covBy_left (hV_disj_q ▸ Γ.hV.bot_covBy)

/-- **A noncollinear triangle spans the plane.**  For atoms `P, Q, R` of `π` with
`R` off the line `P ⊔ Q` and `P` off `m`, the join is all of `π`. -/
theorem span_plane (Γ : CoordSystem L) {P Q R : L}
    (hP : IsAtom P) (hQ : IsAtom Q) (hR : IsAtom R) (hPQ : P ≠ Q)
    (hP_le : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hQ_le : Q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hR_le : R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hR_not : ¬ R ≤ P ⊔ Q) :
    P ⊔ Q ⊔ R = Γ.O ⊔ Γ.U ⊔ Γ.V := by
  set m := Γ.U ⊔ Γ.V with hm
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hm_line : ∀ y, IsAtom y → y ≤ m → y ⋖ m := fun y hy hle =>
    line_covers_its_atoms Γ.hU Γ.hV hUV hy hle
  have hPR : P ≠ R := fun h => hR_not (h ▸ le_sup_left)
  set F := (P ⊔ Q) ⊓ m with hF_def
  set G := (P ⊔ R) ⊓ m with hG_def
  have hF_atom : IsAtom F :=
    line_meets_m_at_atom hP hQ hPQ (sup_le hP_le hQ_le) hm_le_π Γ.m_covBy_π hP_not_m
  have hG_atom : IsAtom G :=
    line_meets_m_at_atom hP hR hPR (sup_le hP_le hR_le) hm_le_π Γ.m_covBy_π hP_not_m
  have hP_ne_F : P ≠ F := fun h => hP_not_m (h.le.trans inf_le_right)
  have hFG : F ≠ G := by
    intro h_eq
    have hPF_lt : P < P ⊔ F := lt_of_le_of_ne le_sup_left
      (fun h => hP_ne_F ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hF_atom.1).symm)
    have hPF_eq_PQ : P ⊔ F = P ⊔ Q :=
      ((atom_covBy_join hP hQ hPQ).eq_or_eq hPF_lt.le
        (sup_le le_sup_left inf_le_left)).resolve_left (ne_of_gt hPF_lt)
    have hPF_eq_PR : P ⊔ F = P ⊔ R :=
      ((atom_covBy_join hP hR hPR).eq_or_eq hPF_lt.le
        (sup_le le_sup_left (h_eq ▸ (inf_le_left : G ≤ P ⊔ R)))).resolve_left
        (ne_of_gt hPF_lt)
    exact hR_not (hPF_eq_PQ ▸ hPF_eq_PR ▸ le_sup_right)
  have hFG_eq_m : F ⊔ G = m := by
    have h_lt : F < F ⊔ G := lt_of_le_of_ne le_sup_left
      (fun h => hFG ((hF_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hG_atom.1).symm)
    exact ((hm_line F hF_atom inf_le_right).eq_or_eq h_lt.le
      (sup_le inf_le_right inf_le_right)).resolve_left (ne_of_gt h_lt)
  have hm_le : m ≤ P ⊔ Q ⊔ R := by
    rw [← hFG_eq_m]
    exact sup_le (inf_le_left.trans le_sup_left)
      ((inf_le_left : G ≤ P ⊔ R).trans
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  have hmP_eq_π : m ⊔ P = π := by
    have h_lt : m < m ⊔ P := lt_of_le_of_ne le_sup_left
      (fun h => hP_not_m (le_sup_right.trans h.symm.le))
    exact (Γ.m_covBy_π.eq_or_eq h_lt.le (sup_le hm_le_π hP_le)).resolve_left
      (ne_of_gt h_lt)
  refine le_antisymm (sup_le (sup_le hP_le hQ_le) hR_le) ?_
  rw [← hmP_eq_π]
  exact sup_le hm_le (le_sup_left.trans le_sup_left)

/-- **The reverse tower is the negative's tower.**  `pc x Γ.O Γ.C m = C_{-x}`:
translating `Γ.C` by the vector `x → O` lands on the C-tower of `coord_neg Γ x`.
Extracted from `coord_add_left_neg` (`x + (-x) = O`): the sum's defining meet
passes through `Γ.O` exactly when the line `Γ.O ⊔ C_{-x}` carries the direction
`(x ⊔ Γ.C) ⊓ m`, which is the second component of the reverse completion. -/
theorem neg_tower_reverse (Γ : CoordSystem L) (x : L)
    (hx : IsAtom x) (hx_on : x ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hx_ne_U : x ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    parallelogram_completion x Γ.O Γ.C (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_neg Γ x) Γ.C (Γ.U ⊔ Γ.V) := by
  set l := Γ.O ⊔ Γ.U with hl
  set m := Γ.U ⊔ Γ.V with hm
  set q := Γ.U ⊔ Γ.C with hq
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ
  set n := coord_neg Γ x with hn
  set C_n := parallelogram_completion Γ.O n Γ.C m with hCn_def
  have hn_atom : IsAtom n := coord_neg_atom Γ hx hx_on hx_ne_O hx_ne_U
  have hn_on : n ≤ l := coord_neg_on_l Γ x
  have hn_ne_U : n ≠ Γ.U := coord_neg_ne_U Γ hx hx_on hx_ne_O hx_ne_U
  obtain ⟨hCn_atom, hCn_not_l, hCn_not_m, hCn_le_q, -⟩ :=
    C_tower_facts Γ n hn_atom hn_on (coord_neg_ne_O Γ hx hx_on hx_ne_O hx_ne_U) hn_ne_U
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hx_ne_C : x ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hx_on)
  have hx_not_m : ¬ x ≤ m := fun h => hx_ne_U (Γ.atom_on_both_eq_U hx hx_on h)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  set h' := (x ⊔ Γ.C) ⊓ m with hh'_def
  have hh'_atom : IsAtom h' :=
    line_meets_m_at_atom hx Γ.hC hx_ne_C (sup_le (hx_on.trans le_sup_left) Γ.hC_plane)
      hm_le_π Γ.m_covBy_π hx_not_m
  have hCn_le_nE : C_n ≤ n ⊔ Γ.E := (inf_le_right : C_n ≤ n ⊔ (Γ.O ⊔ Γ.C) ⊓ m)
  have hCn_cov_q : C_n ⋖ q := line_covers_its_atoms Γ.hU Γ.hC hUC hCn_atom hCn_le_q
  have hDn_eq : (n ⊔ Γ.E) ⊓ q = C_n := by
    have h_ne_q : (n ⊔ Γ.E) ⊓ q ≠ q := by
      intro h_eq
      have hU_le_nE : Γ.U ≤ n ⊔ Γ.E := (le_sup_left.trans h_eq.symm.le).trans inf_le_left
      have h_nE_l : (Γ.E ⊔ n) ⊓ l = n := line_direction Γ.hE_atom Γ.hE_not_l hn_on
      have hU_le_n : Γ.U ≤ n := by
        rw [← h_nE_l]
        exact le_inf (hU_le_nE.trans (sup_comm n Γ.E).le) le_sup_right
      exact hn_ne_U ((hn_atom.le_iff.mp hU_le_n).resolve_left Γ.hU.1).symm
    exact (hCn_cov_q.eq_or_eq (le_inf hCn_le_nE hCn_le_q) inf_le_right).resolve_right
      h_ne_q
  have hadd : ((x ⊔ Γ.C) ⊓ m ⊔ (n ⊔ Γ.E) ⊓ q) ⊓ l = Γ.O :=
    coord_add_left_neg Γ x hx hx_on hx_ne_O hx_ne_U R hR hR_not h_irred
  rw [hDn_eq] at hadd
  have hO_le : Γ.O ≤ h' ⊔ C_n := hadd ▸ inf_le_left
  have hh'_ne_Cn : h' ≠ C_n := fun h => hCn_not_m (h.symm.le.trans inf_le_right)
  have hO_ne_Cn : Γ.O ≠ C_n := fun h => hCn_not_l (h.symm.le.trans le_sup_left)
  have hOCn_eq : C_n ⊔ Γ.O = C_n ⊔ h' := by
    have h_lt : C_n < C_n ⊔ Γ.O := lt_of_le_of_ne le_sup_left
      (fun h => hO_ne_Cn ((hCn_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hO.1))
    exact ((atom_covBy_join hCn_atom hh'_atom hh'_ne_Cn.symm).eq_or_eq h_lt.le
      (sup_le le_sup_left (hO_le.trans (sup_comm h' C_n).le))).resolve_left (ne_of_gt h_lt)
  have hO_cov : Γ.O ⋖ Γ.O ⊔ C_n := atom_covBy_join Γ.hO hCn_atom hO_ne_Cn
  have hOh'_eq : Γ.O ⊔ h' = Γ.O ⊔ C_n := by
    have hO_ne_h' : Γ.O ≠ h' := fun h => Γ.hO_not_m (h.le.trans inf_le_right)
    have h_lt : Γ.O < Γ.O ⊔ h' := lt_of_le_of_ne le_sup_left
      (fun h => hO_ne_h' ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hh'_atom.1).symm)
    have hh'_le : h' ≤ Γ.O ⊔ C_n := by
      have : h' ≤ C_n ⊔ h' := le_sup_right
      rw [← hOCn_eq] at this
      exact this.trans (sup_comm C_n Γ.O).le
    exact (hO_cov.eq_or_eq h_lt.le (sup_le le_sup_left hh'_le)).resolve_left
      (ne_of_gt h_lt)
  have hxO_eq_l : x ⊔ Γ.O = l := by
    have h_lt : Γ.O < Γ.O ⊔ x := lt_of_le_of_ne le_sup_left
      (fun h => hx_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hx.1))
    rw [sup_comm x Γ.O]
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
      (sup_le le_sup_left hx_on)).resolve_left (ne_of_gt h_lt)
  have hlm : l ⊓ m = Γ.U := Γ.l_inf_m_eq_U
  show (Γ.C ⊔ (x ⊔ Γ.O) ⊓ m) ⊓ (Γ.O ⊔ (x ⊔ Γ.C) ⊓ m) = C_n
  rw [hxO_eq_l, hlm, sup_comm Γ.C Γ.U, ← hh'_def, hOh'_eq]
  have h_ne_q : (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ C_n) ≠ Γ.U ⊔ Γ.C := by
    intro h_eq
    have hl_le : l ≤ Γ.O ⊔ C_n := sup_le le_sup_left
      ((le_sup_left.trans h_eq.symm.le).trans inf_le_right)
    have := (hO_cov.eq_or_eq (le_sup_left : Γ.O ≤ l) hl_le).resolve_left
      (fun h => Γ.hOU ((Γ.hO.le_iff.mp (le_sup_right.trans h.le)).resolve_left Γ.hU.1).symm)
    exact hCn_not_l (le_sup_right.trans this.symm.le)
  exact ((hCn_cov_q.eq_or_eq (le_inf hCn_le_q le_sup_right) inf_le_left).resolve_right
    h_ne_q)

/-- **The τ-inverse auxiliary point.**  `z = (x ⊔ Γ.E) ⊓ (w' ⊔ X)`: the meet of the
`Γ.E`-direction line through `x` with the line joining a fresh good point `w'` to the
target `X` on `q`.  In general position with respect to every line the τ-inverse
transport routes through: off `l`, `m`, `q`, `Γ.O ⊔ Γ.C`, `x ⊔ Γ.C`, `Γ.O ⊔ X`,
and `x ⊔ X`. -/
theorem inv_aux_point (Γ : CoordSystem L) (x w' X : L)
    (hx : IsAtom x) (hx_on : x ≤ Γ.O ⊔ Γ.U) (hx_ne_O : x ≠ Γ.O) (hx_ne_U : x ≠ Γ.U)
    (hw' : IsAtom w') (hw'_on : w' ≤ Γ.O ⊔ Γ.U) (hw'_ne_O : w' ≠ Γ.O)
    (hw'_ne_U : w' ≠ Γ.U) (hw'x : w' ≠ x)
    (hX : IsAtom X) (hX_q : X ≤ Γ.U ⊔ Γ.C) (hX_ne_U : X ≠ Γ.U)
    (hX_xE : ¬ X ≤ x ⊔ Γ.E) (hX_w'E : ¬ X ≤ w' ⊔ Γ.E) :
    IsAtom ((x ⊔ Γ.E) ⊓ (w' ⊔ X))
    ∧ (x ⊔ Γ.E) ⊓ (w' ⊔ X) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V
    ∧ ¬ (x ⊔ Γ.E) ⊓ (w' ⊔ X) ≤ Γ.O ⊔ Γ.U
    ∧ ¬ (x ⊔ Γ.E) ⊓ (w' ⊔ X) ≤ Γ.U ⊔ Γ.V
    ∧ ¬ (x ⊔ Γ.E) ⊓ (w' ⊔ X) ≤ Γ.U ⊔ Γ.C
    ∧ ¬ (x ⊔ Γ.E) ⊓ (w' ⊔ X) ≤ Γ.O ⊔ Γ.C
    ∧ ¬ (x ⊔ Γ.E) ⊓ (w' ⊔ X) ≤ x ⊔ Γ.C
    ∧ ¬ (x ⊔ Γ.E) ⊓ (w' ⊔ X) ≤ Γ.O ⊔ X
    ∧ ¬ (x ⊔ Γ.E) ⊓ (w' ⊔ X) ≤ x ⊔ X := by
  set l := Γ.O ⊔ Γ.U with hl
  set m := Γ.U ⊔ Γ.V with hm
  set q := Γ.U ⊔ Γ.C with hq
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ
  set z := (x ⊔ Γ.E) ⊓ (w' ⊔ X) with hz_def
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hx_ne_E : x ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hx_on)
  have hx_ne_C : x ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hx_on)
  have hx_not_m : ¬ x ≤ m := fun h => hx_ne_U (Γ.atom_on_both_eq_U hx hx_on h)
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
  have hX_not_l : ¬ X ≤ l := fun h =>
    hX_ne_U ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf h hX_q)).resolve_left hX.1)
  have hX_not_m : ¬ X ≤ m := fun h =>
    hX_ne_U ((Γ.hU.le_iff.mp (hqm_eq_U ▸ le_inf hX_q h)).resolve_left hX.1)
  have hw'X_ne : w' ≠ X := fun h => hX_not_l (h ▸ hw'_on)
  have hxE_le_π : x ⊔ Γ.E ≤ π := sup_le (hx_on.trans le_sup_left) (Γ.hE_on_m.trans hm_le_π)
  have hw'X_le_π : w' ⊔ X ≤ π :=
    sup_le (hw'_on.trans le_sup_left) (hX_q.trans (sup_le (le_sup_right.trans le_sup_left)
      Γ.hC_plane))
  have hxE_l : (x ⊔ Γ.E) ⊓ l = x := by
    rw [sup_comm]; exact line_direction Γ.hE_atom Γ.hE_not_l hx_on
  have hxE_m : (x ⊔ Γ.E) ⊓ m = Γ.E := line_direction hx hx_not_m Γ.hE_on_m
  have hw'_not_xE : ¬ w' ≤ x ⊔ Γ.E := fun h =>
    hw'x ((hx.le_iff.mp (hxE_l ▸ le_inf h hw'_on)).resolve_left hw'.1)
  have hU_not_xE : ¬ Γ.U ≤ x ⊔ Γ.E := fun h =>
    hx_ne_U ((hx.le_iff.mp (hxE_l ▸ le_inf h le_sup_right)).resolve_left Γ.hU.1).symm
  have hl_cov_π : l ⋖ π := by
    have hV_disj_l : Γ.V ⊓ l = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have h2 := covBy_sup_of_inf_covBy_left (hV_disj_l ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ l = π from by rw [hl, hπ]; ac_rfl] at h2
  have hlE_eq_π : l ⊔ Γ.E = π := by
    have h_lt : l < l ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => Γ.hE_not_l (le_sup_right.trans h.symm.le))
    exact (hl_cov_π.eq_or_eq h_lt.le
      (sup_le le_sup_left (Γ.hE_on_m.trans hm_le_π))).resolve_left (ne_of_gt h_lt)
  have hxU_eq_l : x ⊔ Γ.U = l := by
    have h_lt : x < x ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h => hx_ne_U ((hx.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hU.1).symm)
    exact ((line_covers_its_atoms Γ.hO Γ.hU Γ.hOU hx hx_on).eq_or_eq h_lt.le
      (sup_le hx_on le_sup_right)).resolve_left (ne_of_gt h_lt)
  have hxE_cov_π : (x ⊔ Γ.E) ⋖ π := by
    have hU_disj : Γ.U ⊓ (x ⊔ Γ.E) = ⊥ :=
      (Γ.hU.le_iff.mp inf_le_left).resolve_right (fun h => hU_not_xE (h ▸ inf_le_right))
    have h2 := covBy_sup_of_inf_covBy_left (hU_disj ▸ Γ.hU.bot_covBy)
    rwa [show Γ.U ⊔ (x ⊔ Γ.E) = π from by
      rw [show Γ.U ⊔ (x ⊔ Γ.E) = (x ⊔ Γ.U) ⊔ Γ.E from by ac_rfl, hxU_eq_l, hlE_eq_π]] at h2
  have hz_atom : IsAtom z := by
    rw [hz_def, inf_comm (x ⊔ Γ.E) (w' ⊔ X)]
    exact line_meets_m_at_atom hw' hX hw'X_ne hw'X_le_π hxE_le_π hxE_cov_π hw'_not_xE
  have hz_le_xE : z ≤ x ⊔ Γ.E := inf_le_left
  have hz_le_w'X : z ≤ w' ⊔ X := inf_le_right
  have hz_le_π : z ≤ π := hz_le_xE.trans hxE_le_π
  have hw'X_l : (w' ⊔ X) ⊓ l = w' := by
    rw [sup_comm]; exact line_direction hX hX_not_l hw'_on
  have hz_not_l : ¬ z ≤ l := by
    intro h
    have hz_eq_x : z = x := (hx.le_iff.mp (hxE_l ▸ le_inf hz_le_xE h)).resolve_left hz_atom.1
    have hx_le : x ≤ w' ⊔ X := hz_eq_x ▸ hz_le_w'X
    exact hw'x ((hw'.le_iff.mp (hw'X_l ▸ le_inf hx_le hx_on)).resolve_left hx.1).symm
  have hz_not_m : ¬ z ≤ m := by
    intro h
    have hz_eq_E : z = Γ.E :=
      (Γ.hE_atom.le_iff.mp (hxE_m ▸ le_inf hz_le_xE h)).resolve_left hz_atom.1
    have hE_le : Γ.E ≤ w' ⊔ X := hz_eq_E ▸ hz_le_w'X
    have hw'_ne_E : w' ≠ Γ.E := fun hh => Γ.hE_not_l (hh ▸ hw'_on)
    have h_lt : w' < w' ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun hh => hw'_ne_E ((hw'.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have h_eq : w' ⊔ Γ.E = w' ⊔ X :=
      ((atom_covBy_join hw' hX hw'X_ne).eq_or_eq h_lt.le
        (sup_le le_sup_left hE_le)).resolve_left (ne_of_gt h_lt)
    exact hX_w'E ((le_sup_right : X ≤ w' ⊔ X).trans h_eq.symm.le)
  have hz_ne_E : z ≠ Γ.E := fun h => hz_not_m (h.le.trans Γ.hE_on_m)
  obtain ⟨hCx_atom, hCx_not_l, hCx_not_m, hCx_le_q, -⟩ := C_tower_facts Γ x hx hx_on hx_ne_O hx_ne_U
  have hCx_le_xE : parallelogram_completion Γ.O x Γ.C m ≤ x ⊔ Γ.E :=
    (inf_le_right : parallelogram_completion Γ.O x Γ.C m ≤ x ⊔ (Γ.O ⊔ Γ.C) ⊓ m)
  have hxE_q_eq : (x ⊔ Γ.E) ⊓ q = parallelogram_completion Γ.O x Γ.C m := by
    have h_ne_q : (x ⊔ Γ.E) ⊓ q ≠ q := fun heq =>
      hU_not_xE ((le_sup_left : Γ.U ≤ q).trans (inf_eq_right.mp heq))
    exact ((line_covers_its_atoms Γ.hU Γ.hC hUC hCx_atom hCx_le_q).eq_or_eq
      (le_inf hCx_le_xE hCx_le_q) inf_le_right).resolve_right h_ne_q
  have hw'_not_q : ¬ w' ≤ q := fun h =>
    hw'_ne_U ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf hw'_on h)).resolve_left hw'.1)
  have hw'X_q : (w' ⊔ X) ⊓ q = X := line_direction hw' hw'_not_q hX_q
  have hz_not_q : ¬ z ≤ q := by
    intro h
    have hz_eq_Cx : z = parallelogram_completion Γ.O x Γ.C m :=
      (hCx_atom.le_iff.mp (hxE_q_eq ▸ le_inf hz_le_xE h)).resolve_left hz_atom.1
    have hCx_le : parallelogram_completion Γ.O x Γ.C m ≤ w' ⊔ X := hz_eq_Cx ▸ hz_le_w'X
    have hCx_eq_X : parallelogram_completion Γ.O x Γ.C m = X :=
      (hX.le_iff.mp (hw'X_q ▸ le_inf hCx_le hCx_le_q)).resolve_left hCx_atom.1
    exact hX_xE (hCx_eq_X ▸ hCx_le_xE)
  have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
    have hC_ne_E : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
    have h_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hC_ne_E ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    exact ((line_covers_its_atoms Γ.hO Γ.hC hOC Γ.hC le_sup_right).eq_or_eq h_lt.le
      (sup_le le_sup_right Γ.hE_le_OC)).resolve_left (ne_of_gt h_lt)
  have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
    intro h
    have h_le : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left h
    have h_eq := ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
      (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le h_le).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)
    exact Γ.hC_not_l (h_eq ▸ le_sup_right)
  have hOC_l : (Γ.O ⊔ Γ.C) ⊓ l = Γ.O :=
    modular_intersection Γ.hO Γ.hC Γ.hU hOC Γ.hOU hUC.symm hU_not_OC
  have hz_not_OC : ¬ z ≤ Γ.O ⊔ Γ.C := by
    intro h
    have hEz_lt : Γ.E < Γ.E ⊔ z := lt_of_le_of_ne le_sup_left
      (fun hh => hz_ne_E ((Γ.hE_atom.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
        hz_atom.1))
    have hEz_eq_xE : Γ.E ⊔ z = x ⊔ Γ.E :=
      ((line_covers_its_atoms hx Γ.hE_atom hx_ne_E Γ.hE_atom le_sup_right).eq_or_eq
        hEz_lt.le (sup_le le_sup_right hz_le_xE)).resolve_left (ne_of_gt hEz_lt)
    have hEz_eq_OC : Γ.E ⊔ z = Γ.O ⊔ Γ.C :=
      ((line_covers_its_atoms Γ.hO Γ.hC hOC Γ.hE_atom Γ.hE_le_OC).eq_or_eq
        hEz_lt.le (sup_le Γ.hE_le_OC h)).resolve_left (ne_of_gt hEz_lt)
    have hx_le_OC : x ≤ Γ.O ⊔ Γ.C :=
      le_sup_left.trans ((hEz_eq_xE.symm.trans hEz_eq_OC).le)
    exact hx_ne_O ((Γ.hO.le_iff.mp (hOC_l ▸ le_inf hx_le_OC hx_on)).resolve_left hx.1)
  have hE_not_xC : ¬ Γ.E ≤ x ⊔ Γ.C := by
    intro h
    have h_lt : x < x ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun hh => hx_ne_E ((hx.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have h_eq : x ⊔ Γ.E = x ⊔ Γ.C :=
      ((atom_covBy_join hx Γ.hC hx_ne_C).eq_or_eq h_lt.le
        (sup_le le_sup_left h)).resolve_left (ne_of_gt h_lt)
    have hC_le_xE : Γ.C ≤ x ⊔ Γ.E := h_eq ▸ le_sup_right
    have hC_eq_Cx : Γ.C = parallelogram_completion Γ.O x Γ.C m :=
      (hCx_atom.le_iff.mp (hxE_q_eq ▸ le_inf hC_le_xE le_sup_right)).resolve_left Γ.hC.1
    have h_rec := recover_std Γ x hx hx_on
    rw [← hm, ← hl, ← hC_eq_Cx, hCE_eq, hOC_l] at h_rec
    exact hx_ne_O h_rec.symm
  have hz_not_xC : ¬ z ≤ x ⊔ Γ.C := by
    intro h
    have hC_ne_E : Γ.C ≠ Γ.E := fun hh => Γ.hC_not_m (hh ▸ Γ.hE_on_m)
    have h_meet : (x ⊔ Γ.C) ⊓ (x ⊔ Γ.E) = x :=
      modular_intersection hx Γ.hC Γ.hE_atom hx_ne_C hx_ne_E hC_ne_E hE_not_xC
    have hz_eq_x : z = x :=
      (hx.le_iff.mp (h_meet ▸ le_inf h hz_le_xE)).resolve_left hz_atom.1
    have hx_le : x ≤ w' ⊔ X := hz_eq_x ▸ hz_le_w'X
    exact hw'x ((hw'.le_iff.mp (hw'X_l ▸ le_inf hx_le hx_on)).resolve_left hx.1).symm
  have hX_ne_O : X ≠ Γ.O := fun h => hX_not_l (h ▸ le_sup_left)
  have hOX_l : (X ⊔ Γ.O) ⊓ l = Γ.O := line_direction hX hX_not_l le_sup_left
  have hw'_not_XO : ¬ w' ≤ X ⊔ Γ.O := fun h =>
    hw'_ne_O ((Γ.hO.le_iff.mp (hOX_l ▸ le_inf h hw'_on)).resolve_left hw'.1)
  have hz_not_OX : ¬ z ≤ Γ.O ⊔ X := by
    intro h
    have h_meet : (X ⊔ Γ.O) ⊓ (X ⊔ w') = X :=
      modular_intersection hX Γ.hO hw' hX_ne_O hw'X_ne.symm hw'_ne_O.symm hw'_not_XO
    have hz_eq_X : z = X :=
      (hX.le_iff.mp (h_meet ▸ le_inf (h.trans (sup_comm Γ.O X).le)
        (hz_le_w'X.trans (sup_comm w' X).le))).resolve_left hz_atom.1
    exact hX_xE (hz_eq_X ▸ hz_le_xE)
  have hx_ne_X : x ≠ X := fun h => hX_not_l (h ▸ hx_on)
  have hE_not_xX : ¬ Γ.E ≤ x ⊔ X := by
    intro h
    have h_lt : x < x ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun hh => hx_ne_E ((hx.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have h_eq : x ⊔ Γ.E = x ⊔ X :=
      ((atom_covBy_join hx hX hx_ne_X).eq_or_eq h_lt.le
        (sup_le le_sup_left h)).resolve_left (ne_of_gt h_lt)
    exact hX_xE ((le_sup_right : X ≤ x ⊔ X).trans h_eq.symm.le)
  have hz_not_xX : ¬ z ≤ x ⊔ X := by
    intro h
    have hE_ne_X : Γ.E ≠ X := fun hh => hX_not_m (hh ▸ Γ.hE_on_m)
    have h_meet : (x ⊔ X) ⊓ (x ⊔ Γ.E) = x :=
      modular_intersection hx hX Γ.hE_atom hx_ne_X hx_ne_E hE_ne_X.symm hE_not_xX
    have hz_eq_x : z = x :=
      (hx.le_iff.mp (h_meet ▸ le_inf h hz_le_xE)).resolve_left hz_atom.1
    have hx_le : x ≤ w' ⊔ X := hz_eq_x ▸ hz_le_w'X
    exact hw'x ((hw'.le_iff.mp (hw'X_l ▸ le_inf hx_le hx_on)).resolve_left hx.1).symm
  exact ⟨hz_atom, hz_le_π, hz_not_l, hz_not_m, hz_not_q, hz_not_OC, hz_not_xC,
    hz_not_OX, hz_not_xX⟩

/-- **The τ-inverse master lemma.**  Composing the tower translation by `x` with the
tower translation by `coord_neg Γ x` is the identity on every atom `X` of the
auxiliary line `q` in general position: `τ_x (τ_{-x} X) = X`.

This is the one composition law `beta_step_core` cannot state (the composite
parameter is `Γ.O`, not a good point).  Proof: it suffices that `τ_{-x} = τ_x⁻¹`
at `X`, i.e. `pc Γ.O n X m = pc x Γ.O X m`; both sides transport by
`parallelogram_completion_well_defined` to the common base pair `(Γ.C, C_{-x})`
at the auxiliary point `z = (x ⊔ Γ.E) ⊓ (w' ⊔ X)` — legal there because `z` is
off `q` — with `neg_tower_reverse` identifying the two base pairs, and transport
back to `X` through the pair `(z, ζ)`; `reverse_completion` closes the loop.
The fresh good point `w'` seeds only `z`. -/
theorem tau_inv_tower (Γ : CoordSystem L) (x w' X : L)
    (hx : IsAtom x) (hx_on : x ≤ Γ.O ⊔ Γ.U) (hx_ne_O : x ≠ Γ.O) (hx_ne_U : x ≠ Γ.U)
    (hw' : IsAtom w') (hw'_on : w' ≤ Γ.O ⊔ Γ.U) (hw'_ne_O : w' ≠ Γ.O)
    (hw'_ne_U : w' ≠ Γ.U) (hw'x : w' ≠ x)
    (hX : IsAtom X) (hX_q : X ≤ Γ.U ⊔ Γ.C) (hX_ne_U : X ≠ Γ.U)
    (hX_xE : ¬ X ≤ x ⊔ Γ.E) (hX_w'E : ¬ X ≤ w' ⊔ Γ.E)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    parallelogram_completion Γ.O x
      (parallelogram_completion Γ.O (coord_neg Γ x) X (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) = X := by
  set m := Γ.U ⊔ Γ.V with hm
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V with hπ
  set n := coord_neg Γ x with hn
  set C_n := parallelogram_completion Γ.O n Γ.C m with hCn_def
  have hUV : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hm_le_π : m ≤ π := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hm_cov : m ⋖ π := Γ.m_covBy_π
  have hm_line : ∀ y, IsAtom y → y ≤ m → y ⋖ m := fun y hy hle =>
    line_covers_its_atoms Γ.hU Γ.hV hUV hy hle
  have hq_le_π : Γ.U ⊔ Γ.C ≤ π := sup_le (le_sup_right.trans le_sup_left) Γ.hC_plane
  have hn_atom : IsAtom n := coord_neg_atom Γ hx hx_on hx_ne_O hx_ne_U
  have hn_on : n ≤ Γ.O ⊔ Γ.U := coord_neg_on_l Γ x
  have hn_ne_O : n ≠ Γ.O := coord_neg_ne_O Γ hx hx_on hx_ne_O hx_ne_U
  have hn_ne_U : n ≠ Γ.U := coord_neg_ne_U Γ hx hx_on hx_ne_O hx_ne_U
  have hn_not_m : ¬ n ≤ m := fun h => hn_ne_U (Γ.atom_on_both_eq_U hn_atom hn_on h)
  have hx_not_m : ¬ x ≤ m := fun h => hx_ne_U (Γ.atom_on_both_eq_U hx hx_on h)
  have hx_ne_C : x ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ hx_on)
  have hx_ne_E : x ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ hx_on)
  have hlq_eq_U : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.C) = Γ.U := by
    rw [sup_comm Γ.O Γ.U]
    exact modular_intersection Γ.hU Γ.hO Γ.hC Γ.hOU.symm hUC
      (fun h => Γ.hC_not_l (h ▸ le_sup_left))
      (fun h => Γ.hC_not_l (le_trans h (by rw [sup_comm])))
  have hqm_eq_U : (Γ.U ⊔ Γ.C) ⊓ m = Γ.U := by
    show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [this, sup_bot_eq]
  have hX_not_l : ¬ X ≤ Γ.O ⊔ Γ.U := fun h =>
    hX_ne_U ((Γ.hU.le_iff.mp (hlq_eq_U ▸ le_inf h hX_q)).resolve_left hX.1)
  have hX_not_m : ¬ X ≤ m := fun h =>
    hX_ne_U ((Γ.hU.le_iff.mp (hqm_eq_U ▸ le_inf hX_q h)).resolve_left hX.1)
  have hX_le_π : X ≤ π := hX_q.trans hq_le_π
  have hx_ne_X : x ≠ X := fun h => hX_not_l (h ▸ hx_on)
  have hO_ne_X : Γ.O ≠ X := fun h => hX_not_l (h.symm.le.trans le_sup_left)
  have hn_ne_X : n ≠ X := fun h => hX_not_l (h ▸ hn_on)
  have hxO_eq_l : x ⊔ Γ.O = Γ.O ⊔ Γ.U := by
    rw [sup_comm x Γ.O]
    have h_lt : Γ.O < Γ.O ⊔ x := lt_of_le_of_ne le_sup_left
      (fun h => hx_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left hx.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
      (sup_le le_sup_left hx_on)).resolve_left (ne_of_gt h_lt)
  have hOn_eq_l : Γ.O ⊔ n = Γ.O ⊔ Γ.U := by
    have h_lt : Γ.O < Γ.O ⊔ n := lt_of_le_of_ne le_sup_left
      (fun h => hn_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hn_atom.1))
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq h_lt.le
      (sup_le le_sup_left hn_on)).resolve_left (ne_of_gt h_lt)
  obtain ⟨hCn_atom, hCn_not_l, hCn_not_m, hCn_le_q, -⟩ :=
    C_tower_facts Γ n hn_atom hn_on hn_ne_O hn_ne_U
  have hCE_eq : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
    have hC_ne_E : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
    have h_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hC_ne_E ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    exact ((line_covers_its_atoms Γ.hO Γ.hC hOC Γ.hC le_sup_right).eq_or_eq h_lt.le
      (sup_le le_sup_right Γ.hE_le_OC)).resolve_left (ne_of_gt h_lt)
  have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
    intro h
    have h_le : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left h
    have h_eq := ((atom_covBy_join Γ.hO Γ.hC hOC).eq_or_eq
      (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt.le h_le).resolve_left
      (ne_of_gt (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt)
    exact Γ.hC_not_l (h_eq ▸ le_sup_right)
  have hOC_l : (Γ.O ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.O :=
    modular_intersection Γ.hO Γ.hC Γ.hU hOC Γ.hOU hUC.symm hU_not_OC
  have hCn_ne_C : C_n ≠ Γ.C := by
    intro h
    have h_rec : (C_n ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = n := recover_std Γ n hn_atom hn_on
    rw [h, hCE_eq, hOC_l] at h_rec
    exact hn_ne_O h_rec.symm
  have hCq_eq : Γ.C ⊔ C_n = Γ.U ⊔ Γ.C := by
    have h_lt : Γ.C < Γ.C ⊔ C_n := lt_of_le_of_ne le_sup_left
      (fun h => hCn_ne_C ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        hCn_atom.1))
    exact ((line_covers_its_atoms Γ.hU Γ.hC hUC Γ.hC le_sup_right).eq_or_eq h_lt.le
      (sup_le le_sup_right hCn_le_q)).resolve_left (ne_of_gt h_lt)
  have hntr : parallelogram_completion x Γ.O Γ.C m = C_n :=
    neg_tower_reverse Γ x hx hx_on hx_ne_O hx_ne_U R hR hR_not h_irred
  obtain ⟨hz_atom, hz_le_π, hz_not_l, hz_not_m, hz_not_q, hz_not_OC, hz_not_xC,
    hz_not_OX, hz_not_xX⟩ :=
    inv_aux_point Γ x w' X hx hx_on hx_ne_O hx_ne_U hw' hw'_on hw'_ne_O hw'_ne_U hw'x
      hX hX_q hX_ne_U hX_xE hX_w'E
  set z := (x ⊔ Γ.E) ⊓ (w' ⊔ X) with hz_def
  have hz_le_xE : z ≤ x ⊔ Γ.E := inf_le_left
  have hz_ne_x : z ≠ x := fun h => hz_not_l (h.le.trans hx_on)
  have hz_ne_O : z ≠ Γ.O := fun h => hz_not_l (h.le.trans le_sup_left)
  have hz_ne_C : z ≠ Γ.C := fun h => hz_not_q (h.le.trans le_sup_right)
  have hz_ne_X : z ≠ X := fun h => hz_not_q (h.le.trans hX_q)
  have hz_ne_n : z ≠ n := fun h => hz_not_l (h.le.trans hn_on)
  set ζ := parallelogram_completion x Γ.O z m with hζ_def
  have hζ_atom : IsAtom ζ :=
    parallelogram_completion_atom hx Γ.hO hz_atom hx_ne_O hz_ne_x.symm hz_ne_O.symm
      (hx_on.trans le_sup_left) (le_sup_left.trans le_sup_left) hz_le_π
      hm_le_π hm_cov hm_line hx_not_m Γ.hO_not_m hz_not_m
      (fun h => hz_not_l (h.trans hxO_eq_l.le))
  have hζ_ne_z : ζ ≠ z := by
    intro h
    have he_atom : IsAtom ((x ⊔ z) ⊓ m) :=
      line_meets_m_at_atom hx hz_atom hz_ne_x.symm (sup_le (hx_on.trans le_sup_left)
        hz_le_π) hm_le_π hm_cov hx_not_m
    have he_ne_z : (x ⊔ z) ⊓ m ≠ z := fun hh => hz_not_m (hh.symm.le.trans inf_le_right)
    have he_ne_O : (x ⊔ z) ⊓ m ≠ Γ.O := fun hh => Γ.hO_not_m (hh.symm.le.trans inf_le_right)
    have hz_le_Oe : z ≤ Γ.O ⊔ (x ⊔ z) ⊓ m := by
      conv_lhs => rw [← h]
      exact inf_le_right
    have hez_lt : (x ⊔ z) ⊓ m < (x ⊔ z) ⊓ m ⊔ z := lt_of_le_of_ne le_sup_left
      (fun hh => he_ne_z.symm ((he_atom.le_iff.mp
        (le_sup_right.trans hh.symm.le)).resolve_left hz_atom.1))
    have hez_eq : (x ⊔ z) ⊓ m ⊔ z = (x ⊔ z) ⊓ m ⊔ Γ.O :=
      ((atom_covBy_join he_atom Γ.hO he_ne_O).eq_or_eq hez_lt.le
        (sup_le le_sup_left (hz_le_Oe.trans (sup_comm Γ.O ((x ⊔ z) ⊓ m)).le))).resolve_left
        (ne_of_gt hez_lt)
    have hO_le_xz : Γ.O ≤ x ⊔ z :=
      (le_sup_right.trans hez_eq.symm.le).trans (sup_le inf_le_left le_sup_right)
    have h_lt2 : x < x ⊔ Γ.O := lt_of_le_of_ne le_sup_left
      (fun hh => hx_ne_O ((hx.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
        Γ.hO.1).symm)
    have hxO_eq_xz : x ⊔ Γ.O = x ⊔ z :=
      ((atom_covBy_join hx hz_atom hz_ne_x.symm).eq_or_eq h_lt2.le
        (sup_le le_sup_left hO_le_xz)).resolve_left (ne_of_gt h_lt2)
    exact hz_not_l ((le_sup_right.trans hxO_eq_xz.symm.le).trans hxO_eq_l.le)
  have hlm_eq_U : (Γ.O ⊔ Γ.U) ⊓ m = Γ.U := Γ.l_inf_m_eq_U
  have hd_atom : IsAtom ((x ⊔ Γ.O) ⊓ m) := by
    rw [hxO_eq_l, hlm_eq_U]; exact Γ.hU
  have hdir : (x ⊔ Γ.O) ⊓ m = (z ⊔ ζ) ⊓ m :=
    parallelogram_parallel_direction hz_atom hz_not_m hd_atom hζ_atom hζ_ne_z
  have hzζ_U : (z ⊔ ζ) ⊓ m = Γ.U := by rw [← hdir, hxO_eq_l, hlm_eq_U]
  have hX_not_zζ : ¬ X ≤ z ⊔ ζ := by
    intro h
    have hU_le : Γ.U ≤ z ⊔ ζ := hzζ_U ▸ (inf_le_left : (z ⊔ ζ) ⊓ m ≤ z ⊔ ζ)
    have hXU_eq_q : X ⊔ Γ.U = Γ.U ⊔ Γ.C := by
      have h_lt : X < X ⊔ Γ.U := lt_of_le_of_ne le_sup_left
        (fun hh => hX_ne_U ((hX.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
          Γ.hU.1).symm)
      exact ((line_covers_its_atoms Γ.hU Γ.hC hUC hX hX_q).eq_or_eq h_lt.le
        (sup_le hX_q le_sup_left)).resolve_left (ne_of_gt h_lt)
    have hq_le : Γ.U ⊔ Γ.C ≤ z ⊔ ζ := hXU_eq_q ▸ sup_le h hU_le
    have hq_cov : (Γ.U ⊔ Γ.C) ⋖ π := q_covBy_π Γ
    have h_lt : (Γ.U ⊔ Γ.C) < (Γ.U ⊔ Γ.C) ⊔ z := lt_of_le_of_ne le_sup_left
      (fun hh => hz_not_q (le_sup_right.trans hh.symm.le))
    have hqz_eq_π : (Γ.U ⊔ Γ.C) ⊔ z = π :=
      (hq_cov.eq_or_eq h_lt.le (sup_le hq_le_π hz_le_π)).resolve_left (ne_of_gt h_lt)
    have hπ_le : π ≤ z ⊔ ζ := by
      rw [← hqz_eq_π]
      exact sup_le hq_le le_sup_left
    have hm_le_U : m ≤ Γ.U := by
      rw [← hzζ_U]
      exact le_inf (hm_le_π.trans hπ_le) (le_refl m)
    exact hUV ((Γ.hU.le_iff.mp (le_sup_right.trans hm_le_U)).resolve_left Γ.hV.1).symm
  have h1 : ζ = parallelogram_completion Γ.C C_n z m := by
    have h1' := parallelogram_completion_well_defined hx Γ.hO Γ.hC hz_atom
      hx_ne_O hx_ne_C hz_ne_x.symm hOC hz_ne_O.symm hz_ne_C.symm
      (hx_on.trans le_sup_left) (le_sup_left.trans le_sup_left) Γ.hC_plane hz_le_π
      hm_le_π hm_cov hm_line hx_not_m Γ.hO_not_m Γ.hC_not_m hz_not_m
      (fun h => Γ.hC_not_l (h.trans hxO_eq_l.le))
      (fun h => hz_not_l (h.trans hxO_eq_l.le))
      hz_not_xC
      (by
        intro h
        have h_lt : x < x ⊔ Γ.C := lt_of_le_of_ne le_sup_left
          (fun hh => hx_ne_C ((hx.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
            Γ.hC.1).symm)
        have h_eq : x ⊔ Γ.C = x ⊔ z :=
          ((atom_covBy_join hx hz_atom hz_ne_x.symm).eq_or_eq h_lt.le
            (sup_le le_sup_left h)).resolve_left (ne_of_gt h_lt)
        exact hz_not_xC ((le_sup_right : z ≤ x ⊔ z).trans h_eq.symm.le))
      (by rw [hntr, hCq_eq]; exact hz_not_q)
      (span_plane Γ hx Γ.hC hz_atom hx_ne_C (hx_on.trans le_sup_left) Γ.hC_plane
        hz_le_π hx_not_m hz_not_xC)
      R hR hR_not h_irred
    rw [hntr] at h1'
    exact h1'
  have h2 : parallelogram_completion Γ.O n z m = parallelogram_completion Γ.C C_n z m := by
    have h2' := parallelogram_completion_well_defined Γ.hO hn_atom Γ.hC hz_atom
      hn_ne_O.symm hOC hz_ne_O.symm (fun h => Γ.hC_not_l (h ▸ hn_on)) hz_ne_n.symm
      hz_ne_C.symm
      (le_sup_left.trans le_sup_left) (hn_on.trans le_sup_left) Γ.hC_plane hz_le_π
      hm_le_π hm_cov hm_line Γ.hO_not_m hn_not_m Γ.hC_not_m hz_not_m
      (fun h => Γ.hC_not_l (h.trans hOn_eq_l.le))
      (fun h => hz_not_l (h.trans hOn_eq_l.le))
      hz_not_OC
      (by
        intro h
        have h_lt : Γ.O < Γ.O ⊔ Γ.C := lt_of_le_of_ne le_sup_left
          (fun hh => hOC ((Γ.hO.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
            Γ.hC.1).symm)
        have h_eq : Γ.O ⊔ Γ.C = Γ.O ⊔ z :=
          ((atom_covBy_join Γ.hO hz_atom hz_ne_O.symm).eq_or_eq h_lt.le
            (sup_le le_sup_left h)).resolve_left (ne_of_gt h_lt)
        exact hz_not_OC ((le_sup_right : z ≤ Γ.O ⊔ z).trans h_eq.symm.le))
      (by
        show ¬ z ≤ Γ.C ⊔ parallelogram_completion Γ.O n Γ.C m
        rw [← hCn_def, hCq_eq]
        exact hz_not_q)
      (span_plane Γ Γ.hO Γ.hC hz_atom hOC (le_sup_left.trans le_sup_left) Γ.hC_plane
        hz_le_π Γ.hO_not_m hz_not_OC)
      R hR hR_not h_irred
    exact h2'
  have hζ_eq : ζ = parallelogram_completion Γ.O n z m := h1.trans h2.symm
  have hxz_eq_xE : x ⊔ z = x ⊔ Γ.E := by
    have h_lt : x < x ⊔ z := lt_of_le_of_ne le_sup_left
      (fun hh => hz_ne_x ((hx.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
        hz_atom.1))
    exact ((atom_covBy_join hx Γ.hE_atom hx_ne_E).eq_or_eq h_lt.le
      (sup_le le_sup_left hz_le_xE)).resolve_left (ne_of_gt h_lt)
  have h3 : parallelogram_completion x Γ.O X m = parallelogram_completion z ζ X m := by
    have h3' := parallelogram_completion_well_defined hx Γ.hO hz_atom hX
      hx_ne_O hz_ne_x.symm hx_ne_X hz_ne_O.symm hO_ne_X hz_ne_X
      (hx_on.trans le_sup_left) (le_sup_left.trans le_sup_left) hz_le_π hX_le_π
      hm_le_π hm_cov hm_line hx_not_m Γ.hO_not_m hz_not_m hX_not_m
      (fun h => hz_not_l (h.trans hxO_eq_l.le))
      (fun h => hX_not_l (h.trans hxO_eq_l.le))
      (fun h => hX_xE (h.trans hxz_eq_xE.le))
      hz_not_xX
      hX_not_zζ
      (span_plane Γ hx hz_atom hX hz_ne_x.symm (hx_on.trans le_sup_left) hz_le_π
        hX_le_π hx_not_m (fun h => hX_xE (h.trans hxz_eq_xE.le)))
      R hR hR_not h_irred
    exact h3'
  have h4 : parallelogram_completion Γ.O n X m = parallelogram_completion z ζ X m := by
    have h4' := parallelogram_completion_well_defined Γ.hO hn_atom hz_atom hX
      hn_ne_O.symm hz_ne_O.symm hO_ne_X hz_ne_n.symm hn_ne_X hz_ne_X
      (le_sup_left.trans le_sup_left) (hn_on.trans le_sup_left) hz_le_π hX_le_π
      hm_le_π hm_cov hm_line Γ.hO_not_m hn_not_m hz_not_m hX_not_m
      (fun h => hz_not_l (h.trans hOn_eq_l.le))
      (fun h => hX_not_l (h.trans hOn_eq_l.le))
      (by
        intro h
        have h_lt : Γ.O < Γ.O ⊔ X := lt_of_le_of_ne le_sup_left
          (fun hh => hO_ne_X ((Γ.hO.le_iff.mp (le_sup_right.trans hh.symm.le)).resolve_left
            hX.1).symm)
        have h_eq : Γ.O ⊔ X = Γ.O ⊔ z :=
          ((atom_covBy_join Γ.hO hz_atom hz_ne_O.symm).eq_or_eq h_lt.le
            (sup_le le_sup_left h)).resolve_left (ne_of_gt h_lt)
        exact hz_not_OX ((le_sup_right : z ≤ Γ.O ⊔ z).trans h_eq.symm.le))
      hz_not_OX
      (by
        show ¬ X ≤ z ⊔ parallelogram_completion Γ.O n z m
        rw [← hζ_eq]
        exact hX_not_zζ)
      (span_plane Γ Γ.hO hz_atom hX hz_ne_O.symm (le_sup_left.trans le_sup_left)
        hz_le_π hX_le_π Γ.hO_not_m (by
          intro h
          have h_lt : Γ.O < Γ.O ⊔ X := lt_of_le_of_ne le_sup_left
            (fun hh => hO_ne_X ((Γ.hO.le_iff.mp
              (le_sup_right.trans hh.symm.le)).resolve_left hX.1).symm)
          have h_eq : Γ.O ⊔ X = Γ.O ⊔ z :=
            ((atom_covBy_join Γ.hO hz_atom hz_ne_O.symm).eq_or_eq h_lt.le
              (sup_le le_sup_left h)).resolve_left (ne_of_gt h_lt)
          exact hz_not_OX ((le_sup_right : z ≤ Γ.O ⊔ z).trans h_eq.symm.le)))
      R hR hR_not h_irred
    rw [← hζ_eq] at h4'
    exact h4'
  have hkey : parallelogram_completion Γ.O n X m = parallelogram_completion x Γ.O X m :=
    h4.trans h3.symm
  rw [hkey]
  exact reverse_completion hx Γ.hO hX hx_ne_O hx_ne_X hO_ne_X
    (hx_on.trans le_sup_left) (le_sup_left.trans le_sup_left) hX_le_π
    hm_le_π hm_cov hm_line hx_not_m Γ.hO_not_m hX_not_m
    (fun h => hX_not_l (h.trans hxO_eq_l.le))

/-- The line through a good point `x` in the direction `Γ.E` meets the auxiliary
line `q` exactly at the C-tower of `x`: `(x ⊔ Γ.E) ⊓ q = C_x`. -/
theorem tower_meets_E_line (Γ : CoordSystem L) (x : L)
    (hx : IsAtom x) (hx_on : x ≤ Γ.O ⊔ Γ.U) (hx_ne_O : x ≠ Γ.O) (hx_ne_U : x ≠ Γ.U) :
    (x ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) = parallelogram_completion Γ.O x Γ.C (Γ.U ⊔ Γ.V) := by
  obtain ⟨hCx_atom, -, -, hCx_le_q, -⟩ := C_tower_facts Γ x hx hx_on hx_ne_O hx_ne_U
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hCx_le_xE : parallelogram_completion Γ.O x Γ.C (Γ.U ⊔ Γ.V) ≤ x ⊔ Γ.E :=
    (inf_le_right : parallelogram_completion Γ.O x Γ.C (Γ.U ⊔ Γ.V)
      ≤ x ⊔ (Γ.O ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V))
  have hxE_l : (x ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = x := by
    rw [sup_comm]; exact line_direction Γ.hE_atom Γ.hE_not_l hx_on
  have hU_not_xE : ¬ Γ.U ≤ x ⊔ Γ.E := fun h =>
    hx_ne_U ((hx.le_iff.mp (hxE_l ▸ le_inf h le_sup_right)).resolve_left Γ.hU.1).symm
  have h_ne_q : (x ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) ≠ Γ.U ⊔ Γ.C := fun heq =>
    hU_not_xE ((le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.C).trans (inf_eq_right.mp heq))
  exact ((line_covers_its_atoms Γ.hU Γ.hC hUC hCx_atom hCx_le_q).eq_or_eq
    (le_inf hCx_le_xE hCx_le_q) inf_le_right).resolve_right h_ne_q

/-- C-tower injectivity: equal towers come from equal points. -/
theorem tower_inj (Γ : CoordSystem L) {x y : L}
    (hx : IsAtom x) (hy : IsAtom y)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (h : parallelogram_completion Γ.O x Γ.C (Γ.U ⊔ Γ.V)
       = parallelogram_completion Γ.O y Γ.C (Γ.U ⊔ Γ.V)) : x = y := by
  have h1 := recover_std Γ x hx hx_on
  have h2 := recover_std Γ y hy hy_on
  rw [h] at h1
  exact h1.symm.trans h2

/-! ## The two degenerate associators, as τ-inverse corollaries

The two associators that total additive associativity bottoms out at.  Both are
now corollaries of `tau_inv_tower`: two `key_identity` steps reduce each to the
half-turn involution on the C-tower of `c`, which is exactly the master lemma. -/

/-- **Generic `inv_absorb`** (`a ≠ -a`): `a + (-a + c) = c`.  Two `key_identity`
steps turn the goal into `τ_a (τ_{-a} C_c) = C_c`, which is `tau_inv_tower`
with fresh point `w' := -a`; `recover_std` reads the coordinate back off. -/
theorem inv_absorb_generic (Γ : CoordSystem L) (a c : L)
    (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hca : c ≠ a) (han : a ≠ coord_neg Γ a) (hcn : c ≠ coord_neg Γ a)
    (hat : a ≠ coord_add Γ (coord_neg Γ a) c)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ a (coord_add Γ (coord_neg Γ a) c) = c := by
  set m := Γ.U ⊔ Γ.V with hm
  set n := coord_neg Γ a with hn_def
  set t := coord_add Γ n c with ht_def
  have hn_atom : IsAtom n := coord_neg_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hn_on : n ≤ Γ.O ⊔ Γ.U := coord_neg_on_l Γ a
  have hn_ne_O : n ≠ Γ.O := coord_neg_ne_O Γ ha ha_on ha_ne_O ha_ne_U
  have hn_ne_U : n ≠ Γ.U := coord_neg_ne_U Γ ha ha_on ha_ne_O ha_ne_U
  have hnc : n ≠ c := fun h => hcn h.symm
  have ht_atom : IsAtom t :=
    coord_add_atom Γ n c hn_atom hc hn_on hc_on hn_ne_O hc_ne_O hn_ne_U hc_ne_U
  have ht_on : t ≤ Γ.O ⊔ Γ.U := inf_le_right
  have ht_ne_U : t ≠ Γ.U :=
    coord_add_ne_U' Γ n c hn_atom hc hn_on hc_on hc_ne_O hn_ne_U hc_ne_U
  have ht_ne_O : t ≠ Γ.O := by
    intro h
    have h_na : coord_add Γ n a = Γ.O := by
      rw [coord_add_comm Γ n a hn_atom ha hn_on ha_on hn_ne_O ha_ne_O hn_ne_U ha_ne_U
        (Ne.symm han) R hR hR_not h_irred]
      exact coord_add_left_neg Γ a ha ha_on ha_ne_O ha_ne_U R hR hR_not h_irred
    have hh : coord_add Γ n c = coord_add Γ n a := h.trans h_na.symm
    exact hca (coord_add_left_cancel Γ n c a hn_atom hc ha hn_on hc_on ha_on hn_ne_U hh)
  obtain ⟨hCc_atom, hCc_not_l, hCc_not_m, hCc_le_q, -⟩ :=
    C_tower_facts Γ c hc hc_on hc_ne_O hc_ne_U
  obtain ⟨hCa_atom, -, -, -, -⟩ := C_tower_facts Γ a ha ha_on ha_ne_O ha_ne_U
  obtain ⟨hCn_atom, -, -, -, -⟩ := C_tower_facts Γ n hn_atom hn_on hn_ne_O hn_ne_U
  have hCc_ne_U : parallelogram_completion Γ.O c Γ.C m ≠ Γ.U :=
    fun h => hCc_not_m (h.le.trans le_sup_left)
  have hβa : (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) = parallelogram_completion Γ.O a Γ.C m :=
    tower_meets_E_line Γ a ha ha_on ha_ne_O ha_ne_U
  have hβn : (n ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) = parallelogram_completion Γ.O n Γ.C m :=
    tower_meets_E_line Γ n hn_atom hn_on hn_ne_O hn_ne_U
  have hX_aE : ¬ parallelogram_completion Γ.O c Γ.C m ≤ a ⊔ Γ.E := by
    intro h
    have h_le : parallelogram_completion Γ.O c Γ.C m
        ≤ parallelogram_completion Γ.O a Γ.C m := hβa ▸ le_inf h hCc_le_q
    exact hca (tower_inj Γ hc ha hc_on ha_on
      ((hCa_atom.le_iff.mp h_le).resolve_left hCc_atom.1))
  have hX_nE : ¬ parallelogram_completion Γ.O c Γ.C m ≤ n ⊔ Γ.E := by
    intro h
    have h_le : parallelogram_completion Γ.O c Γ.C m
        ≤ parallelogram_completion Γ.O n Γ.C m := hβn ▸ le_inf h hCc_le_q
    exact hcn (tower_inj Γ hc hn_atom hc_on hn_on
      ((hCn_atom.le_iff.mp h_le).resolve_left hCc_atom.1))
  have hM : parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O n (parallelogram_completion Γ.O c Γ.C m) m) m
      = parallelogram_completion Γ.O c Γ.C m :=
    tau_inv_tower Γ a n (parallelogram_completion Γ.O c Γ.C m)
      ha ha_on ha_ne_O ha_ne_U hn_atom hn_on hn_ne_O hn_ne_U (Ne.symm han)
      hCc_atom hCc_le_q hCc_ne_U hX_aE hX_nE R hR hR_not h_irred
  have hki_nc : parallelogram_completion Γ.O n
      (parallelogram_completion Γ.O c Γ.C m) m
      = parallelogram_completion Γ.O t Γ.C m :=
    key_identity Γ n c hn_atom hc hn_on hc_on hn_ne_O hc_ne_O hn_ne_U hc_ne_U hnc
      R hR hR_not h_irred
  have hki_at : parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O t Γ.C m) m
      = parallelogram_completion Γ.O (coord_add Γ a t) Γ.C m :=
    key_identity Γ a t ha ht_atom ha_on ht_on ha_ne_O ht_ne_O ha_ne_U ht_ne_U hat
      R hR hR_not h_irred
  have h_eq : parallelogram_completion Γ.O (coord_add Γ a t) Γ.C m
      = parallelogram_completion Γ.O c Γ.C m := by
    rw [← hki_at, ← hki_nc]
    exact hM
  have h_at_atom : IsAtom (coord_add Γ a t) :=
    coord_add_atom Γ a t ha ht_atom ha_on ht_on ha_ne_O ht_ne_O ha_ne_U ht_ne_U
  have h1 : (parallelogram_completion Γ.O (coord_add Γ a t) Γ.C m ⊔ Γ.E)
      ⊓ (Γ.O ⊔ Γ.U) = coord_add Γ a t :=
    recover_std Γ (coord_add Γ a t) h_at_atom inf_le_right
  have h2 : (parallelogram_completion Γ.O c Γ.C m ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = c :=
    recover_std Γ c hc hc_on
  rw [h_eq] at h1
  exact h1.symm.trans h2

/-- **The characteristic-2 knot** (`a = -a`): `a + (a + c) = c`.  No longer a
knot: it is `tau_inv_tower` with `-a` rewritten to `a` by the hypothesis, the
fresh point seeded by `s = a + c` itself. -/
theorem char2_absorb (Γ : CoordSystem L) (a c : L)
    (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (hchar2 : a = coord_neg Γ a)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ a (coord_add Γ a c) = c := by
  have haa : coord_add Γ a a = Γ.O := by
    have h := coord_add_left_neg Γ a ha ha_on ha_ne_O ha_ne_U R hR hR_not h_irred
    rwa [← hchar2] at h
  by_cases hca : c = a
  · rw [hca, haa, coord_add_right_zero Γ a ha ha_on]
  set m := Γ.U ⊔ Γ.V with hm
  set s := coord_add Γ a c with hs_def
  have hs_atom : IsAtom s :=
    coord_add_atom Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U
  have hs_on : s ≤ Γ.O ⊔ Γ.U := inf_le_right
  have hs_ne_U : s ≠ Γ.U :=
    coord_add_ne_U' Γ a c ha hc ha_on hc_on hc_ne_O ha_ne_U hc_ne_U
  have hs_ne_O : s ≠ Γ.O := by
    intro h
    have hh : coord_add Γ a c = coord_add Γ a a := h.trans haa.symm
    exact hca (coord_add_left_cancel Γ a c a ha hc ha ha_on hc_on ha_on ha_ne_U hh)
  have has : a ≠ s := by
    intro h
    have h0 : coord_add Γ a c = coord_add Γ a Γ.O :=
      h.symm.trans (coord_add_right_zero Γ a ha ha_on).symm
    exact hc_ne_O (coord_add_left_cancel Γ a c Γ.O ha hc Γ.hO ha_on hc_on le_sup_left
      ha_ne_U h0)
  obtain ⟨hCc_atom, hCc_not_l, hCc_not_m, hCc_le_q, -⟩ :=
    C_tower_facts Γ c hc hc_on hc_ne_O hc_ne_U
  obtain ⟨hCa_atom, -, -, -, -⟩ := C_tower_facts Γ a ha ha_on ha_ne_O ha_ne_U
  obtain ⟨hCs_atom, -, -, -, -⟩ := C_tower_facts Γ s hs_atom hs_on hs_ne_O hs_ne_U
  have hCc_ne_U : parallelogram_completion Γ.O c Γ.C m ≠ Γ.U :=
    fun h => hCc_not_m (h.le.trans le_sup_left)
  have hβa : (a ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) = parallelogram_completion Γ.O a Γ.C m :=
    tower_meets_E_line Γ a ha ha_on ha_ne_O ha_ne_U
  have hβs : (s ⊔ Γ.E) ⊓ (Γ.U ⊔ Γ.C) = parallelogram_completion Γ.O s Γ.C m :=
    tower_meets_E_line Γ s hs_atom hs_on hs_ne_O hs_ne_U
  have hX_aE : ¬ parallelogram_completion Γ.O c Γ.C m ≤ a ⊔ Γ.E := by
    intro h
    have h_le : parallelogram_completion Γ.O c Γ.C m
        ≤ parallelogram_completion Γ.O a Γ.C m := hβa ▸ le_inf h hCc_le_q
    exact hca (tower_inj Γ hc ha hc_on ha_on
      ((hCa_atom.le_iff.mp h_le).resolve_left hCc_atom.1))
  have hX_sE : ¬ parallelogram_completion Γ.O c Γ.C m ≤ s ⊔ Γ.E := by
    intro h
    have h_le : parallelogram_completion Γ.O c Γ.C m
        ≤ parallelogram_completion Γ.O s Γ.C m := hβs ▸ le_inf h hCc_le_q
    have hcs : c = s := tower_inj Γ hc hs_atom hc_on hs_on
      ((hCs_atom.le_iff.mp h_le).resolve_left hCc_atom.1)
    have h_comm : coord_add Γ a c = coord_add Γ c a :=
      coord_add_comm Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U
        (fun h' => hca h'.symm) R hR hR_not h_irred
    have h0 : coord_add Γ c a = coord_add Γ c Γ.O := by
      rw [← h_comm, ← hs_def, ← hcs, coord_add_right_zero Γ c hc hc_on]
    exact ha_ne_O (coord_add_left_cancel Γ c a Γ.O hc ha Γ.hO hc_on ha_on le_sup_left
      hc_ne_U h0)
  have hM : parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O a (parallelogram_completion Γ.O c Γ.C m) m) m
      = parallelogram_completion Γ.O c Γ.C m := by
    have h := tau_inv_tower Γ a s (parallelogram_completion Γ.O c Γ.C m)
      ha ha_on ha_ne_O ha_ne_U hs_atom hs_on hs_ne_O hs_ne_U (Ne.symm has)
      hCc_atom hCc_le_q hCc_ne_U hX_aE hX_sE R hR hR_not h_irred
    rwa [← hchar2] at h
  have hki_ac : parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O c Γ.C m) m
      = parallelogram_completion Γ.O s Γ.C m :=
    key_identity Γ a c ha hc ha_on hc_on ha_ne_O hc_ne_O ha_ne_U hc_ne_U
      (fun h => hca h.symm) R hR hR_not h_irred
  have hki_as : parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O s Γ.C m) m
      = parallelogram_completion Γ.O (coord_add Γ a s) Γ.C m :=
    key_identity Γ a s ha hs_atom ha_on hs_on ha_ne_O hs_ne_O ha_ne_U hs_ne_U has
      R hR hR_not h_irred
  have h_eq : parallelogram_completion Γ.O (coord_add Γ a s) Γ.C m
      = parallelogram_completion Γ.O c Γ.C m := by
    rw [← hki_as, ← hki_ac]
    exact hM
  have h_as_atom : IsAtom (coord_add Γ a s) :=
    coord_add_atom Γ a s ha hs_atom ha_on hs_on ha_ne_O hs_ne_O ha_ne_U hs_ne_U
  have h1 : (parallelogram_completion Γ.O (coord_add Γ a s) Γ.C m ⊔ Γ.E)
      ⊓ (Γ.O ⊔ Γ.U) = coord_add Γ a s :=
    recover_std Γ (coord_add Γ a s) h_as_atom inf_le_right
  have h2 : (parallelogram_completion Γ.O c Γ.C m ⊔ Γ.E) ⊓ (Γ.O ⊔ Γ.U) = c :=
    recover_std Γ c hc hc_on
  rw [h_eq] at h1
  exact h1.symm.trans h2

/-- **The order-3 loop.**  If `a + a = -a` then `(-a) + (-a) = a`: the ℤ/3
sub-line closes.  A four-move corollary of `dbl_beta_generic`. -/
theorem z3_knot (Γ : CoordSystem L) (a : L)
    (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (han : a ≠ coord_neg Γ a)
    (hknot : coord_add Γ a a = coord_neg Γ a)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ (coord_neg Γ a) (coord_neg Γ a) = a := by
  set n := coord_neg Γ a with hn_def
  have hn_atom : IsAtom n := coord_neg_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hn_on : n ≤ Γ.O ⊔ Γ.U := coord_neg_on_l Γ a
  have hn_ne_O : n ≠ Γ.O := coord_neg_ne_O Γ ha ha_on ha_ne_O ha_ne_U
  have hn_ne_U : n ≠ Γ.U := coord_neg_ne_U Γ ha ha_on ha_ne_O ha_ne_U
  have hβ : parallelogram_completion Γ.O (coord_add Γ a a)
      (parallelogram_completion Γ.O n Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O a
        (parallelogram_completion Γ.O a
          (parallelogram_completion Γ.O n Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) :=
    dbl_beta_generic Γ a n ha hn_atom ha_on hn_on ha_ne_O hn_ne_O ha_ne_U hn_ne_U
      (by rw [hknot]; exact hn_ne_O) R hR hR_not h_irred
  have hki_an : parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O n Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_add Γ a n) Γ.C (Γ.U ⊔ Γ.V) :=
    key_identity Γ a n ha hn_atom ha_on hn_on ha_ne_O hn_ne_O ha_ne_U hn_ne_U han
      R hR hR_not h_irred
  have h_an : coord_add Γ a n = Γ.O :=
    coord_add_left_neg Γ a ha ha_on ha_ne_O ha_ne_U R hR hR_not h_irred
  rw [h_an, C_O_eq_C Γ] at hki_an
  rw [hknot, hki_an] at hβ
  have hdbl : parallelogram_completion Γ.O n
      (parallelogram_completion Γ.O n Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_add Γ n n) Γ.C (Γ.U ⊔ Γ.V) :=
    dbl_key_identity Γ n a hn_atom ha hn_on ha_on hn_ne_O ha_ne_O hn_ne_U ha_ne_U
      (fun h => han h.symm) R hR hR_not h_irred
  rw [hdbl] at hβ
  exact tower_inj Γ
    (coord_add_atom Γ n n hn_atom hn_atom hn_on hn_on hn_ne_O hn_ne_O hn_ne_U hn_ne_U)
    ha inf_le_right ha_on hβ

/-- **Double plus negative** (`a + a ≠ -a`): `(a + a) + (-a) = a`. -/
theorem dbl_plus_neg (Γ : CoordSystem L) (a : L)
    (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (han : a ≠ coord_neg Γ a)
    (hs_ne_O : coord_add Γ a a ≠ Γ.O)
    (hsn : coord_add Γ a a ≠ coord_neg Γ a)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ (coord_add Γ a a) (coord_neg Γ a) = a := by
  set n := coord_neg Γ a with hn_def
  set s := coord_add Γ a a with hs_def
  have hn_atom : IsAtom n := coord_neg_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hn_on : n ≤ Γ.O ⊔ Γ.U := coord_neg_on_l Γ a
  have hn_ne_O : n ≠ Γ.O := coord_neg_ne_O Γ ha ha_on ha_ne_O ha_ne_U
  have hn_ne_U : n ≠ Γ.U := coord_neg_ne_U Γ ha ha_on ha_ne_O ha_ne_U
  have hs_atom : IsAtom s :=
    coord_add_atom Γ a a ha ha ha_on ha_on ha_ne_O ha_ne_O ha_ne_U ha_ne_U
  have hs_on : s ≤ Γ.O ⊔ Γ.U := inf_le_right
  have hs_ne_U : s ≠ Γ.U :=
    coord_add_ne_U' Γ a a ha ha ha_on ha_on ha_ne_O ha_ne_U ha_ne_U
  have hβ : parallelogram_completion Γ.O s
      (parallelogram_completion Γ.O n Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O a
        (parallelogram_completion Γ.O a
          (parallelogram_completion Γ.O n Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) :=
    dbl_beta_generic Γ a n ha hn_atom ha_on hn_on ha_ne_O hn_ne_O ha_ne_U hn_ne_U
      hs_ne_O R hR hR_not h_irred
  have hki_an : parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O n Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_add Γ a n) Γ.C (Γ.U ⊔ Γ.V) :=
    key_identity Γ a n ha hn_atom ha_on hn_on ha_ne_O hn_ne_O ha_ne_U hn_ne_U han
      R hR hR_not h_irred
  have h_an : coord_add Γ a n = Γ.O :=
    coord_add_left_neg Γ a ha ha_on ha_ne_O ha_ne_U R hR hR_not h_irred
  rw [h_an, C_O_eq_C Γ] at hki_an
  rw [hki_an] at hβ
  have hki_sn : parallelogram_completion Γ.O s
      (parallelogram_completion Γ.O n Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_add Γ s n) Γ.C (Γ.U ⊔ Γ.V) :=
    key_identity Γ s n hs_atom hn_atom hs_on hn_on hs_ne_O hn_ne_O hs_ne_U hn_ne_U hsn
      R hR hR_not h_irred
  rw [hki_sn] at hβ
  exact tower_inj Γ
    (coord_add_atom Γ s n hs_atom hn_atom hs_on hn_on hs_ne_O hn_ne_O hs_ne_U hn_ne_U)
    ha inf_le_right ha_on hβ

/-- **The squared double** (`c = a + a` branch of the doubling wall, generic):
`(a+a) + (a+a) = a + (a + (a+a))`. -/
theorem dbl_assoc_sq (Γ : CoordSystem L) (a : L)
    (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (ha_ne_U : a ≠ Γ.U)
    (hs_ne_O : coord_add Γ a a ≠ Γ.O)
    (has2 : coord_add Γ a (coord_add Γ a a) ≠ Γ.O)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_add Γ (coord_add Γ a a) (coord_add Γ a a)
      = coord_add Γ a (coord_add Γ a (coord_add Γ a a)) := by
  set s := coord_add Γ a a with hs_def
  have hs_atom : IsAtom s :=
    coord_add_atom Γ a a ha ha ha_on ha_on ha_ne_O ha_ne_O ha_ne_U ha_ne_U
  have hs_on : s ≤ Γ.O ⊔ Γ.U := inf_le_right
  have hs_ne_U : s ≠ Γ.U :=
    coord_add_ne_U' Γ a a ha ha ha_on ha_on ha_ne_O ha_ne_U ha_ne_U
  have has : a ≠ s := by
    intro h
    have h2 : coord_add Γ a Γ.O = coord_add Γ a a :=
      (coord_add_right_zero Γ a ha ha_on).trans h
    exact ha_ne_O (coord_add_left_cancel Γ a Γ.O a ha Γ.hO ha ha_on le_sup_left ha_on
      ha_ne_U h2).symm
  have has_atom : IsAtom (coord_add Γ a s) :=
    coord_add_atom Γ a s ha hs_atom ha_on hs_on ha_ne_O hs_ne_O ha_ne_U hs_ne_U
  have has_ne_U : coord_add Γ a s ≠ Γ.U :=
    coord_add_ne_U' Γ a s ha hs_atom ha_on hs_on hs_ne_O ha_ne_U hs_ne_U
  have ha_ne_as : a ≠ coord_add Γ a s := by
    intro h
    have h2 : coord_add Γ a Γ.O = coord_add Γ a s :=
      (coord_add_right_zero Γ a ha ha_on).trans h
    exact hs_ne_O (coord_add_left_cancel Γ a Γ.O s ha Γ.hO hs_atom ha_on le_sup_left
      hs_on ha_ne_U h2).symm
  have hdbl : parallelogram_completion Γ.O s
      (parallelogram_completion Γ.O s Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_add Γ s s) Γ.C (Γ.U ⊔ Γ.V) :=
    dbl_key_identity Γ s a hs_atom ha hs_on ha_on hs_ne_O ha_ne_O hs_ne_U ha_ne_U
      (Ne.symm has) R hR hR_not h_irred
  have hβ : parallelogram_completion Γ.O s
      (parallelogram_completion Γ.O s Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O a
        (parallelogram_completion Γ.O a
          (parallelogram_completion Γ.O s Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V) :=
    dbl_beta_generic Γ a s ha hs_atom ha_on hs_on ha_ne_O hs_ne_O ha_ne_U hs_ne_U
      hs_ne_O R hR hR_not h_irred
  have hki_as : parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O s Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_add Γ a s) Γ.C (Γ.U ⊔ Γ.V) :=
    key_identity Γ a s ha hs_atom ha_on hs_on ha_ne_O hs_ne_O ha_ne_U hs_ne_U has
      R hR hR_not h_irred
  have hki_aas : parallelogram_completion Γ.O a
      (parallelogram_completion Γ.O (coord_add Γ a s) Γ.C (Γ.U ⊔ Γ.V)) (Γ.U ⊔ Γ.V)
      = parallelogram_completion Γ.O (coord_add Γ a (coord_add Γ a s)) Γ.C (Γ.U ⊔ Γ.V) :=
    key_identity Γ a (coord_add Γ a s) ha has_atom ha_on inf_le_right ha_ne_O has2
      ha_ne_U has_ne_U ha_ne_as R hR hR_not h_irred
  rw [hki_as, hki_aas] at hβ
  rw [hdbl] at hβ
  exact tower_inj Γ
    (coord_add_atom Γ s s hs_atom hs_atom hs_on hs_on hs_ne_O hs_ne_O hs_ne_U hs_ne_U)
    (coord_add_atom Γ a (coord_add Γ a s) ha has_atom ha_on inf_le_right ha_ne_O has2
      ha_ne_U has_ne_U)
    inf_le_right inf_le_right hβ

namespace Coordinate

variable {Φ : CoordFrame L}

/-! ## Total cancellation, lifted to `Coordinate Φ.Γ` -/

/-- Left cancellation is TOTAL at the `Coordinate` level: the only side condition of
`coord_add_left_cancel` is `a ≠ U`, which every coordinate satisfies. -/
theorem fadd_left_cancel (a b c : Coordinate Φ.Γ) (h : fadd a b = fadd a c) : b = c := by
  apply Coordinate.ext
  exact coord_add_left_cancel Φ.Γ a.1 b.1 c.1 a.isAtom b.isAtom c.isAtom
    a.on_l b.on_l c.on_l a.ne_U (congrArg Subtype.val h)

/-! ## Total commutativity, lifted to `Coordinate Φ.Γ` -/

theorem fadd_comm (a b : Coordinate Φ.Γ) : fadd a b = fadd b a := by
  apply Coordinate.ext
  show coord_add Φ.Γ a.1 b.1 = coord_add Φ.Γ b.1 a.1
  by_cases ha : a.1 = Φ.Γ.O
  · rw [ha, coord_add_left_zero Φ.Γ b.1 b.isAtom b.on_l b.ne_U,
        coord_add_right_zero Φ.Γ b.1 b.isAtom b.on_l]
  by_cases hb : b.1 = Φ.Γ.O
  · rw [hb, coord_add_left_zero Φ.Γ a.1 a.isAtom a.on_l a.ne_U,
        coord_add_right_zero Φ.Γ a.1 a.isAtom a.on_l]
  by_cases hab : a.1 = b.1
  · rw [hab]
  · exact coord_add_comm Φ.Γ a.1 b.1 a.isAtom b.isAtom a.on_l b.on_l ha hb
      a.ne_U b.ne_U hab Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred

/-- Right cancellation is TOTAL: from left cancellation and total commutativity. -/
theorem fadd_right_cancel (a b c : Coordinate Φ.Γ) (h : fadd a c = fadd b c) : a = b := by
  apply fadd_left_cancel c a b
  rw [fadd_comm c a, fadd_comm c b]; exact h

/-! ## Zero laws (already sorry-free upstream, restated at `fadd`) -/

theorem fadd_zero (a : Coordinate Φ.Γ) : fadd a 0 = a :=
  Coordinate.ext (coord_add_right_zero Φ.Γ a.1 a.isAtom a.on_l)

theorem fzero_add (a : Coordinate Φ.Γ) : fadd 0 a = a :=
  Coordinate.ext (coord_add_left_zero Φ.Γ a.1 a.isAtom a.on_l a.ne_U)

/-! ## Negation laws (total) -/

/-- `(fneg a).1` when `a.1 ≠ O` is `coord_neg`. -/
theorem fneg_val_of_ne (a : Coordinate Φ.Γ) (h : a.1 ≠ Φ.Γ.O) :
    (fneg a).1 = coord_neg Φ.Γ a.1 := by
  simp only [fneg, dif_neg h]

theorem fneg_val_of_eq (a : Coordinate Φ.Γ) (h : a.1 = Φ.Γ.O) :
    (fneg a).1 = Φ.Γ.O := by
  simp only [fneg, dif_pos h]

/-- `a + (-a) = 0`, total. -/
theorem fadd_neg (a : Coordinate Φ.Γ) : fadd a (fneg a) = 0 := by
  apply Coordinate.ext
  show coord_add Φ.Γ a.1 (fneg a).1 = (0 : Coordinate Φ.Γ).1
  by_cases h : a.1 = Φ.Γ.O
  · rw [fneg_val_of_eq a h, h, coord_add_right_zero Φ.Γ Φ.Γ.O Φ.Γ.hO le_sup_left]; rfl
  · rw [fneg_val_of_ne a h]
    exact coord_add_left_neg Φ.Γ a.1 a.isAtom a.on_l h a.ne_U Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred

/-- `(-a) + a = 0`, total. -/
theorem fneg_add (a : Coordinate Φ.Γ) : fadd (fneg a) a = 0 := by
  rw [fadd_comm]; exact fadd_neg a

/-- Double negation, total (via cancellation). -/
theorem fneg_fneg (a : Coordinate Φ.Γ) : fneg (fneg a) = a := by
  apply fadd_left_cancel (fneg a)
  rw [fadd_neg (fneg a), fneg_add a]

/-! ## `≠ 0` unfolding helpers -/

theorem val_ne_O_of_ne_zero {a : Coordinate Φ.Γ} (h : a ≠ 0) : a.1 ≠ Φ.Γ.O :=
  fun hv => h (Coordinate.ext hv)

theorem ne_zero_of_val_ne_O {a : Coordinate Φ.Γ} (h : a.1 ≠ Φ.Γ.O) : a ≠ 0 :=
  fun hv => h (congrArg Subtype.val hv)

theorem fadd_val_ne_O_of_ne_zero {a b : Coordinate Φ.Γ} (h : fadd a b ≠ 0) :
    coord_add Φ.Γ a.1 b.1 ≠ Φ.Γ.O :=
  fun hv => h (Coordinate.ext hv)

/-! ## Generic associativity, lifted to `Coordinate Φ.Γ`

All `≠ U` conditions are discharged automatically (`.ne_U`).  The unused geometric
hypothesis `a ≠ c` of `coord_add_assoc` is handled here by pure commutativity when
`a = c`, so callers need not supply it. -/

theorem fadd_assoc_generic (a b c : Coordinate Φ.Γ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hs : fadd a b ≠ 0) (ht : fadd b c ≠ 0)
    (hsc : fadd a b ≠ c) (hat : a ≠ fadd b c) :
    fadd (fadd a b) c = fadd a (fadd b c) := by
  by_cases hac : a = c
  ·
    subst hac
    rw [show fadd (fadd a b) a = fadd a (fadd a b) from fadd_comm (fadd a b) a,
        show fadd b a = fadd a b from fadd_comm b a]
  · apply Coordinate.ext
    show coord_add Φ.Γ (coord_add Φ.Γ a.1 b.1) c.1
       = coord_add Φ.Γ a.1 (coord_add Φ.Γ b.1 c.1)
    exact coord_add_assoc Φ.Γ a.1 b.1 c.1 a.isAtom b.isAtom c.isAtom
      a.on_l b.on_l c.on_l
      (val_ne_O_of_ne_zero ha) (val_ne_O_of_ne_zero hb) (val_ne_O_of_ne_zero hc)
      a.ne_U b.ne_U c.ne_U
      (fun h => hab (Coordinate.ext h)) (fun h => hbc (Coordinate.ext h))
      (fun h => hac (Coordinate.ext h))
      (fadd_val_ne_O_of_ne_zero hs) (add_ne_U a b)
      (fadd_val_ne_O_of_ne_zero ht) (add_ne_U b c)
      (fun h => hsc (Coordinate.ext h)) (fun h => hat (Coordinate.ext h))
      Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred

/-! ## Reversal symmetry of the associativity goal (pure commutativity) -/

/-- `G(c,b,a) → G(a,b,c)`.  The associativity statement is invariant under reversing
the outer operands, provably from commutativity alone. -/
theorem assoc_symm (a b c : Coordinate Φ.Γ)
    (H : fadd (fadd c b) a = fadd c (fadd b a)) :
    fadd (fadd a b) c = fadd a (fadd b c) :=
  calc fadd (fadd a b) c
      = fadd c (fadd a b) := fadd_comm _ _
    _ = fadd c (fadd b a) := by rw [fadd_comm a b]
    _ = fadd (fadd c b) a := H.symm
    _ = fadd a (fadd c b) := fadd_comm _ _
    _ = fadd a (fadd b c) := by rw [fadd_comm c b]

/-! ## GEOMETRIC CORE 2 — doubling (proved first; core 1 uses its mirror)

`(a + a) + c = a + (a + c)`.  `coord_add_assoc` cannot be invoked (routes through
`key_identity`, which requires the two summands distinct).  Totalized from
`coord_double_left_generic'` (the char-≠2 wall), `char2_absorb` (the char-2
branch, a τ-inverse corollary), and the three doubling satellites `z3_knot`,
`dbl_plus_neg`, `dbl_assoc_sq`. -/
theorem double_left (a c : Coordinate Φ.Γ) :
    fadd (fadd a a) c = fadd a (fadd a c) := by
  by_cases ha0 : a = 0
  · subst ha0; simp only [fadd_zero, fzero_add]
  by_cases hc0 : c = 0
  · subst hc0; simp only [fadd_zero]
  by_cases hca : c = a
  · subst hca; exact fadd_comm (fadd c c) c
  by_cases hchar2 : a = fneg a
  · have haa0 : fadd a a = 0 := by
      have h := fadd_neg a
      rwa [← hchar2] at h
    have hval : a.1 = coord_neg Φ.Γ a.1 :=
      (congrArg Subtype.val hchar2).trans (fneg_val_of_ne a (val_ne_O_of_ne_zero ha0))
    rw [haa0, fzero_add c]
    exact (Coordinate.ext (char2_absorb Φ.Γ a.1 c.1 a.isAtom c.isAtom a.on_l c.on_l
      (val_ne_O_of_ne_zero ha0) (val_ne_O_of_ne_zero hc0) a.ne_U c.ne_U hval
      Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred)).symm
  have haa0 : fadd a a ≠ 0 :=
    fun h => hchar2 (fadd_left_cancel a a (fneg a) (h.trans (fadd_neg a).symm))
  have hanval : a.1 ≠ coord_neg Φ.Γ a.1 := fun h =>
    hchar2 (Coordinate.ext (h.trans (fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)).symm))
  by_cases hcs : c = fadd a a
  · by_cases has2 : fadd a (fadd a a) = 0
    · have hsn : fadd a a = fneg a :=
        fadd_left_cancel a _ _ (has2.trans (fadd_neg a).symm)
      have hknotval : coord_add Φ.Γ a.1 a.1 = (fneg a).1 := congrArg Subtype.val hsn
      rw [fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)] at hknotval
      rw [hcs, has2, fadd_zero a, hsn]
      apply Coordinate.ext
      show coord_add Φ.Γ (fneg a).1 (fneg a).1 = a.1
      rw [fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)]
      exact z3_knot Φ.Γ a.1 a.isAtom a.on_l (val_ne_O_of_ne_zero ha0) a.ne_U hanval
        hknotval Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred
    · rw [hcs]
      exact Coordinate.ext (dbl_assoc_sq Φ.Γ a.1 a.isAtom a.on_l
        (val_ne_O_of_ne_zero ha0) a.ne_U (fadd_val_ne_O_of_ne_zero haa0)
        (fadd_val_ne_O_of_ne_zero has2) Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred)
  by_cases hcn : c = fneg a
  · rw [hcn, fadd_neg a, fadd_zero a]
    by_cases hsn : fadd a a = fneg a
    · have hknotval : coord_add Φ.Γ a.1 a.1 = (fneg a).1 := congrArg Subtype.val hsn
      rw [fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)] at hknotval
      rw [hsn]
      apply Coordinate.ext
      show coord_add Φ.Γ (fneg a).1 (fneg a).1 = a.1
      rw [fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)]
      exact z3_knot Φ.Γ a.1 a.isAtom a.on_l (val_ne_O_of_ne_zero ha0) a.ne_U hanval
        hknotval Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred
    · have hsnval : coord_add Φ.Γ a.1 a.1 ≠ coord_neg Φ.Γ a.1 := by
        intro h
        have h2 : coord_add Φ.Γ a.1 a.1 = (fneg a).1 := by
          rw [fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)]
          exact h
        exact hsn (Coordinate.ext h2)
      apply Coordinate.ext
      show coord_add Φ.Γ (coord_add Φ.Γ a.1 a.1) (fneg a).1 = a.1
      rw [fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)]
      exact dbl_plus_neg Φ.Γ a.1 a.isAtom a.on_l (val_ne_O_of_ne_zero ha0) a.ne_U
        hanval (fadd_val_ne_O_of_ne_zero haa0) hsnval Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred
  · have ht_ne_O : coord_add Φ.Γ a.1 c.1 ≠ Φ.Γ.O := by
      intro h
      exact hcn (fadd_left_cancel a c (fneg a) ((Coordinate.ext h).trans (fadd_neg a).symm))
    exact Coordinate.ext (coord_double_left_generic' Φ.Γ a.1 c.1 a.isAtom c.isAtom
      a.on_l c.on_l (val_ne_O_of_ne_zero ha0) (val_ne_O_of_ne_zero hc0) a.ne_U c.ne_U
      (fun h => hca (Coordinate.ext h.symm)) (fadd_val_ne_O_of_ne_zero haa0)
      (fun h => hcs (Coordinate.ext h.symm)) ht_ne_O Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred)

/-- The mirror doubling `(a + c) + c = a + (c + c)`, from `double_left` + reversal. -/
theorem double_right (a c : Coordinate Φ.Γ) :
    fadd (fadd a c) c = fadd a (fadd c c) :=
  assoc_symm a c c (double_left c a)

/-! ## GEOMETRIC CORE 1 — inverse absorption

`a + (-a + c) = c`.  The degenerate associator `A(a,-a,c)`, blocked from
`coord_add_assoc` because the intermediate `a + (-a) = O` violates its `≠O` side
conditions.  Totalized from `inv_absorb_generic` (the τ-inverse corollary),
`char2_absorb`, and `double_right` for the coincident slivers. -/
theorem inv_absorb (a c : Coordinate Φ.Γ) :
    fadd a (fadd (fneg a) c) = c := by
  by_cases ha0 : a = 0
  · have hn0 : fneg (0 : Coordinate Φ.Γ) = 0 := by
      apply fadd_left_cancel (0 : Coordinate Φ.Γ)
      rw [fadd_neg (0 : Coordinate Φ.Γ), fadd_zero (0 : Coordinate Φ.Γ)]
    subst ha0
    rw [hn0, fzero_add c, fzero_add c]
  by_cases hc0 : c = 0
  · subst hc0
    rw [fadd_zero (fneg a), fadd_neg a]
  by_cases hca : c = a
  · rw [hca, fneg_add a, fadd_zero a]
  by_cases hchar2 : a = fneg a
  · have hval : a.1 = coord_neg Φ.Γ a.1 :=
      (congrArg Subtype.val hchar2).trans (fneg_val_of_ne a (val_ne_O_of_ne_zero ha0))
    rw [← hchar2]
    exact Coordinate.ext (char2_absorb Φ.Γ a.1 c.1 a.isAtom c.isAtom a.on_l c.on_l
      (val_ne_O_of_ne_zero ha0) (val_ne_O_of_ne_zero hc0) a.ne_U c.ne_U hval
      Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred)
  by_cases hcn : c = fneg a
  · rw [hcn, ← double_right a (fneg a), fadd_neg a, fzero_add]
  by_cases hat : a = fadd (fneg a) c
  · have h1 : fadd (fneg a) (fadd a a) = a := by
      rw [← double_right (fneg a) a, fneg_add a, fzero_add a]
    have h3 : fadd a a = c := fadd_left_cancel (fneg a) _ _ (h1.trans hat)
    rw [← hat, h3]
  · have hanval : a.1 ≠ coord_neg Φ.Γ a.1 := fun h =>
      hchar2 (Coordinate.ext (h.trans (fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)).symm))
    have hcnval : c.1 ≠ coord_neg Φ.Γ a.1 := fun h =>
      hcn (Coordinate.ext (h.trans (fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)).symm))
    have hatval : a.1 ≠ coord_add Φ.Γ (coord_neg Φ.Γ a.1) c.1 := by
      intro h
      apply hat
      apply Coordinate.ext
      show a.1 = coord_add Φ.Γ (fneg a).1 c.1
      rw [fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)]
      exact h
    apply Coordinate.ext
    show coord_add Φ.Γ a.1 (coord_add Φ.Γ (fneg a).1 c.1) = c.1
    rw [fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)]
    exact inv_absorb_generic Φ.Γ a.1 c.1 a.isAtom c.isAtom a.on_l c.on_l
      (val_ne_O_of_ne_zero ha0) (val_ne_O_of_ne_zero hc0) a.ne_U c.ne_U
      (fun h => hca (Coordinate.ext h)) hanval hcnval hatval
      Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred

/-- The mirror: `-a + (a + c) = c`, from `inv_absorb` and double negation. -/
theorem inv_absorb' (a c : Coordinate Φ.Γ) :
    fadd (fneg a) (fadd a c) = c := by
  have := inv_absorb (fneg a) c
  rwa [fneg_fneg] at this

/-! ## Degenerate-case lemmas (each reduced to the two cores + cancellation) -/

/-- `s = a + b = O` case: then `b = -a`, and the associator collapses by `inv_absorb`. -/
theorem assoc_inv_left (a c : Coordinate Φ.Γ) :
    fadd (fadd a (fneg a)) c = fadd a (fadd (fneg a) c) := by
  rw [fadd_neg a, fzero_add c, inv_absorb a c]

/-- `t = b + c = O` case (mirror): `c = -b`, associator collapses. -/
theorem assoc_inv_right (a b : Coordinate Φ.Γ) :
    fadd (fadd a b) (fneg b) = fadd a (fadd b (fneg b)) := by
  refine assoc_symm a b (fneg b) ?_
  rw [fneg_add b, fzero_add a, inv_absorb' b a]

/-- `s = a + b = c` case (E): collapses via `inv_absorb'` + `double_right`. -/
theorem assoc_sum_eq_right (a b : Coordinate Φ.Γ) :
    fadd (fadd a b) (fadd a b) = fadd a (fadd b (fadd a b)) := by
  apply fadd_left_cancel (fneg a)
  rw [inv_absorb' a (fadd b (fadd a b))]
  rw [← double_right (fneg a) (fadd a b), inv_absorb' a b]

/-- `a = b + c` case (mirror of E), via reversal. -/
theorem assoc_sum_eq_left (b c : Coordinate Φ.Γ) :
    fadd (fadd (fadd b c) b) c = fadd (fadd b c) (fadd b c) := by
  refine assoc_symm (fadd b c) b c ?_
  have h := assoc_sum_eq_right c b
  rw [show fadd c b = fadd b c from fadd_comm c b] at h ⊢
  exact h

/-! ## TOTAL associativity — the master case split -/

theorem fadd_assoc_total (a b c : Coordinate Φ.Γ) :
    fadd (fadd a b) c = fadd a (fadd b c) := by
  by_cases ha0 : a = 0
  · subst ha0; rw [fzero_add b, fzero_add (fadd b c)]
  by_cases hb0 : b = 0
  · subst hb0; rw [fadd_zero a, fzero_add c]
  by_cases hc0 : c = 0
  · subst hc0; rw [fadd_zero (fadd a b), fadd_zero b]
  by_cases hab : a = b
  · subst hab; exact double_left a c
  by_cases hbc : b = c
  · subst hbc; exact double_right a b
  by_cases hs0 : fadd a b = 0
  ·
    have hb_eq : b = fneg a := fadd_left_cancel a b (fneg a) (hs0.trans (fadd_neg a).symm)
    subst hb_eq; exact assoc_inv_left a c
  by_cases ht0 : fadd b c = 0
  ·
    have hc_eq : c = fneg b := fadd_left_cancel b c (fneg b) (ht0.trans (fadd_neg b).symm)
    subst hc_eq; exact assoc_inv_right a b
  by_cases hsc : fadd a b = c
  · subst hsc; exact assoc_sum_eq_right a b
  by_cases hat : a = fadd b c
  · subst hat; exact assoc_sum_eq_left b c
  exact fadd_assoc_generic a b c ha0 hb0 hc0 hab hbc hs0 ht0 hsc hat

end Coordinate

/-! ## Axiom receipts

Everything is axiom-clean (`[propext, Classical.choice, Quot.sound]`) —
`fadd_assoc_total` included: the additive group of the FTPG coordinate line is
CLOSED, no `sorryAx` anywhere in its trace. -/

/-- info: 'Foam.Bridges.reverse_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reverse_completion

/-- info: 'Foam.Bridges.pc_id_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pc_id_left

/-- info: 'Foam.Bridges.C_O_eq_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms C_O_eq_C

/-- info: 'Foam.Bridges.recover_std' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms recover_std

/-- info: 'Foam.Bridges.coord_add_eq_translation_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_add_eq_translation_diag

/-- info: 'Foam.Bridges.dbl_aux_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dbl_aux_point

/-- info: 'Foam.Bridges.beta_step_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms beta_step_core

/-- info: 'Foam.Bridges.key_identity_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms key_identity_core

/-- info: 'Foam.Bridges.dbl_key_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dbl_key_identity

/-- info: 'Foam.Bridges.dbl_beta_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dbl_beta_generic

/-- info: 'Foam.Bridges.coord_double_left_generic'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coord_double_left_generic'

/-- info: 'Foam.Bridges.C_tower_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms C_tower_facts

/-- info: 'Foam.Bridges.grounding_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms grounding_left

/-- info: 'Foam.Bridges.grounding_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms grounding_right

/-- info: 'Foam.Bridges.noncol_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noncol_symm

/-- info: 'Foam.Bridges.base_change_hinv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms base_change_hinv

/-- info: 'Foam.Bridges.inv_absorb_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inv_absorb_core

/-- info: 'Foam.Bridges.Coordinate.fadd_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Coordinate.fadd_comm

/-- info: 'Foam.Bridges.Coordinate.fadd_assoc_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Coordinate.fadd_assoc_generic

/-- info: 'Foam.Bridges.neg_tower_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms neg_tower_reverse

/-- info: 'Foam.Bridges.q_covBy_π' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms q_covBy_π

/-- info: 'Foam.Bridges.span_plane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms span_plane

/-- info: 'Foam.Bridges.inv_aux_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inv_aux_point

/-- info: 'Foam.Bridges.tau_inv_tower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tau_inv_tower

/-- info: 'Foam.Bridges.tower_meets_E_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tower_meets_E_line

/-- info: 'Foam.Bridges.tower_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tower_inj

/-- info: 'Foam.Bridges.inv_absorb_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inv_absorb_generic

/-- info: 'Foam.Bridges.char2_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms char2_absorb

/-- info: 'Foam.Bridges.z3_knot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms z3_knot

/-- info: 'Foam.Bridges.dbl_plus_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dbl_plus_neg

/-- info: 'Foam.Bridges.dbl_assoc_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dbl_assoc_sq

/-- info: 'Foam.Bridges.Coordinate.double_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Coordinate.double_left

/-- info: 'Foam.Bridges.Coordinate.inv_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Coordinate.inv_absorb

/-- info: 'Foam.Bridges.Coordinate.fadd_assoc_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Coordinate.fadd_assoc_total

end Foam.Bridges
