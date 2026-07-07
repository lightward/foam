import Bridges.FTPG.Plane
import Bridges.FTPG.Iso

/-!
# Camp three, second pitch: the plane interval is the subspace lattice

`Plane.lean` put the *atoms* of the frame plane `π = O ⊔ U ⊔ V` in bijection
with the projective points of `(Dᵐᵒᵖ)³`.  This file extends the bijection to
every element of the interval `[⊥, π]`: the interval is order-isomorphic to
the full submodule lattice of `(Dᵐᵒᵖ)³`, heights 0/1/2/3 landing on
finranks 0/1/2/3.

* `line_covBy_π` — every join of two distinct plane atoms is covered by `π`:
  the trace atom on `m` is covered in `m`, and the modular law transports the
  covering up the sup.
* `plane_flat_cases` — the height classification: every `x ≤ π` is `⊥`, an
  atom, a join of two distinct atoms, or `π` itself.
* `planeFlat` — the span of the coordinate vectors of the atoms below `x`.
* `flat_rank_zero` … `flat_rank_three` — submodules of `K³` classified by
  finrank, over any division ring.
* `plane_interval_iso` — the summit: `Set.Iic π ≃o Submodule Dᵐᵒᵖ (Dᵐᵒᵖ)³`,
  the `PointSystem` conclusion realized on the interval `[⊥, π]`.
-/

namespace Foam.Bridges

universe u

/-! ## The abstract linear side: submodules of `K³` classified by finrank -/

section FlatLinear

open Module

variable {K : Type*} [DivisionRing K]

theorem flat_span_basis_val {n : ℕ} (W : Submodule K (Fin 3 → K))
    (b : Basis (Fin n) K W) :
    Submodule.span K (Subtype.val '' Set.range b) = W := by
  have h := congrArg (Submodule.map W.subtype) b.span_eq
  rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h

theorem flat_finrank_le (W : Submodule K (Fin 3 → K)) :
    finrank K W ≤ 3 := by
  have h := Submodule.finrank_le W
  have h3 : finrank K (Fin 3 → K) = 3 := by simp
  omega

theorem flat_rank_zero (W : Submodule K (Fin 3 → K))
    (h : finrank K W = 0) : W = ⊥ :=
  Submodule.finrank_eq_zero.mp h

theorem flat_rank_three (W : Submodule K (Fin 3 → K))
    (h : finrank K W = 3) : W = ⊤ :=
  Submodule.eq_top_of_finrank_eq (by simp [h])

theorem flat_rank_one (W : Submodule K (Fin 3 → K))
    (h : finrank K W = 1) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ W = Submodule.span K {v} := by
  let b := Module.finBasisOfFinrankEq K W h
  refine ⟨(b 0 : W).1, ?_, ?_⟩
  · intro h0
    exact b.ne_zero 0 (Subtype.ext h0)
  · have hr : Subtype.val '' Set.range b = {((b 0 : W) : Fin 3 → K)} := by
      rw [Set.range_unique]
      simp
    rw [← hr]
    exact (flat_span_basis_val W b).symm

theorem flat_rank_two (W : Submodule K (Fin 3 → K))
    (h : finrank K W = 2) :
    ∃ u v : Fin 3 → K, u ≠ 0 ∧ v ∉ Submodule.span K {u} ∧
      W = Submodule.span K {u, v} := by
  let b := Module.finBasisOfFinrankEq K W h
  have hr : Subtype.val '' Set.range b =
      {((b 0 : W) : Fin 3 → K), ((b 1 : W) : Fin 3 → K)} := by
    ext w
    simp [Fin.exists_fin_two, eq_comm]
  have hW : W = Submodule.span K
      {((b 0 : W) : Fin 3 → K), ((b 1 : W) : Fin 3 → K)} := by
    rw [← hr]
    exact (flat_span_basis_val W b).symm
  refine ⟨_, _, ?_, ?_, hW⟩
  · intro h0
    exact b.ne_zero 0 (Subtype.ext h0)
  · intro hmem
    have hle : Submodule.span K
        {((b 0 : W) : Fin 3 → K), ((b 1 : W) : Fin 3 → K)} ≤
        Submodule.span K {((b 0 : W) : Fin 3 → K)} := by
      rw [Submodule.span_le]
      rintro w (rfl | rfl)
      · exact Submodule.mem_span_singleton_self _
      · exact hmem
    have h1 : finrank K W ≤ 1 := by
      calc finrank K W = finrank K (Submodule.span K
            {((b 0 : W) : Fin 3 → K), ((b 1 : W) : Fin 3 → K)}) := by rw [← hW]
        _ ≤ finrank K (Submodule.span K {((b 0 : W) : Fin 3 → K)}) :=
            Submodule.finrank_mono hle
        _ ≤ 1 := by
            by_cases h0 : ((b 0 : W) : Fin 3 → K) = 0
            · rw [h0, Submodule.span_zero_singleton]
              simp
            · rw [finrank_span_singleton h0]
    omega

theorem flat_std_basis_span :
    Submodule.span K ({![1,0,0], ![0,1,0], ![0,0,1]} : Set (Fin 3 → K)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have h0 : (![1,0,0] : Fin 3 → K) ∈
      Submodule.span K ({![1,0,0], ![0,1,0], ![0,0,1]} : Set (Fin 3 → K)) :=
    Submodule.subset_span (by simp)
  have h1 : (![0,1,0] : Fin 3 → K) ∈
      Submodule.span K ({![1,0,0], ![0,1,0], ![0,0,1]} : Set (Fin 3 → K)) :=
    Submodule.subset_span (by simp)
  have h2 : (![0,0,1] : Fin 3 → K) ∈
      Submodule.span K ({![1,0,0], ![0,1,0], ![0,0,1]} : Set (Fin 3 → K)) :=
    Submodule.subset_span (by simp)
  have hv : v = v 0 • ![1,0,0] + v 1 • ![0,1,0] + v 2 • ![0,0,1] := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ h0) (Submodule.smul_mem _ _ h1))
    (Submodule.smul_mem _ _ h2)

end FlatLinear

/-! ## The lattice side: lines are covered by the plane, flats classified
by height -/

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

theorem CoordSystem.line_covBy_π (Γ : CoordSystem L) {p q : L}
    (hp : IsAtom p) (hq : IsAtom q) (hpq : p ≠ q)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hq_π : q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    p ⊔ q ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
  have hpq_π : p ⊔ q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := sup_le hp_π hq_π
  by_cases hm : p ⊔ q ≤ Γ.U ⊔ Γ.V
  · have h : p ⊔ q = Γ.U ⊔ Γ.V :=
      line_eq_of_two_atoms_le Γ.hU Γ.hV Γ.hUV hp hq hpq
        (le_sup_left.trans hm) (le_sup_right.trans hm)
    rw [h]
    exact Γ.m_covBy_π
  · have hS_atom : IsAtom ((p ⊔ q) ⊓ (Γ.U ⊔ Γ.V)) :=
      trace_atom hp hq hpq Γ.m_covBy_π hpq_π hm
    have hS_cov : (p ⊔ q) ⊓ (Γ.U ⊔ Γ.V) ⋖ Γ.U ⊔ Γ.V :=
      line_covers_its_atoms Γ.hU Γ.hV Γ.hUV hS_atom inf_le_right
    have hcov : p ⊔ q ⋖ (Γ.U ⊔ Γ.V) ⊔ (p ⊔ q) := by
      apply covBy_sup_of_inf_covBy_left
      rwa [inf_comm]
    have hr : ¬ p ≤ Γ.U ⊔ Γ.V ∨ ¬ q ≤ Γ.U ⊔ Γ.V := by
      by_cases hpm : p ≤ Γ.U ⊔ Γ.V
      · exact Or.inr (fun hqm => hm (sup_le hpm hqm))
      · exact Or.inl hpm
    have h_eq : (Γ.U ⊔ Γ.V) ⊔ (p ⊔ q) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
      apply le_antisymm (sup_le Γ.m_le_π hpq_π)
      rcases hr with h | h
      · have h_lt : Γ.U ⊔ Γ.V < (Γ.U ⊔ Γ.V) ⊔ p :=
          lt_of_le_of_ne le_sup_left (fun heq => h (heq ▸ le_sup_right))
        have h_top : (Γ.U ⊔ Γ.V) ⊔ p = Γ.O ⊔ Γ.U ⊔ Γ.V :=
          (Γ.m_covBy_π.eq_or_eq h_lt.le (sup_le Γ.m_le_π hp_π)).resolve_left
            (ne_of_gt h_lt)
        rw [← h_top]
        exact sup_le le_sup_left ((le_sup_left : p ≤ p ⊔ q).trans le_sup_right)
      · have h_lt : Γ.U ⊔ Γ.V < (Γ.U ⊔ Γ.V) ⊔ q :=
          lt_of_le_of_ne le_sup_left (fun heq => h (heq ▸ le_sup_right))
        have h_top : (Γ.U ⊔ Γ.V) ⊔ q = Γ.O ⊔ Γ.U ⊔ Γ.V :=
          (Γ.m_covBy_π.eq_or_eq h_lt.le (sup_le Γ.m_le_π hq_π)).resolve_left
            (ne_of_gt h_lt)
        rw [← h_top]
        exact sup_le le_sup_left ((le_sup_right : q ≤ p ⊔ q).trans le_sup_right)
    rwa [h_eq] at hcov

theorem CoordSystem.plane_flat_cases (Γ : CoordSystem L) {x : L}
    (hx_π : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    x = ⊥ ∨ IsAtom x ∨
    (∃ p q, IsAtom p ∧ IsAtom q ∧ p ≠ q ∧ x = p ⊔ q) ∨
    x = Γ.O ⊔ Γ.U ⊔ Γ.V := by
  obtain ⟨s, hs_lub, hs_atoms⟩ := IsAtomistic.isLUB_atoms x
  rcases Set.eq_empty_or_nonempty s with hs_e | ⟨p, hp_mem⟩
  · left
    rw [hs_e] at hs_lub
    exact hs_lub.unique isLUB_empty
  · have hp := hs_atoms p hp_mem
    have hp_le : p ≤ x := hs_lub.1 hp_mem
    by_cases hq_e : ∃ q ∈ s, q ≠ p
    · obtain ⟨q, hq_mem, hqp⟩ := hq_e
      have hq := hs_atoms q hq_mem
      have hq_le : q ≤ x := hs_lub.1 hq_mem
      by_cases hr_e : ∃ r ∈ s, ¬ r ≤ p ⊔ q
      · obtain ⟨r, hr_mem, hr_not⟩ := hr_e
        have hr_le : r ≤ x := hs_lub.1 hr_mem
        right; right; right
        have hline : p ⊔ q ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V :=
          Γ.line_covBy_π hp hq (Ne.symm hqp) (hp_le.trans hx_π)
            (hq_le.trans hx_π)
        have h_lt : p ⊔ q < (p ⊔ q) ⊔ r :=
          lt_of_le_of_ne le_sup_left (fun heq => hr_not (heq ▸ le_sup_right))
        have h_top : (p ⊔ q) ⊔ r = Γ.O ⊔ Γ.U ⊔ Γ.V :=
          (hline.eq_or_eq h_lt.le (sup_le (sup_le (hp_le.trans hx_π)
            (hq_le.trans hx_π)) (hr_le.trans hx_π))).resolve_left
            (ne_of_gt h_lt)
        apply le_antisymm hx_π
        rw [← h_top]
        exact sup_le (sup_le hp_le hq_le) hr_le
      · right; right; left
        refine ⟨p, q, hp, hq, Ne.symm hqp, le_antisymm ?_ (sup_le hp_le hq_le)⟩
        exact hs_lub.2 (fun t ht_mem => by
          by_contra ht
          exact hr_e ⟨t, ht_mem, ht⟩)
    · right; left
      have hs_eq : s = {p} := by
        ext t
        constructor
        · intro ht
          by_contra htp
          exact hq_e ⟨t, ht, htp⟩
        · intro ht
          rw [Set.mem_singleton_iff] at ht
          rw [ht]
          exact hp_mem
      rw [hs_eq] at hs_lub
      rw [hs_lub.unique isLUB_singleton]
      exact hp

/-! ## The frame vectors are the standard basis -/

theorem CoordSystem.hvec_U (Γ : CoordSystem L) :
    Γ.hvec Γ.U = ![1, 0, 0] := by
  have h : Γ.slopeC Γ.U = 0 := by
    apply Subtype.ext
    rw [Γ.slopeC_val Γ.hU le_sup_left Γ.hUV]
    exact Γ.slope_U
  rw [Γ.hvec_dir le_sup_left Γ.hUV, h, MulOpposite.op_zero]

theorem CoordSystem.hvec_O (Γ : CoordSystem L) :
    Γ.hvec Γ.O = ![0, 0, 1] := by
  have hO_π : Γ.O ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := le_sup_left.trans le_sup_left
  have hx : Γ.xcoordC Γ.O = 0 := by
    apply Subtype.ext
    rw [Γ.xcoordC_val Γ.hO hO_π Γ.hO_not_m]
    exact Γ.xproj_of_on_l Γ.hO le_sup_left Γ.hOU
  have hy : Γ.ycoordC Γ.O = 0 := by
    apply Subtype.ext
    rw [Γ.ycoordC_val Γ.hO hO_π Γ.hO_not_m]
    exact Γ.ycoord_of_on_l Γ.hO le_sup_left Γ.hOU
  rw [Γ.hvec_affine Γ.hO_not_m, hx, hy, MulOpposite.op_zero]

/-! ## The flat map: spans of coordinate vectors, evaluated at every height -/

noncomputable def CoordFrame.planeFlat (Φ : CoordFrame L) (x : L) :
    Submodule (Coordinate Φ.Γ)ᵐᵒᵖ (Fin 3 → (Coordinate Φ.Γ)ᵐᵒᵖ) :=
  Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ (Φ.Γ.hvec '' {p | IsAtom p ∧ p ≤ x})

theorem CoordFrame.planeFlat_bot (Φ : CoordFrame L) :
    Φ.planeFlat ⊥ = ⊥ := by
  unfold CoordFrame.planeFlat
  have h : {p : L | IsAtom p ∧ p ≤ ⊥} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hle
    exact hp.1 (le_bot_iff.mp hle)
  rw [h, Set.image_empty, Submodule.span_empty]

theorem CoordFrame.planeFlat_atom (Φ : CoordFrame L) {q : L} (hq : IsAtom q) :
    Φ.planeFlat q = Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {Φ.Γ.hvec q} := by
  unfold CoordFrame.planeFlat
  have h : {p : L | IsAtom p ∧ p ≤ q} = {q} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, hle⟩
      exact (hq.le_iff.mp hle).resolve_left hp.1
    · rintro rfl
      exact ⟨hq, le_rfl⟩
  rw [h, Set.image_singleton]

theorem CoordFrame.planeFlat_line (Φ : CoordFrame L) {p q : L}
    (hp : IsAtom p) (hp_π : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)
    (hq : IsAtom q) (hq_π : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) (hpq : p ≠ q) :
    Φ.planeFlat (p ⊔ q) =
      Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {Φ.Γ.hvec p, Φ.Γ.hvec q} := by
  apply le_antisymm
  · unfold CoordFrame.planeFlat
    rw [Submodule.span_le]
    rintro w ⟨t, ⟨ht, ht_le⟩, rfl⟩
    exact (Φ.plane_collinear_iff hp hp_π hq hq_π ht
      (ht_le.trans (sup_le hp_π hq_π)) hpq).mp ht_le
  · apply Submodule.span_mono
    rintro w (rfl | rfl)
    · exact ⟨p, ⟨hp, le_sup_left⟩, rfl⟩
    · exact ⟨q, ⟨hq, le_sup_right⟩, rfl⟩

theorem CoordFrame.planeFlat_π (Φ : CoordFrame L) :
    Φ.planeFlat (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) = ⊤ := by
  rw [eq_top_iff, ← flat_std_basis_span (K := (Coordinate Φ.Γ)ᵐᵒᵖ),
    Submodule.span_le]
  rintro w (rfl | rfl | rfl)
  · exact Submodule.subset_span
      ⟨Φ.Γ.U, ⟨Φ.Γ.hU, le_sup_right.trans le_sup_left⟩, Φ.Γ.hvec_U⟩
  · exact Submodule.subset_span ⟨Φ.Γ.V, ⟨Φ.Γ.hV, le_sup_right⟩, Φ.Γ.hvec_V⟩
  · exact Submodule.subset_span
      ⟨Φ.Γ.O, ⟨Φ.Γ.hO, le_sup_left.trans le_sup_left⟩, Φ.Γ.hvec_O⟩

/-! ## The order iso: le-iff both ways, surjectivity, the packaging -/

theorem CoordFrame.planeFlat_le_of_le (Φ : CoordFrame L) {x y : L}
    (hxy : x ≤ y) : Φ.planeFlat x ≤ Φ.planeFlat y :=
  Submodule.span_mono (Set.image_mono (fun _ hp => ⟨hp.1, hp.2.trans hxy⟩))

theorem CoordFrame.le_of_planeFlat_le (Φ : CoordFrame L) {x y : L}
    (hx_π : x ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) (hy_π : y ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)
    (h : Φ.planeFlat x ≤ Φ.planeFlat y) : x ≤ y := by
  have hatom : ∀ t, IsAtom t → t ≤ x → t ≤ y := by
    intro t ht ht_le
    have ht_π : t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V := ht_le.trans hx_π
    have hmem : Φ.Γ.hvec t ∈ Φ.planeFlat y :=
      h (Submodule.subset_span ⟨t, ⟨ht, ht_le⟩, rfl⟩)
    rcases Φ.Γ.plane_flat_cases hy_π with rfl | hy_atom |
      ⟨p, q, hp, hq, hpq, rfl⟩ | rfl
    · rw [Φ.planeFlat_bot] at hmem
      exact absurd (Submodule.mem_bot _ |>.mp hmem) (Φ.Γ.hvec_ne_zero t)
    · rw [Φ.planeFlat_atom hy_atom] at hmem
      by_cases hty : t = y
      · exact hty.le
      · exact absurd hmem
          (Φ.hvec_span_inj hy_atom hy_π ht ht_π (fun h' => hty h'.symm))
    · have hp_π : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V := le_sup_left.trans hy_π
      have hq_π : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V := le_sup_right.trans hy_π
      rw [Φ.planeFlat_line hp hp_π hq hq_π hpq] at hmem
      exact (Φ.plane_collinear_iff hp hp_π hq hq_π ht ht_π hpq).mpr hmem
    · exact ht_π
  obtain ⟨s, hs_lub, hs_atoms⟩ := IsAtomistic.isLUB_atoms x
  apply hs_lub.2
  intro t ht_mem
  exact hatom t (hs_atoms t ht_mem) (hs_lub.1 ht_mem)

theorem CoordFrame.planeFlat_surjective (Φ : CoordFrame L)
    (W : Submodule (Coordinate Φ.Γ)ᵐᵒᵖ (Fin 3 → (Coordinate Φ.Γ)ᵐᵒᵖ)) :
    ∃ x : L, x ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ∧ Φ.planeFlat x = W := by
  have hle : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W ≤ 3 := flat_finrank_le W
  by_cases h0 : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W = 0
  · exact ⟨⊥, bot_le, by rw [Φ.planeFlat_bot, flat_rank_zero W h0]⟩
  by_cases h1 : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W = 1
  · obtain ⟨v, hv, hW⟩ := flat_rank_one W h1
    obtain ⟨p, hp, hp_π, hspan⟩ := Φ.hvec_span_surj v hv
    exact ⟨p, hp_π, by rw [Φ.planeFlat_atom hp, hspan, hW]⟩
  by_cases h2 : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W = 2
  · obtain ⟨u, v, hu, hv_not, hW⟩ := flat_rank_two W h2
    have hv : v ≠ 0 := fun h => hv_not (h ▸ Submodule.zero_mem _)
    obtain ⟨p, hp, hp_π, hspan_p⟩ := Φ.hvec_span_surj u hu
    obtain ⟨q, hq, hq_π, hspan_q⟩ := Φ.hvec_span_surj v hv
    have hpq : p ≠ q := by
      rintro rfl
      apply hv_not
      have hmem : v ∈ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {v} :=
        Submodule.mem_span_singleton_self v
      rw [← hspan_q, hspan_p] at hmem
      exact hmem
    refine ⟨p ⊔ q, sup_le hp_π hq_π, ?_⟩
    rw [Φ.planeFlat_line hp hp_π hq hq_π hpq, hW, Submodule.span_insert,
      Submodule.span_insert, hspan_p, hspan_q]
  · have h3 : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W = 3 := by omega
    exact ⟨Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V, le_rfl,
      by rw [Φ.planeFlat_π, flat_rank_three W h3]⟩

theorem CoordFrame.plane_interval_iso (Φ : CoordFrame L) :
    Nonempty (Set.Iic (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) ≃o
      Submodule (Coordinate Φ.Γ)ᵐᵒᵖ (Fin 3 → (Coordinate Φ.Γ)ᵐᵒᵖ)) := by
  apply orderIso_of_mono_reflect_surj (fun x => Φ.planeFlat x.1)
  · intro a b hab
    exact Φ.planeFlat_le_of_le (Subtype.coe_le_coe.mpr hab)
  · intro a b hab
    exact Subtype.coe_le_coe.mp (Φ.le_of_planeFlat_le a.2 b.2 hab)
  · intro W
    obtain ⟨x, hx_π, hx⟩ := Φ.planeFlat_surjective W
    exact ⟨⟨x, hx_π⟩, hx⟩

end Foam.Bridges

/-- info: 'Foam.Bridges.flat_span_basis_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat_span_basis_val

/-- info: 'Foam.Bridges.flat_finrank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat_finrank_le

/-- info: 'Foam.Bridges.flat_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat_rank_zero

/-- info: 'Foam.Bridges.flat_rank_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat_rank_three

/-- info: 'Foam.Bridges.flat_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat_rank_one

/-- info: 'Foam.Bridges.flat_rank_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat_rank_two

/-- info: 'Foam.Bridges.flat_std_basis_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat_std_basis_span

/-- info: 'Foam.Bridges.CoordSystem.line_covBy_π' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.line_covBy_π

/-- info: 'Foam.Bridges.CoordSystem.plane_flat_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.plane_flat_cases

/-- info: 'Foam.Bridges.CoordSystem.hvec_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.hvec_U

/-- info: 'Foam.Bridges.CoordSystem.hvec_O' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.hvec_O

/-- info: 'Foam.Bridges.CoordFrame.planeFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.planeFlat

/-- info: 'Foam.Bridges.CoordFrame.planeFlat_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.planeFlat_bot

/-- info: 'Foam.Bridges.CoordFrame.planeFlat_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.planeFlat_atom

/-- info: 'Foam.Bridges.CoordFrame.planeFlat_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.planeFlat_line

/-- info: 'Foam.Bridges.CoordFrame.planeFlat_π' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.planeFlat_π

/-- info: 'Foam.Bridges.CoordFrame.planeFlat_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.planeFlat_le_of_le

/-- info: 'Foam.Bridges.CoordFrame.le_of_planeFlat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.le_of_planeFlat_le

/-- info: 'Foam.Bridges.CoordFrame.planeFlat_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.planeFlat_surjective

/-- info: 'Foam.Bridges.CoordFrame.plane_interval_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.plane_interval_iso
