import Bridges.FTPG.Solid
import Bridges.FTPG.Flat

/-!
# Camp three, sixth pitch: the space interval is the subspace lattice

`Solid.lean` put the *atoms* of the frame 3-space `τ = π ⊔ R` in bijection
with the projective points of `(Dᵐᵒᵖ)⁴`.  This file extends the bijection to
every element of the interval `[⊥, τ]`: the interval is order-isomorphic to
the full submodule lattice of `(Dᵐᵒᵖ)⁴`, heights 0/1/2/3/4 landing on
finranks 0/1/2/3/4.  No fresh Desargues, no new incidence — the sibling of
`Flat.lean` one dimension up.

* `three_atoms_ne_τ` — three atoms cannot span the 3-space: if they did, the
  line of two of them would be covered by `τ` while `π` is too, and the trace
  atom of `planes_meet_covBy` would be covered by `π` — impossible, since
  joining it with a frame atom sits strictly between (`line_covBy_π`).
* `flat_trace_pair` / `plane_trace_line` — a 3-atom span off `π` traces two
  *distinct* atoms on `π` (two lines through an off-`π` atom meet `π` by
  `line_meets_hyperplane`; a common trace would collapse the three atoms
  onto one line).
* `plane_covBy_τ` — the trace is therefore a line of `π`, covered by `π`
  (`line_covBy_π`), and one modular transport (`covBy_sup_of_inf_covBy_left`)
  carries the covering up the sup: every 3-atom span is covered by `τ`.
* `space_flat_cases` — the height classification: every `x ≤ τ` is `⊥`, an
  atom, a join of two atoms, a join of three (the third off the first two's
  line), or `τ` itself.
* `space_coplanar_iff` — an atom lies below a 3-atom span iff its coordinate
  vector lies in the span of the three coordinate vectors; forward by the
  two-lines-meet trace and `space_collinear_iff` twice, reverse by splitting
  the combination at the first vector, `hvec4_span_surj` on the tail, and
  `space_collinear_iff` twice.
* `flat4_rank_zero` … `flat4_rank_four` — submodules of `K⁴` classified by
  finrank, over any division ring.
* `spaceFlat` — the span of the coordinate vectors of the atoms below `x`,
  evaluated at every height (`hvec4_R` seats the fourth frame point at the
  third standard basis vector, completing the frame-is-the-standard-basis
  calibration).
* `space_interval_iso` — the summit: `Set.Iic τ ≃o Submodule Dᵐᵒᵖ (Dᵐᵒᵖ)⁴`,
  the `PointSystem` conclusion realized on the interval `[⊥, τ]`.
-/

namespace Foam.Bridges

universe u

/-! ## The abstract linear side: submodules of `K⁴` classified by finrank -/

section Flat4Linear

open Module

variable {K : Type*} [DivisionRing K]

theorem flat4_span_basis_val {n : ℕ} (W : Submodule K (Fin 4 → K))
    (b : Basis (Fin n) K W) :
    Submodule.span K (Subtype.val '' Set.range b) = W := by
  have h := congrArg (Submodule.map W.subtype) b.span_eq
  rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h

theorem flat4_finrank_le (W : Submodule K (Fin 4 → K)) :
    finrank K W ≤ 4 := by
  have h := Submodule.finrank_le W
  have h4 : finrank K (Fin 4 → K) = 4 := by simp
  omega

theorem flat4_rank_zero (W : Submodule K (Fin 4 → K))
    (h : finrank K W = 0) : W = ⊥ :=
  Submodule.finrank_eq_zero.mp h

theorem flat4_rank_four (W : Submodule K (Fin 4 → K))
    (h : finrank K W = 4) : W = ⊤ :=
  Submodule.eq_top_of_finrank_eq (by simp [h])

theorem flat4_rank_one (W : Submodule K (Fin 4 → K))
    (h : finrank K W = 1) :
    ∃ v : Fin 4 → K, v ≠ 0 ∧ W = Submodule.span K {v} := by
  let b := Module.finBasisOfFinrankEq K W h
  refine ⟨(b 0 : W).1, ?_, ?_⟩
  · intro h0
    exact b.ne_zero 0 (Subtype.ext h0)
  · have hr : Subtype.val '' Set.range b = {((b 0 : W) : Fin 4 → K)} := by
      rw [Set.range_unique]
      simp
    rw [← hr]
    exact (flat4_span_basis_val W b).symm

theorem span_pair_finrank_le {V : Type*} [AddCommGroup V] [Module K V]
    (u v : V) :
    finrank K (Submodule.span K ({u, v} : Set V)) ≤ 2 := by
  classical
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_insert, Set.toFinset_singleton]
  exact (Finset.card_insert_le _ _).trans (by simp)

theorem flat4_rank_two (W : Submodule K (Fin 4 → K))
    (h : finrank K W = 2) :
    ∃ u v : Fin 4 → K, u ≠ 0 ∧ v ∉ Submodule.span K {u} ∧
      W = Submodule.span K {u, v} := by
  let b := Module.finBasisOfFinrankEq K W h
  have hr : Subtype.val '' Set.range b =
      {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K)} := by
    ext w
    simp [Fin.exists_fin_two, eq_comm]
  have hW : W = Submodule.span K
      {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K)} := by
    rw [← hr]
    exact (flat4_span_basis_val W b).symm
  refine ⟨_, _, ?_, ?_, hW⟩
  · intro h0
    exact b.ne_zero 0 (Subtype.ext h0)
  · intro hmem
    have hle : Submodule.span K
        {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K)} ≤
        Submodule.span K {((b 0 : W) : Fin 4 → K)} := by
      rw [Submodule.span_le]
      rintro w (rfl | rfl)
      · exact Submodule.mem_span_singleton_self _
      · exact hmem
    have h1 : finrank K W ≤ 1 := by
      calc finrank K W = finrank K (Submodule.span K
            {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K)}) := by rw [← hW]
        _ ≤ finrank K (Submodule.span K {((b 0 : W) : Fin 4 → K)}) :=
            Submodule.finrank_mono hle
        _ ≤ 1 := by
            by_cases h0 : ((b 0 : W) : Fin 4 → K) = 0
            · rw [h0, Submodule.span_zero_singleton]
              simp
            · rw [finrank_span_singleton h0]
    omega

theorem flat4_rank_three (W : Submodule K (Fin 4 → K))
    (h : finrank K W = 3) :
    ∃ u v w : Fin 4 → K, u ≠ 0 ∧ v ∉ Submodule.span K {u} ∧
      w ∉ Submodule.span K {u, v} ∧ W = Submodule.span K {u, v, w} := by
  let b := Module.finBasisOfFinrankEq K W h
  have hr : Subtype.val '' Set.range b =
      {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K),
       ((b 2 : W) : Fin 4 → K)} := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨b 0, ⟨0, rfl⟩, rfl⟩
      · exact ⟨b 1, ⟨1, rfl⟩, rfl⟩
      · exact ⟨b 2, ⟨2, rfl⟩, rfl⟩
  have hW : W = Submodule.span K
      {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K),
       ((b 2 : W) : Fin 4 → K)} := by
    rw [← hr]
    exact (flat4_span_basis_val W b).symm
  refine ⟨_, _, _, ?_, ?_, ?_, hW⟩
  · intro h0
    exact b.ne_zero 0 (Subtype.ext h0)
  · intro hmem
    have hle : Submodule.span K
        {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K),
         ((b 2 : W) : Fin 4 → K)} ≤
        Submodule.span K {((b 0 : W) : Fin 4 → K), ((b 2 : W) : Fin 4 → K)} := by
      rw [Submodule.span_le]
      rintro x (rfl | rfl | rfl)
      · exact Submodule.subset_span (by simp)
      · exact Submodule.span_mono
          (Set.singleton_subset_iff.mpr (by simp)) hmem
      · exact Submodule.subset_span (by simp)
    have h2 : finrank K W ≤ 2 := by
      calc finrank K W = finrank K (Submodule.span K
            {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K),
             ((b 2 : W) : Fin 4 → K)}) := by rw [← hW]
        _ ≤ finrank K (Submodule.span K
              {((b 0 : W) : Fin 4 → K), ((b 2 : W) : Fin 4 → K)}) :=
            Submodule.finrank_mono hle
        _ ≤ 2 := span_pair_finrank_le _ _
    omega
  · intro hmem
    have hle : Submodule.span K
        {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K),
         ((b 2 : W) : Fin 4 → K)} ≤
        Submodule.span K {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K)} := by
      rw [Submodule.span_le]
      rintro x (rfl | rfl | rfl)
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
      · exact hmem
    have h2 : finrank K W ≤ 2 := by
      calc finrank K W = finrank K (Submodule.span K
            {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K),
             ((b 2 : W) : Fin 4 → K)}) := by rw [← hW]
        _ ≤ finrank K (Submodule.span K
              {((b 0 : W) : Fin 4 → K), ((b 1 : W) : Fin 4 → K)}) :=
            Submodule.finrank_mono hle
        _ ≤ 2 := span_pair_finrank_le _ _
    omega

theorem flat4_std_basis_span :
    Submodule.span K ({![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]} :
      Set (Fin 4 → K)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have h0 : (![1,0,0,0] : Fin 4 → K) ∈ Submodule.span K
      ({![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]} : Set (Fin 4 → K)) :=
    Submodule.subset_span (by simp)
  have h1 : (![0,1,0,0] : Fin 4 → K) ∈ Submodule.span K
      ({![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]} : Set (Fin 4 → K)) :=
    Submodule.subset_span (by simp)
  have h2 : (![0,0,1,0] : Fin 4 → K) ∈ Submodule.span K
      ({![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]} : Set (Fin 4 → K)) :=
    Submodule.subset_span (by simp)
  have h3 : (![0,0,0,1] : Fin 4 → K) ∈ Submodule.span K
      ({![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]} : Set (Fin 4 → K)) :=
    Submodule.subset_span (by simp)
  have hv : v = v 0 • (![1,0,0,0] : Fin 4 → K) + v 1 • (![0,1,0,0] : Fin 4 → K)
      + v 2 • (![0,0,1,0] : Fin 4 → K) + v 3 • (![0,0,0,1] : Fin 4 → K) := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ h0) (Submodule.smul_mem _ _ h1))
    (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3)

theorem span_triple_sup {V : Type*} [AddCommGroup V] [Module K V]
    (u v w : V) :
    Submodule.span K ({u, v, w} : Set V) =
      Submodule.span K {u} ⊔ Submodule.span K {v} ⊔ Submodule.span K {w} := by
  rw [Submodule.span_insert, Submodule.span_insert, sup_assoc]

end Flat4Linear

/-! ## The lattice side: three atoms never span the 3-space -/

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

variable {Γ : CoordSystem L} {R : L}

theorem CoordSystem.line_ne_π (Γ : CoordSystem L) {p q : L}
    (hp : IsAtom p) (hq : IsAtom q) (hpq : p ≠ q) :
    p ⊔ q ≠ Γ.O ⊔ Γ.U ⊔ Γ.V := by
  intro h
  have hU_le : Γ.U ≤ p ⊔ q :=
    le_of_le_of_eq (le_sup_right.trans le_sup_left) h.symm
  have hV_le : Γ.V ≤ p ⊔ q := le_of_le_of_eq le_sup_right h.symm
  have hm : Γ.U ⊔ Γ.V = p ⊔ q :=
    line_eq_of_two_atoms_le hp hq hpq Γ.hU Γ.hV Γ.hUV hU_le hV_le
  have hO_le : Γ.O ≤ p ⊔ q :=
    le_of_le_of_eq (le_sup_left.trans le_sup_left) h.symm
  exact Γ.hO_not_m (le_of_le_of_eq hO_le hm.symm)

theorem CoordSystem.three_atoms_ne_τ (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p q r : L}
    (hp : IsAtom p) (hq : IsAtom q) (hr : IsAtom r)
    (hpq : p ≠ q) (hr_line : ¬ r ≤ p ⊔ q) :
    p ⊔ q ⊔ r ≠ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R := by
  intro h
  have hpr : p ≠ r := fun h' => hr_line (h' ▸ le_sup_left)
  have hqr : q ≠ r := fun h' => hr_line (h' ▸ le_sup_right)
  have h_lcov : p ⊔ q ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
    h ▸ line_covBy_plane hp hq hr hpq hpr hqr hr_line
  obtain ⟨hS1, hS2⟩ := planes_meet_covBy h_lcov
    (CoordSystem.π_covBy_τ hR hR_π) (Γ.line_ne_π hp hq hpq)
  have hp_lt : p < p ⊔ q := lt_of_le_of_ne le_sup_left
    (fun h' => hpq (IsAtom.eq_of_le hq hp (h' ▸ le_sup_right)).symm)
  have hS_ne_bot : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) ≠ ⊥ := by
    intro h0
    rw [h0] at hS1
    exact hS1.2 hp.bot_lt hp_lt
  have hS_atom : IsAtom ((p ⊔ q) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V)) :=
    line_height_two hp hq hpq (bot_lt_iff_ne_bot.mpr hS_ne_bot) hS1.lt
  have key : ∀ a : L, IsAtom a → a ≤ Γ.O ⊔ Γ.U ⊔ Γ.V →
      (p ⊔ q) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) ≠ a → False := by
    intro a ha ha_π hSa
    have h_line := Γ.line_covBy_π hS_atom ha hSa inf_le_right ha_π
    have h_lt : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) <
        (p ⊔ q) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊔ a :=
      lt_of_le_of_ne le_sup_left
        (fun h' => hSa (IsAtom.eq_of_le ha hS_atom (h' ▸ le_sup_right)).symm)
    exact hS2.2 h_lt h_line.lt
  by_cases hSO : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = Γ.O
  · exact key Γ.U Γ.hU (le_sup_right.trans le_sup_left)
      (fun h' => Γ.hOU (hSO.symm.trans h'))
  · exact key Γ.O Γ.hO (le_sup_left.trans le_sup_left) hSO

/-! ## The trace of a 3-atom span on the frame plane is a line -/

theorem CoordSystem.flat_trace_pair (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {x a b₁ b₂ : L}
    (ha : IsAtom a) (hb₁ : IsAtom b₁) (hb₂ : IsAtom b₂)
    (ha_π : ¬ a ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hab₁ : a ≠ b₁) (hab₂ : a ≠ b₂)
    (ha_x : a ≤ x) (hb₁_x : b₁ ≤ x) (hb₂_x : b₂ ≤ x)
    (hx_τ : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (h_col : ¬ b₂ ≤ a ⊔ b₁) :
    ∃ s₁ s₂ : L, IsAtom s₁ ∧ IsAtom s₂ ∧ s₁ ≠ s₂ ∧
      s₁ ≤ x ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) ∧ s₂ ≤ x ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
  have hs₁_atom : IsAtom ((a ⊔ b₁) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V)) :=
    line_meets_hyperplane (CoordSystem.π_covBy_τ hR hR_π) ha hb₁ hab₁
      (sup_le (ha_x.trans hx_τ) (hb₁_x.trans hx_τ))
      (fun h => ha_π (le_sup_left.trans h))
  have hs₂_atom : IsAtom ((a ⊔ b₂) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V)) :=
    line_meets_hyperplane (CoordSystem.π_covBy_τ hR hR_π) ha hb₂ hab₂
      (sup_le (ha_x.trans hx_τ) (hb₂_x.trans hx_τ))
      (fun h => ha_π (le_sup_left.trans h))
  refine ⟨_, _, hs₁_atom, hs₂_atom, ?_,
    le_inf (inf_le_left.trans (sup_le ha_x hb₁_x)) inf_le_right,
    le_inf (inf_le_left.trans (sup_le ha_x hb₂_x)) inf_le_right⟩
  intro h_eq
  have hs₁_ne_a : (a ⊔ b₁) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) ≠ a :=
    fun h' => ha_π (h' ▸ inf_le_right)
  have hs₂_ne_a : (a ⊔ b₂) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) ≠ a :=
    fun h' => ha_π (h' ▸ inf_le_right)
  have h1 : a ⊔ (a ⊔ b₁) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = a ⊔ b₁ :=
    line_eq_of_two_atoms_le ha hb₁ hab₁ ha hs₁_atom (Ne.symm hs₁_ne_a)
      le_sup_left inf_le_left
  have h2 : a ⊔ (a ⊔ b₂) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = a ⊔ b₂ :=
    line_eq_of_two_atoms_le ha hb₂ hab₂ ha hs₂_atom (Ne.symm hs₂_ne_a)
      le_sup_left inf_le_left
  rw [← h_eq] at h2
  exact h_col (by rw [← h1, h2]; exact le_sup_right)

theorem CoordSystem.plane_trace_line (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p q r : L}
    (hp : IsAtom p) (hq : IsAtom q) (hr : IsAtom r)
    (hpq : p ≠ q) (hr_line : ¬ r ≤ p ⊔ q)
    (hp_τ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (hq_τ : q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R)
    (hr_τ : r ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) :
    ∃ s₁ s₂ : L, IsAtom s₁ ∧ IsAtom s₂ ∧ s₁ ≠ s₂ ∧
      s₁ ≤ (p ⊔ q ⊔ r) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) ∧
      s₂ ≤ (p ⊔ q ⊔ r) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
  have hpr : p ≠ r := fun h' => hr_line (h' ▸ le_sup_left)
  have hqr : q ≠ r := fun h' => hr_line (h' ▸ le_sup_right)
  have hp_x : p ≤ p ⊔ q ⊔ r := le_sup_left.trans le_sup_left
  have hq_x : q ≤ p ⊔ q ⊔ r := le_sup_right.trans le_sup_left
  have hr_x : r ≤ p ⊔ q ⊔ r := le_sup_right
  have hx_τ : p ⊔ q ⊔ r ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
    sup_le (sup_le hp_τ hq_τ) hr_τ
  by_cases hpπ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V
  · by_cases hqπ : q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V
    · exact ⟨p, q, hp, hq, hpq, le_inf hp_x hpπ, le_inf hq_x hqπ⟩
    · by_cases hrπ : r ≤ Γ.O ⊔ Γ.U ⊔ Γ.V
      · exact ⟨p, r, hp, hr, hpr, le_inf hp_x hpπ, le_inf hr_x hrπ⟩
      · exact CoordSystem.flat_trace_pair hR hR_π hq hp hr hqπ
          (Ne.symm hpq) hqr hq_x hp_x hr_x hx_τ
          (fun h => hr_line (by rwa [sup_comm q p] at h))
  · exact CoordSystem.flat_trace_pair hR hR_π hp hq hr hpπ hpq hpr
      hp_x hq_x hr_x hx_τ hr_line

/-! ## Every 3-atom span is covered by the 3-space -/

theorem CoordSystem.plane_covBy_τ (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p q r : L}
    (hp : IsAtom p) (hq : IsAtom q) (hr : IsAtom r)
    (hpq : p ≠ q) (hr_line : ¬ r ≤ p ⊔ q)
    (hp_τ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (hq_τ : q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R)
    (hr_τ : r ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) :
    p ⊔ q ⊔ r ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R := by
  have hx_τ : p ⊔ q ⊔ r ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
    sup_le (sup_le hp_τ hq_τ) hr_τ
  by_cases hPπ : p ⊔ q ⊔ r ≤ Γ.O ⊔ Γ.U ⊔ Γ.V
  · have h_lcov : p ⊔ q ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V :=
      Γ.line_covBy_π hp hq hpq ((le_sup_left.trans le_sup_left).trans hPπ)
        ((le_sup_right.trans le_sup_left).trans hPπ)
    have h_lt : p ⊔ q < p ⊔ q ⊔ r := lt_of_le_of_ne le_sup_left
      (fun h' => hr_line (h' ▸ le_sup_right))
    have h_eq : p ⊔ q ⊔ r = Γ.O ⊔ Γ.U ⊔ Γ.V :=
      (h_lcov.eq_or_eq le_sup_left hPπ).resolve_left (ne_of_gt h_lt)
    rw [h_eq]
    exact CoordSystem.π_covBy_τ hR hR_π
  · have hπP : ¬ Γ.O ⊔ Γ.U ⊔ Γ.V ≤ p ⊔ q ⊔ r := by
      intro h
      have h_lt : Γ.O ⊔ Γ.U ⊔ Γ.V < p ⊔ q ⊔ r :=
        lt_of_le_of_ne h (fun h' => hPπ (le_of_eq h'.symm))
      have h_top : p ⊔ q ⊔ r = Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
        ((CoordSystem.π_covBy_τ hR hR_π).eq_or_eq h hx_τ).resolve_left
          (ne_of_gt h_lt)
      exact CoordSystem.three_atoms_ne_τ hR hR_π hp hq hr hpq hr_line h_top
    obtain ⟨s₁, s₂, hs₁, hs₂, hs₁₂, hs₁_le, hs₂_le⟩ :=
      CoordSystem.plane_trace_line hR hR_π hp hq hr hpq hr_line
        hp_τ hq_τ hr_τ
    have h_line_cov : s₁ ⊔ s₂ ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V :=
      Γ.line_covBy_π hs₁ hs₂ hs₁₂ (hs₁_le.trans inf_le_right)
        (hs₂_le.trans inf_le_right)
    have hT_ne_π : (p ⊔ q ⊔ r) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) ≠ Γ.O ⊔ Γ.U ⊔ Γ.V :=
      fun h' => hπP (h' ▸ inf_le_left)
    have hT_eq : (p ⊔ q ⊔ r) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = s₁ ⊔ s₂ :=
      (h_line_cov.eq_or_eq (sup_le hs₁_le hs₂_le) inf_le_right).resolve_right
        hT_ne_π
    have hT_cov : (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊓ (p ⊔ q ⊔ r) ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
      rw [inf_comm, hT_eq]
      exact h_line_cov
    have h_cov := covBy_sup_of_inf_covBy_left hT_cov
    have h_lt : Γ.O ⊔ Γ.U ⊔ Γ.V < (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊔ (p ⊔ q ⊔ r) :=
      lt_of_le_of_ne le_sup_left
        (fun h' => hPπ (le_of_le_of_eq le_sup_right h'.symm))
    have h_join : (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊔ (p ⊔ q ⊔ r) = Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
      ((CoordSystem.π_covBy_τ hR hR_π).eq_or_eq h_lt.le
        (sup_le le_sup_left hx_τ)).resolve_left (ne_of_gt h_lt)
    rwa [h_join] at h_cov

/-! ## The height classification of the interval `[⊥, τ]` -/

theorem CoordSystem.space_flat_cases (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {x : L}
    (hx_τ : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) :
    x = ⊥ ∨ IsAtom x ∨
    (∃ p q, IsAtom p ∧ IsAtom q ∧ p ≠ q ∧ x = p ⊔ q) ∨
    (∃ p q r, IsAtom p ∧ IsAtom q ∧ IsAtom r ∧ p ≠ q ∧ ¬ r ≤ p ⊔ q ∧
      x = p ⊔ q ⊔ r) ∨
    x = Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R := by
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
        have hr := hs_atoms r hr_mem
        have hr_le : r ≤ x := hs_lub.1 hr_mem
        by_cases hw_e : ∃ w ∈ s, ¬ w ≤ p ⊔ q ⊔ r
        · obtain ⟨w, hw_mem, hw_not⟩ := hw_e
          have hw_le : w ≤ x := hs_lub.1 hw_mem
          right; right; right; right
          have h_pcov : p ⊔ q ⊔ r ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
            CoordSystem.plane_covBy_τ hR hR_π hp hq hr (Ne.symm hqp) hr_not
              (hp_le.trans hx_τ) (hq_le.trans hx_τ) (hr_le.trans hx_τ)
          have h_lt : p ⊔ q ⊔ r < p ⊔ q ⊔ r ⊔ w :=
            lt_of_le_of_ne le_sup_left
              (fun heq => hw_not (heq ▸ le_sup_right))
          have h_top : p ⊔ q ⊔ r ⊔ w = Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
            (h_pcov.eq_or_eq h_lt.le (sup_le (sup_le (sup_le
              (hp_le.trans hx_τ) (hq_le.trans hx_τ)) (hr_le.trans hx_τ))
              (hw_le.trans hx_τ))).resolve_left (ne_of_gt h_lt)
          apply le_antisymm hx_τ
          rw [← h_top]
          exact sup_le (sup_le (sup_le hp_le hq_le) hr_le) hw_le
        · right; right; right; left
          refine ⟨p, q, r, hp, hq, hr, Ne.symm hqp, hr_not,
            le_antisymm ?_ (sup_le (sup_le hp_le hq_le) hr_le)⟩
          exact hs_lub.2 (fun t ht_mem => by
            by_contra ht
            exact hw_e ⟨t, ht_mem, ht⟩)
      · right; right; left
        refine ⟨p, q, hp, hq, Ne.symm hqp,
          le_antisymm ?_ (sup_le hp_le hq_le)⟩
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

/-! ## The fourth frame vector: `R` sits at the third standard basis slot -/

open MulOpposite

theorem CoordSystem.hvec4_R (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R) :
    Γ.hvec4 R c R = ![0, 0, 1, 0] := by
  obtain ⟨hw_atom, _, hw_σ, _, _⟩ := CoordSystem.wpt_facts hR hR_π hc
    hc_UR hc_U hc_R hR le_sup_right (CoordSystem.hR_not_m hR_π)
  have hw_ne_R : Γ.wpt R c R ≠ R :=
    fun h => hw_σ (le_of_eq_of_le h le_sup_right)
  have hO_ne_R : Γ.O ≠ R :=
    CoordSystem.ne_R_of_le_π hR_π (le_sup_left.trans le_sup_left)
  have hw_le : Γ.wpt R c R ≤ Γ.O ⊔ R := inf_le_left
  have h_line : Γ.wpt R c R ⊔ R = Γ.O ⊔ R :=
    line_eq_of_two_atoms_le Γ.hO hR hO_ne_R hw_atom hR hw_ne_R hw_le
      le_sup_right
  have h_base : Γ.baseproj R (Γ.wpt R c R) = Γ.O := by
    show (Γ.wpt R c R ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = Γ.O
    rw [h_line]
    exact CoordSystem.ζ_inf_π hR hR_π
  rw [Γ.hvec4_inf R c le_sup_right (CoordSystem.hR_not_m hR_π), h_base,
    Γ.xcoordC_O, Γ.ycoordC_O]
  funext i
  fin_cases i <;> simp

/-! ## Coplanarity is span membership -/

theorem CoordFrame.space_coplanar_iff (Φ : CoordFrame L) {c : L}
    (hc : IsAtom c) (hc_UR : c ≤ Φ.Γ.U ⊔ Φ.R) (hc_U : c ≠ Φ.Γ.U) (hc_R : c ≠ Φ.R)
    {p q r t : L} (hp : IsAtom p) (hp_τ : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (hq : IsAtom q) (hq_τ : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (hr : IsAtom r) (hr_τ : r ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (ht : IsAtom t) (ht_τ : t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (hpq : p ≠ q) (hr_line : ¬ r ≤ p ⊔ q) :
    t ≤ p ⊔ q ⊔ r ↔ Φ.Γ.hvec4 Φ.R c t ∈ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
      {Φ.Γ.hvec4 Φ.R c p, Φ.Γ.hvec4 Φ.R c q, Φ.Γ.hvec4 Φ.R c r} := by
  have hpr : p ≠ r := fun h' => hr_line (h' ▸ le_sup_left)
  have hqr : q ≠ r := fun h' => hr_line (h' ▸ le_sup_right)
  have h_pair_sub : ({Φ.Γ.hvec4 Φ.R c p, Φ.Γ.hvec4 Φ.R c q} :
      Set (Fin 4 → (Coordinate Φ.Γ)ᵐᵒᵖ)) ⊆
      {Φ.Γ.hvec4 Φ.R c p, Φ.Γ.hvec4 Φ.R c q, Φ.Γ.hvec4 Φ.R c r} := by
    rintro y (rfl | rfl)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  constructor
  · intro ht_P
    by_cases ht_line : t ≤ p ⊔ q
    · exact Submodule.span_mono h_pair_sub
        ((Φ.space_collinear_iff hc hc_UR hc_U hc_R hp hp_τ hq hq_τ
          ht ht_τ hpq).mp ht_line)
    · by_cases htr : t = r
      · exact htr ▸ Submodule.subset_span
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
      · have h_pcov : p ⊔ q ⋖ p ⊔ q ⊔ r :=
          line_covBy_plane hp hq hr hpq hpr hqr hr_line
        have h_tr_not : ¬ t ⊔ r ≤ p ⊔ q :=
          fun h => hr_line (le_sup_right.trans h)
        have h_meet_ne : (p ⊔ q) ⊓ (t ⊔ r) ≠ ⊥ :=
          lines_meet_if_coplanar h_pcov (sup_le ht_P le_sup_right) h_tr_not
            ht (lt_of_le_of_ne le_sup_left (fun h' =>
              htr (IsAtom.eq_of_le hr ht (h' ▸ le_sup_right)).symm))
        have h_pq_not : ¬ p ⊔ q ≤ t ⊔ r := by
          intro h
          apply hr_line
          rw [line_eq_of_two_atoms_le ht hr htr hp hq hpq
            (le_sup_left.trans h) (le_sup_right.trans h)]
          exact le_sup_right
        have hs_atom : IsAtom ((p ⊔ q) ⊓ (t ⊔ r)) :=
          meet_of_lines_is_atom hp hq ht hr hpq htr h_pq_not h_meet_ne
        have hs_pq : (p ⊔ q) ⊓ (t ⊔ r) ≤ p ⊔ q := inf_le_left
        have hs_τ : (p ⊔ q) ⊓ (t ⊔ r) ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R :=
          hs_pq.trans (sup_le hp_τ hq_τ)
        have hs_ne_r : (p ⊔ q) ⊓ (t ⊔ r) ≠ r :=
          fun h' => hr_line (h' ▸ hs_pq)
        have h_rs : r ⊔ (p ⊔ q) ⊓ (t ⊔ r) = t ⊔ r :=
          line_eq_of_two_atoms_le ht hr htr hr hs_atom (Ne.symm hs_ne_r)
            le_sup_right inf_le_right
        have ht_rs : t ≤ r ⊔ (p ⊔ q) ⊓ (t ⊔ r) :=
          le_of_le_of_eq le_sup_left h_rs.symm
        have hmem_t := (Φ.space_collinear_iff hc hc_UR hc_U hc_R hr hr_τ
          hs_atom hs_τ ht ht_τ (Ne.symm hs_ne_r)).mp ht_rs
        have hmem_s := (Φ.space_collinear_iff hc hc_UR hc_U hc_R hp hp_τ
          hq hq_τ hs_atom hs_τ hpq).mp hs_pq
        have h_incl : Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
            {Φ.Γ.hvec4 Φ.R c r, Φ.Γ.hvec4 Φ.R c ((p ⊔ q) ⊓ (t ⊔ r))} ≤
            Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
              {Φ.Γ.hvec4 Φ.R c p, Φ.Γ.hvec4 Φ.R c q, Φ.Γ.hvec4 Φ.R c r} := by
          rw [Submodule.span_le]
          rintro y (rfl | rfl)
          · exact Submodule.subset_span
              (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
          · exact Submodule.span_mono h_pair_sub hmem_s
        exact h_incl hmem_t
  · intro hmem
    rw [Submodule.mem_span_insert] at hmem
    obtain ⟨a, u, hu, ht_eq⟩ := hmem
    by_cases hu0 : u = 0
    · have hmem_p : Φ.Γ.hvec4 Φ.R c t ∈ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
          {Φ.Γ.hvec4 Φ.R c p} := by
        rw [ht_eq, hu0, add_zero]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      by_cases htp : t = p
      · exact htp.le.trans (le_sup_left.trans le_sup_left)
      · exact absurd hmem_p (Φ.hvec4_span_inj hc hc_UR hc_U hc_R hp hp_τ
          ht ht_τ (fun h' => htp h'.symm))
    · obtain ⟨s, hs, hs_τ, hspan⟩ :=
        Φ.hvec4_span_surj hc hc_UR hc_U hc_R u hu0
      have hu_le : Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {u} ≤
          Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
            {Φ.Γ.hvec4 Φ.R c q, Φ.Γ.hvec4 Φ.R c r} :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr hu
      have hs_mem_u : Φ.Γ.hvec4 Φ.R c s ∈
          Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {u} :=
        hspan ▸ Submodule.mem_span_singleton_self _
      have hqr' : q ≠ r := hqr
      have hs_qr : s ≤ q ⊔ r :=
        (Φ.space_collinear_iff hc hc_UR hc_U hc_R hq hq_τ hr hr_τ
          hs hs_τ hqr').mpr (hu_le hs_mem_u)
      have hu_mem_s : u ∈ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
          {Φ.Γ.hvec4 Φ.R c s} :=
        hspan.symm ▸ Submodule.mem_span_singleton_self u
      by_cases hps : p = s
      · have hmem_p : Φ.Γ.hvec4 Φ.R c t ∈ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
            {Φ.Γ.hvec4 Φ.R c p} := by
          rw [ht_eq]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
            (hps ▸ hu_mem_s)
        by_cases htp : t = p
        · exact htp.le.trans (le_sup_left.trans le_sup_left)
        · exact absurd hmem_p (Φ.hvec4_span_inj hc hc_UR hc_U hc_R hp hp_τ
            ht ht_τ (fun h' => htp h'.symm))
      · obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hu_mem_s
        have ht_ps : Φ.Γ.hvec4 Φ.R c t ∈ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
            {Φ.Γ.hvec4 Φ.R c p, Φ.Γ.hvec4 Φ.R c s} := by
          rw [ht_eq, ← he]
          exact Submodule.mem_span_pair.mpr ⟨a, e, rfl⟩
        have ht_le : t ≤ p ⊔ s :=
          (Φ.space_collinear_iff hc hc_UR hc_U hc_R hp hp_τ hs hs_τ
            ht ht_τ hps).mpr ht_ps
        exact ht_le.trans (sup_le (le_sup_left.trans le_sup_left)
          (hs_qr.trans (sup_le (le_sup_right.trans le_sup_left)
            le_sup_right)))

/-! ## The flat map: spans of coordinate vectors, evaluated at every height -/

noncomputable def CoordFrame.spaceFlat (Φ : CoordFrame L) (c x : L) :
    Submodule (Coordinate Φ.Γ)ᵐᵒᵖ (Fin 4 → (Coordinate Φ.Γ)ᵐᵒᵖ) :=
  Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
    (Φ.Γ.hvec4 Φ.R c '' {p | IsAtom p ∧ p ≤ x})

theorem CoordFrame.spaceFlat_bot (Φ : CoordFrame L) (c : L) :
    Φ.spaceFlat c ⊥ = ⊥ := by
  unfold CoordFrame.spaceFlat
  have h : {p : L | IsAtom p ∧ p ≤ ⊥} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hle
    exact hp.1 (le_bot_iff.mp hle)
  rw [h, Set.image_empty, Submodule.span_empty]

theorem CoordFrame.spaceFlat_atom (Φ : CoordFrame L) (c : L) {q : L}
    (hq : IsAtom q) :
    Φ.spaceFlat c q =
      Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {Φ.Γ.hvec4 Φ.R c q} := by
  unfold CoordFrame.spaceFlat
  have h : {p : L | IsAtom p ∧ p ≤ q} = {q} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, hle⟩
      exact (hq.le_iff.mp hle).resolve_left hp.1
    · rintro rfl
      exact ⟨hq, le_rfl⟩
  rw [h, Set.image_singleton]

theorem CoordFrame.spaceFlat_line (Φ : CoordFrame L) {c : L}
    (hc : IsAtom c) (hc_UR : c ≤ Φ.Γ.U ⊔ Φ.R) (hc_U : c ≠ Φ.Γ.U) (hc_R : c ≠ Φ.R)
    {p q : L} (hp : IsAtom p) (hp_τ : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (hq : IsAtom q) (hq_τ : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R) (hpq : p ≠ q) :
    Φ.spaceFlat c (p ⊔ q) = Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
      {Φ.Γ.hvec4 Φ.R c p, Φ.Γ.hvec4 Φ.R c q} := by
  apply le_antisymm
  · unfold CoordFrame.spaceFlat
    rw [Submodule.span_le]
    rintro w ⟨t, ⟨ht, ht_le⟩, rfl⟩
    exact (Φ.space_collinear_iff hc hc_UR hc_U hc_R hp hp_τ hq hq_τ ht
      (ht_le.trans (sup_le hp_τ hq_τ)) hpq).mp ht_le
  · apply Submodule.span_mono
    rintro w (rfl | rfl)
    · exact ⟨p, ⟨hp, le_sup_left⟩, rfl⟩
    · exact ⟨q, ⟨hq, le_sup_right⟩, rfl⟩

theorem CoordFrame.spaceFlat_plane (Φ : CoordFrame L) {c : L}
    (hc : IsAtom c) (hc_UR : c ≤ Φ.Γ.U ⊔ Φ.R) (hc_U : c ≠ Φ.Γ.U) (hc_R : c ≠ Φ.R)
    {p q r : L} (hp : IsAtom p) (hp_τ : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (hq : IsAtom q) (hq_τ : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (hr : IsAtom r) (hr_τ : r ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (hpq : p ≠ q) (hr_line : ¬ r ≤ p ⊔ q) :
    Φ.spaceFlat c (p ⊔ q ⊔ r) = Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
      {Φ.Γ.hvec4 Φ.R c p, Φ.Γ.hvec4 Φ.R c q, Φ.Γ.hvec4 Φ.R c r} := by
  apply le_antisymm
  · unfold CoordFrame.spaceFlat
    rw [Submodule.span_le]
    rintro w ⟨t, ⟨ht, ht_le⟩, rfl⟩
    exact (Φ.space_coplanar_iff hc hc_UR hc_U hc_R hp hp_τ hq hq_τ hr hr_τ
      ht (ht_le.trans (sup_le (sup_le hp_τ hq_τ) hr_τ)) hpq hr_line).mp ht_le
  · apply Submodule.span_mono
    rintro w (rfl | rfl | rfl)
    · exact ⟨p, ⟨hp, le_sup_left.trans le_sup_left⟩, rfl⟩
    · exact ⟨q, ⟨hq, le_sup_right.trans le_sup_left⟩, rfl⟩
    · exact ⟨r, ⟨hr, le_sup_right⟩, rfl⟩

theorem CoordFrame.spaceFlat_τ (Φ : CoordFrame L) {c : L}
    (hc : IsAtom c) (hc_UR : c ≤ Φ.Γ.U ⊔ Φ.R) (hc_U : c ≠ Φ.Γ.U)
    (hc_R : c ≠ Φ.R) :
    Φ.spaceFlat c (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R) = ⊤ := by
  rw [eq_top_iff, ← flat4_std_basis_span (K := (Coordinate Φ.Γ)ᵐᵒᵖ),
    Submodule.span_le]
  have hU_π : Φ.Γ.U ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V := le_sup_right.trans le_sup_left
  have hO_π : Φ.Γ.O ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V := le_sup_left.trans le_sup_left
  rintro w (rfl | rfl | rfl | rfl)
  · refine Submodule.subset_span
      ⟨Φ.Γ.U, ⟨Φ.Γ.hU, hU_π.trans le_sup_left⟩, ?_⟩
    rw [Φ.hvec4_π hc hc_UR hc_U hU_π, Φ.Γ.hvec_U]
    funext i
    fin_cases i <;> rfl
  · exact Submodule.subset_span
      ⟨Φ.Γ.V, ⟨Φ.Γ.hV, le_sup_right.trans le_sup_left⟩, Φ.Γ.hvec4_V Φ.R c⟩
  · exact Submodule.subset_span ⟨Φ.R, ⟨Φ.hR_atom, le_sup_right⟩,
      CoordSystem.hvec4_R Φ.hR_atom Φ.hR_not hc hc_UR hc_U hc_R⟩
  · refine Submodule.subset_span
      ⟨Φ.Γ.O, ⟨Φ.Γ.hO, hO_π.trans le_sup_left⟩, ?_⟩
    rw [Φ.hvec4_π hc hc_UR hc_U hO_π, Φ.Γ.hvec_O]
    funext i
    fin_cases i <;> rfl

/-! ## The order iso: le-iff both ways, surjectivity, the packaging -/

theorem CoordFrame.spaceFlat_le_of_le (Φ : CoordFrame L) (c : L) {x y : L}
    (hxy : x ≤ y) : Φ.spaceFlat c x ≤ Φ.spaceFlat c y :=
  Submodule.span_mono (Set.image_mono (fun _ hp => ⟨hp.1, hp.2.trans hxy⟩))

theorem CoordFrame.le_of_spaceFlat_le (Φ : CoordFrame L) {c : L}
    (hc : IsAtom c) (hc_UR : c ≤ Φ.Γ.U ⊔ Φ.R) (hc_U : c ≠ Φ.Γ.U) (hc_R : c ≠ Φ.R)
    {x y : L} (hx_τ : x ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (hy_τ : y ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R)
    (h : Φ.spaceFlat c x ≤ Φ.spaceFlat c y) : x ≤ y := by
  have hatom : ∀ t, IsAtom t → t ≤ x → t ≤ y := by
    intro t ht ht_le
    have ht_τ : t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := ht_le.trans hx_τ
    have hmem : Φ.Γ.hvec4 Φ.R c t ∈ Φ.spaceFlat c y :=
      h (Submodule.subset_span ⟨t, ⟨ht, ht_le⟩, rfl⟩)
    rcases CoordSystem.space_flat_cases Φ.hR_atom Φ.hR_not hy_τ with
      rfl | hy_atom | ⟨p, q, hp, hq, hpq, rfl⟩ |
      ⟨p, q, r, hp, hq, hr, hpq, hr_line, rfl⟩ | rfl
    · rw [Φ.spaceFlat_bot] at hmem
      exact absurd (Submodule.mem_bot _ |>.mp hmem)
        (Φ.Γ.hvec4_ne_zero Φ.R c t)
    · rw [Φ.spaceFlat_atom c hy_atom] at hmem
      by_cases hty : t = y
      · exact hty.le
      · exact absurd hmem (Φ.hvec4_span_inj hc hc_UR hc_U hc_R hy_atom hy_τ
          ht ht_τ (fun h' => hty h'.symm))
    · have hp_τ : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := le_sup_left.trans hy_τ
      have hq_τ : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := le_sup_right.trans hy_τ
      rw [Φ.spaceFlat_line hc hc_UR hc_U hc_R hp hp_τ hq hq_τ hpq] at hmem
      exact (Φ.space_collinear_iff hc hc_UR hc_U hc_R hp hp_τ hq hq_τ
        ht ht_τ hpq).mpr hmem
    · have hp_τ : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R :=
        (le_sup_left.trans le_sup_left).trans hy_τ
      have hq_τ : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R :=
        (le_sup_right.trans le_sup_left).trans hy_τ
      have hr_τ : r ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R := le_sup_right.trans hy_τ
      rw [Φ.spaceFlat_plane hc hc_UR hc_U hc_R hp hp_τ hq hq_τ hr hr_τ
        hpq hr_line] at hmem
      exact (Φ.space_coplanar_iff hc hc_UR hc_U hc_R hp hp_τ hq hq_τ
        hr hr_τ ht ht_τ hpq hr_line).mpr hmem
    · exact ht_τ
  obtain ⟨s, hs_lub, hs_atoms⟩ := IsAtomistic.isLUB_atoms x
  apply hs_lub.2
  intro t ht_mem
  exact hatom t (hs_atoms t ht_mem) (hs_lub.1 ht_mem)

theorem CoordFrame.spaceFlat_surjective (Φ : CoordFrame L) {c : L}
    (hc : IsAtom c) (hc_UR : c ≤ Φ.Γ.U ⊔ Φ.R) (hc_U : c ≠ Φ.Γ.U) (hc_R : c ≠ Φ.R)
    (W : Submodule (Coordinate Φ.Γ)ᵐᵒᵖ (Fin 4 → (Coordinate Φ.Γ)ᵐᵒᵖ)) :
    ∃ x : L, x ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R ∧ Φ.spaceFlat c x = W := by
  have hle : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W ≤ 4 := flat4_finrank_le W
  by_cases h0 : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W = 0
  · exact ⟨⊥, bot_le, by rw [Φ.spaceFlat_bot, flat4_rank_zero W h0]⟩
  by_cases h1 : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W = 1
  · obtain ⟨v, hv, hW⟩ := flat4_rank_one W h1
    obtain ⟨p, hp, hp_τ, hspan⟩ := Φ.hvec4_span_surj hc hc_UR hc_U hc_R v hv
    exact ⟨p, hp_τ, by rw [Φ.spaceFlat_atom c hp, hspan, hW]⟩
  by_cases h2 : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W = 2
  · obtain ⟨u, v, hu, hv_not, hW⟩ := flat4_rank_two W h2
    have hv : v ≠ 0 := fun h => hv_not (h ▸ Submodule.zero_mem _)
    obtain ⟨p, hp, hp_τ, hspan_p⟩ := Φ.hvec4_span_surj hc hc_UR hc_U hc_R u hu
    obtain ⟨q, hq, hq_τ, hspan_q⟩ := Φ.hvec4_span_surj hc hc_UR hc_U hc_R v hv
    have hpq : p ≠ q := by
      rintro rfl
      apply hv_not
      have hmem : v ∈ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {v} :=
        Submodule.mem_span_singleton_self v
      rw [← hspan_q, hspan_p] at hmem
      exact hmem
    refine ⟨p ⊔ q, sup_le hp_τ hq_τ, ?_⟩
    rw [Φ.spaceFlat_line hc hc_UR hc_U hc_R hp hp_τ hq hq_τ hpq, hW,
      Submodule.span_insert, Submodule.span_insert, hspan_p, hspan_q]
  by_cases h3 : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W = 3
  · obtain ⟨u, v, w, hu, hv_not, hw_not, hW⟩ := flat4_rank_three W h3
    have hv : v ≠ 0 := fun h => hv_not (h ▸ Submodule.zero_mem _)
    have hw : w ≠ 0 := fun h => hw_not (h ▸ Submodule.zero_mem _)
    obtain ⟨p, hp, hp_τ, hspan_p⟩ := Φ.hvec4_span_surj hc hc_UR hc_U hc_R u hu
    obtain ⟨q, hq, hq_τ, hspan_q⟩ := Φ.hvec4_span_surj hc hc_UR hc_U hc_R v hv
    obtain ⟨r, hr, hr_τ, hspan_r⟩ := Φ.hvec4_span_surj hc hc_UR hc_U hc_R w hw
    have hpq : p ≠ q := by
      rintro rfl
      apply hv_not
      have hmem : v ∈ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {v} :=
        Submodule.mem_span_singleton_self v
      rw [← hspan_q, hspan_p] at hmem
      exact hmem
    have hr_line : ¬ r ≤ p ⊔ q := by
      intro hle'
      apply hw_not
      have hmem := (Φ.space_collinear_iff hc hc_UR hc_U hc_R hp hp_τ
        hq hq_τ hr hr_τ hpq).mp hle'
      have h_r_le : Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
          {Φ.Γ.hvec4 Φ.R c r} ≤ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
            {Φ.Γ.hvec4 Φ.R c p, Φ.Γ.hvec4 Φ.R c q} :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
      have hw_mem : w ∈ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ
          {Φ.Γ.hvec4 Φ.R c r} :=
        hspan_r.symm ▸ Submodule.mem_span_singleton_self w
      have := h_r_le hw_mem
      rwa [Submodule.span_insert, hspan_p, hspan_q,
        ← Submodule.span_insert] at this
    refine ⟨p ⊔ q ⊔ r, sup_le (sup_le hp_τ hq_τ) hr_τ, ?_⟩
    rw [Φ.spaceFlat_plane hc hc_UR hc_U hc_R hp hp_τ hq hq_τ hr hr_τ
      hpq hr_line, hW, span_triple_sup, span_triple_sup, hspan_p, hspan_q,
      hspan_r]
  · have h4 : Module.finrank (Coordinate Φ.Γ)ᵐᵒᵖ W = 4 := by omega
    exact ⟨Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R, le_rfl,
      by rw [Φ.spaceFlat_τ hc hc_UR hc_U hc_R, flat4_rank_four W h4]⟩

theorem CoordFrame.space_interval_iso (Φ : CoordFrame L) :
    Nonempty (Set.Iic (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R) ≃o
      Submodule (Coordinate Φ.Γ)ᵐᵒᵖ (Fin 4 → (Coordinate Φ.Γ)ᵐᵒᵖ)) := by
  obtain ⟨c, hc, hc_UR, hc_U, hc_R⟩ := Φ.h_irred Φ.Γ.U Φ.R Φ.Γ.hU Φ.hR_atom
    (CoordSystem.hU_ne_R Φ.hR_not)
  apply orderIso_of_mono_reflect_surj (fun x => Φ.spaceFlat c x.1)
  · intro a b hab
    exact Φ.spaceFlat_le_of_le c (Subtype.coe_le_coe.mpr hab)
  · intro a b hab
    exact Subtype.coe_le_coe.mp
      (Φ.le_of_spaceFlat_le hc hc_UR hc_U hc_R a.2 b.2 hab)
  · intro W
    obtain ⟨x, hx_τ, hx⟩ := Φ.spaceFlat_surjective hc hc_UR hc_U hc_R W
    exact ⟨⟨x, hx_τ⟩, hx⟩

end Foam.Bridges

/-- info: 'Foam.Bridges.flat4_span_basis_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat4_span_basis_val

/-- info: 'Foam.Bridges.flat4_finrank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat4_finrank_le

/-- info: 'Foam.Bridges.flat4_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat4_rank_zero

/-- info: 'Foam.Bridges.flat4_rank_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat4_rank_four

/-- info: 'Foam.Bridges.flat4_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat4_rank_one

/-- info: 'Foam.Bridges.span_pair_finrank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.span_pair_finrank_le

/-- info: 'Foam.Bridges.flat4_rank_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat4_rank_two

/-- info: 'Foam.Bridges.flat4_rank_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat4_rank_three

/-- info: 'Foam.Bridges.flat4_std_basis_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.flat4_std_basis_span

/-- info: 'Foam.Bridges.span_triple_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.span_triple_sup

/-- info: 'Foam.Bridges.CoordSystem.line_ne_π' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.line_ne_π

/-- info: 'Foam.Bridges.CoordSystem.three_atoms_ne_τ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.three_atoms_ne_τ

/-- info: 'Foam.Bridges.CoordSystem.flat_trace_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.flat_trace_pair

/-- info: 'Foam.Bridges.CoordSystem.plane_trace_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.plane_trace_line

/-- info: 'Foam.Bridges.CoordSystem.plane_covBy_τ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.plane_covBy_τ

/-- info: 'Foam.Bridges.CoordSystem.space_flat_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.space_flat_cases

/-- info: 'Foam.Bridges.CoordSystem.hvec4_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.hvec4_R

/-- info: 'Foam.Bridges.CoordFrame.space_coplanar_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.space_coplanar_iff

/-- info: 'Foam.Bridges.CoordFrame.spaceFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.spaceFlat

/-- info: 'Foam.Bridges.CoordFrame.spaceFlat_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.spaceFlat_bot

/-- info: 'Foam.Bridges.CoordFrame.spaceFlat_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.spaceFlat_atom

/-- info: 'Foam.Bridges.CoordFrame.spaceFlat_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.spaceFlat_line

/-- info: 'Foam.Bridges.CoordFrame.spaceFlat_plane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.spaceFlat_plane

/-- info: 'Foam.Bridges.CoordFrame.spaceFlat_τ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.spaceFlat_τ

/-- info: 'Foam.Bridges.CoordFrame.spaceFlat_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.spaceFlat_le_of_le

/-- info: 'Foam.Bridges.CoordFrame.le_of_spaceFlat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.le_of_spaceFlat_le

/-- info: 'Foam.Bridges.CoordFrame.spaceFlat_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.spaceFlat_surjective

/-- info: 'Foam.Bridges.CoordFrame.space_interval_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.space_interval_iso
