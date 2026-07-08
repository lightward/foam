import Bridges.FTPG.SpaceFlat

/-!
# Camp four, first pitch: the rank ladder's step

The generic Veblen–Young induction step, frame-free: an abstract division ring
`K`, a flat `x` carrying a point system into `K^n` (`n ≥ 3`), and one off-flat
witness atom `w` yield a point system at `x ⊔ w` into `K^(n+1)`, extending the
old coordinates by a zero slot.

The engine is the central shear lemma: every secondary center reads the same
height through a gauge constant, pinned by the bridge trace and the flat's own
span laws — no fresh Desargues, no new incidence.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## The induction datum: a point system at a flat -/

structure PointSys (x : L) (n : ℕ) (K : Type*) [DivisionRing K] where
  hv : L → Fin n → K
  ne_zero : ∀ {p : L}, IsAtom p → p ≤ x → hv p ≠ 0
  span_inj : ∀ {p q : L}, IsAtom p → p ≤ x → IsAtom q → q ≤ x → p ≠ q →
    hv q ∉ Submodule.span K {hv p}
  span_surj : ∀ v : Fin n → K, v ≠ 0 → ∃ p : L, IsAtom p ∧ p ≤ x ∧
    Submodule.span K {hv p} = Submodule.span K {v}
  collinear_iff : ∀ {p q r : L}, IsAtom p → p ≤ x → IsAtom q → q ≤ x →
    IsAtom r → r ≤ x → p ≠ q →
    (r ≤ p ⊔ q ↔ hv r ∈ Submodule.span K {hv p, hv q})

/-! ## The lattice stratum: traces, centers, recovery, the shadow line -/

section LadderLattice

variable {x w : L}

omit [ComplementedLattice L] in
theorem ladder_trace_atom (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {c t : L} (hc : IsAtom c) (hc_le : c ≤ x ⊔ w)
    (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (htc : t ≠ c) :
    IsAtom (project c t x) :=
  line_meets_hyperplane (covBy_sup_atom hw hwx) ht hc htc
    (sup_le ht_le hc_le) (fun h => htx (le_trans le_sup_left h))

omit [ComplementedLattice L] in
theorem ladder_regen (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {c t : L} (hc : IsAtom c) (hc_le : c ≤ x ⊔ w) (hcx : ¬ c ≤ x)
    (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (htc : t ≠ c) :
    t ⊔ c = project c t x ⊔ c ∧ t ≤ project c t x ⊔ c := by
  have hs_atom : IsAtom (project c t x) :=
    ladder_trace_atom hw hwx hc hc_le ht ht_le htx htc
  have hs_le_line : project c t x ≤ t ⊔ c := inf_le_left
  have hs_x : project c t x ≤ x := inf_le_right
  have hcs : c ≠ project c t x := fun h => hcx (h ▸ hs_x)
  have hts : t ≠ project c t x := fun h => htx (h ▸ hs_x)
  have h1 : c ⊔ t = c ⊔ project c t x :=
    line_eq_of_atom_le hc ht hs_atom (Ne.symm htc) hcs hts
      (by rw [sup_comm]; exact hs_le_line)
  have h2 : t ⊔ c = project c t x ⊔ c := by
    rw [sup_comm t c, sup_comm (project c t x) c]; exact h1
  exact ⟨h2, h2 ▸ (le_sup_left : t ≤ t ⊔ c)⟩

omit [ComplementedLattice L] [IsAtomistic L] in
theorem ladder_wline_trace (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {b : L} (hbx : b ≤ x) : (b ⊔ w) ⊓ x = b := by
  rw [sup_inf_assoc_of_le w hbx, inf_eq_bot_of_atom_not_le hw hwx, sup_bot_eq]

omit [ComplementedLattice L] in
theorem ladder_base_iff (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {t u₀ : L} (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (htw : t ≠ w)
    (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x) :
    project w t x = u₀ ↔ t ≤ u₀ ⊔ w := by
  constructor
  · intro h
    have h1 := (ladder_regen hw hwx hw le_sup_right hwx ht ht_le htx htw).2
    rwa [h] at h1
  · intro h
    have h1 : project w t x ≤ u₀ := by
      have h2 : (t ⊔ w) ⊓ x ≤ (u₀ ⊔ w) ⊓ x :=
        inf_le_inf_right x (sup_le h le_sup_right)
      rwa [ladder_wline_trace hw hwx hu₀x] at h2
    exact IsAtom.eq_of_le
      (ladder_trace_atom hw hwx hw le_sup_right ht ht_le htx htw) hu₀ h1

omit [ComplementedLattice L] in
theorem ladder_center (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {u₀ c₀ : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hc₀ : IsAtom c₀) (hc₀_le : c₀ ≤ u₀ ⊔ w) (hc₀u : c₀ ≠ u₀) (hc₀w : c₀ ≠ w) :
    ¬ c₀ ≤ x ∧ c₀ ≤ x ⊔ w ∧ u₀ ⊔ c₀ = u₀ ⊔ w ∧ c₀ ⊔ w = u₀ ⊔ w ∧
      project w c₀ x = u₀ := by
  have hu₀w : u₀ ≠ w := fun h => hwx (h ▸ hu₀x)
  have h1 : u₀ ⊔ w = u₀ ⊔ c₀ :=
    line_eq_of_atom_le hu₀ hw hc₀ hu₀w (Ne.symm hc₀u) (Ne.symm hc₀w) hc₀_le
  have h2 : w ⊔ u₀ = w ⊔ c₀ :=
    line_eq_of_atom_le hw hu₀ hc₀ (Ne.symm hu₀w) (Ne.symm hc₀w) (Ne.symm hc₀u)
      (by rw [sup_comm]; exact hc₀_le)
  have hc₀x : ¬ c₀ ≤ x := by
    intro h
    apply hwx
    have h3 : u₀ ⊔ w ≤ x := by rw [h1]; exact sup_le hu₀x h
    exact le_sup_right.trans h3
  have hc₀_xw : c₀ ≤ x ⊔ w :=
    hc₀_le.trans (sup_le (hu₀x.trans le_sup_left) le_sup_right)
  have h4 : c₀ ⊔ w = u₀ ⊔ w := by
    rw [sup_comm c₀ w, ← h2, sup_comm w u₀]
  refine ⟨hc₀x, hc₀_xw, h1.symm, h4, ?_⟩
  exact (ladder_base_iff hw hwx hc₀ hc₀_xw hc₀x hc₀w hu₀ hu₀x).mpr hc₀_le

omit [ComplementedLattice L] [IsAtomistic L] in
theorem ladder_axis_inf (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {u₀ u₁ : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hu₁ : IsAtom u₁) (hu₁x : u₁ ≤ x) (hne : u₀ ≠ u₁) :
    (u₀ ⊔ w) ⊓ (u₁ ⊔ w) = w := by
  have hu₀w : w ≠ u₀ := fun h => hwx (h ▸ hu₀x)
  have hcov : w ⋖ w ⊔ u₀ := atom_covBy_join hw hu₀ hu₀w
  have hle : w ≤ (u₀ ⊔ w) ⊓ (u₁ ⊔ w) := le_inf le_sup_right le_sup_right
  have hle2 : (u₀ ⊔ w) ⊓ (u₁ ⊔ w) ≤ w ⊔ u₀ := by
    rw [sup_comm w u₀]; exact inf_le_left
  rcases hcov.eq_or_eq hle hle2 with h | h
  · exact h
  · exfalso
    have h1 : u₀ ≤ u₁ ⊔ w :=
      le_sup_right.trans ((h ▸ inf_le_right : w ⊔ u₀ ≤ u₁ ⊔ w))
    have h2 : u₀ ≤ u₁ := by
      have h3 : u₀ ≤ (u₁ ⊔ w) ⊓ x := le_inf h1 hu₀x
      rwa [ladder_wline_trace hw hwx hu₁x] at h3
    exact hne (IsAtom.eq_of_le hu₀ hu₁ h2)

omit [ComplementedLattice L] [IsAtomistic L] in
theorem ladder_line_trace {s c₀ : L} (hs_x : s ≤ x)
    (hc₀ : IsAtom c₀) (hc₀x : ¬ c₀ ≤ x) :
    (s ⊔ c₀) ⊓ x = s := by
  rw [sup_inf_assoc_of_le c₀ hs_x, inf_eq_bot_of_atom_not_le hc₀ hc₀x,
    sup_bot_eq]

omit [ComplementedLattice L] in
theorem ladder_shear_le (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {u₀ c₀ t : L} (hu₀x : u₀ ≤ x) (hc₀_le : c₀ ≤ u₀ ⊔ w)
    (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (htw : t ≠ w) :
    project c₀ t x ≤ project w t x ⊔ u₀ := by
  have hb_x : project w t x ≤ x := inf_le_right
  have ht_line : t ≤ project w t x ⊔ w :=
    (ladder_regen hw hwx hw le_sup_right hwx ht ht_le htx htw).2
  have h1 : t ⊔ c₀ ≤ (project w t x ⊔ u₀) ⊔ w := by
    refine sup_le (ht_line.trans ?_) (hc₀_le.trans ?_)
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have h2 : project c₀ t x ≤ ((project w t x ⊔ u₀) ⊔ w) ⊓ x :=
    le_inf (inf_le_left.trans h1) inf_le_right
  rwa [sup_inf_assoc_of_le w (sup_le hb_x hu₀x),
    inf_eq_bot_of_atom_not_le hw hwx, sup_bot_eq] at h2

omit [ComplementedLattice L] in
theorem ladder_shear_ne_axis (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {u₀ c₀ t : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hc₀ : IsAtom c₀) (hc₀_le : c₀ ≤ u₀ ⊔ w) (hc₀u : c₀ ≠ u₀) (hc₀w : c₀ ≠ w)
    (ht : IsAtom t) (htu₀w : ¬ t ≤ u₀ ⊔ w) :
    project c₀ t x ≠ u₀ := by
  obtain ⟨hc₀x, hc₀_xw, hline, hline', hbase⟩ :=
    ladder_center hw hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
  intro h
  have htc₀ : t ≠ c₀ := fun heq => htu₀w (heq ▸ hc₀_le)
  have hu₀_le : u₀ ≤ c₀ ⊔ t := by
    rw [sup_comm]; exact h ▸ inf_le_left
  have h1 : c₀ ⊔ t = c₀ ⊔ u₀ :=
    line_eq_of_atom_le hc₀ ht hu₀ (Ne.symm htc₀) hc₀u
      (fun heq => htu₀w (heq.le.trans le_sup_left)) hu₀_le
  apply htu₀w
  calc t ≤ c₀ ⊔ t := le_sup_right
    _ = c₀ ⊔ u₀ := h1
    _ = u₀ ⊔ c₀ := sup_comm _ _
    _ = u₀ ⊔ w := hline

omit [ComplementedLattice L] in
theorem ladder_shear_ne_base (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {u₀ c₀ t : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hc₀ : IsAtom c₀) (hc₀_le : c₀ ≤ u₀ ⊔ w) (hc₀u : c₀ ≠ u₀) (hc₀w : c₀ ≠ w)
    (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (htw : t ≠ w)
    (htu₀w : ¬ t ≤ u₀ ⊔ w) :
    project c₀ t x ≠ project w t x := by
  obtain ⟨hc₀x, hc₀_xw, hline, hline', hbase⟩ :=
    ladder_center hw hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
  set b := project w t x with hb_def
  have hb_atom : IsAtom b :=
    ladder_trace_atom hw hwx hw le_sup_right ht ht_le htx htw
  have hb_x : b ≤ x := inf_le_right
  have hbu₀ : b ≠ u₀ := fun h =>
    htu₀w ((ladder_base_iff hw hwx ht ht_le htx htw hu₀ hu₀x).mp h)
  have htc₀ : t ≠ c₀ := fun heq => htu₀w (heq ▸ hc₀_le)
  intro h
  have hb_le : b ≤ t ⊔ c₀ := h ▸ inf_le_left
  have hbc₀ : c₀ ≠ b := fun heq => hc₀x (heq ▸ hb_x)
  have h1 : c₀ ⊔ t = c₀ ⊔ b :=
    line_eq_of_atom_le hc₀ ht hb_atom (Ne.symm htc₀) hbc₀
      (fun heq => htx (heq ▸ hb_x)) (by rw [sup_comm]; exact hb_le)
  have ht_bc₀ : t ≤ b ⊔ c₀ := by
    rw [sup_comm b c₀, ← h1]; exact le_sup_right
  have ht_bw : t ≤ b ⊔ w :=
    (ladder_regen hw hwx hw le_sup_right hwx ht ht_le htx htw).2
  have hbw : b ≠ w := fun heq => hwx (heq ▸ hb_x)
  have hcov : b ⋖ b ⊔ w := atom_covBy_join hb_atom hw hbw
  have hb_le_meet : b ≤ (b ⊔ w) ⊓ (b ⊔ c₀) := le_inf le_sup_left le_sup_left
  rcases hcov.eq_or_eq hb_le_meet inf_le_left with hmeq | hmeq
  · have h2 : t ≤ b := hmeq ▸ le_inf ht_bw ht_bc₀
    exact htx (h2.trans hb_x)
  · have hw_le : w ≤ b ⊔ c₀ :=
      le_sup_right.trans (hmeq ▸ inf_le_right : (b ⊔ w : L) ≤ b ⊔ c₀)
    have h2 : b ⊔ c₀ = b ⊔ w :=
      line_eq_of_atom_le hb_atom hc₀ hw hbc₀.symm hbw hc₀w hw_le
    have hc₀_bw : c₀ ≤ b ⊔ w := h2 ▸ le_sup_right
    have h3 : c₀ ≤ w := by
      have h4 := le_inf hc₀_bw hc₀_le
      rwa [ladder_axis_inf hw hwx hb_atom hb_x hu₀ hu₀x hbu₀] at h4
    exact hc₀w (IsAtom.eq_of_le hc₀ hw h3)

omit [ComplementedLattice L] in
theorem ladder_recover (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {u₀ c₀ t : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hc₀ : IsAtom c₀) (hc₀_le : c₀ ≤ u₀ ⊔ w) (hc₀u : c₀ ≠ u₀) (hc₀w : c₀ ≠ w)
    (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (htw : t ≠ w)
    (htu₀w : ¬ t ≤ u₀ ⊔ w) :
    (project w t x ⊔ w) ⊓ (project c₀ t x ⊔ c₀) = t := by
  obtain ⟨hc₀x, hc₀_xw, hline, hline', hbase⟩ :=
    ladder_center hw hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
  set b := project w t x with hb_def
  set s := project c₀ t x with hs_def
  have htc₀ : t ≠ c₀ := fun heq => htu₀w (heq ▸ hc₀_le)
  have hb_atom : IsAtom b :=
    ladder_trace_atom hw hwx hw le_sup_right ht ht_le htx htw
  have hs_atom : IsAtom s :=
    ladder_trace_atom hw hwx hc₀ hc₀_xw ht ht_le htx htc₀
  have hb_x : b ≤ x := inf_le_right
  have hs_x : s ≤ x := inf_le_right
  have hs_u₀ : s ≠ u₀ :=
    ladder_shear_ne_axis hw hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w ht htu₀w
  have hbw : b ≠ w := fun heq => hwx (heq ▸ hb_x)
  have hsc₀ : s ≠ c₀ := fun heq => hc₀x (heq ▸ hs_x)
  have hsw : s ≠ w := fun heq => hwx (heq ▸ hs_x)
  have ht_bw : t ≤ b ⊔ w :=
    (ladder_regen hw hwx hw le_sup_right hwx ht ht_le htx htw).2
  have ht_sc₀ : t ≤ s ⊔ c₀ :=
    (ladder_regen hw hwx hc₀ hc₀_xw hc₀x ht ht_le htx htc₀).2
  have h_not_le : ¬ b ⊔ w ≤ s ⊔ c₀ := by
    intro hle
    have hw_le : w ≤ c₀ ⊔ s := by rw [sup_comm]; exact le_sup_right.trans hle
    have h1 : c₀ ⊔ s = c₀ ⊔ w :=
      line_eq_of_atom_le hc₀ hs_atom hw hsc₀.symm hc₀w hsw hw_le
    have h2 : s ≤ u₀ ⊔ w := by
      calc s ≤ c₀ ⊔ s := le_sup_right
        _ = c₀ ⊔ w := h1
        _ = u₀ ⊔ w := hline'
    have h3 : s ≤ u₀ := by
      have h4 : s ≤ (u₀ ⊔ w) ⊓ x := le_inf h2 hs_x
      rwa [ladder_wline_trace hw hwx hu₀x] at h4
    exact hs_u₀ (IsAtom.eq_of_le hs_atom hu₀ h3)
  have h_meet_ne : (b ⊔ w) ⊓ (s ⊔ c₀) ≠ ⊥ := by
    intro h
    have h1 : t ≤ ⊥ := h ▸ le_inf ht_bw ht_sc₀
    exact ht.1 (le_bot_iff.mp h1)
  have h_meet_atom : IsAtom ((b ⊔ w) ⊓ (s ⊔ c₀)) :=
    meet_of_lines_is_atom hb_atom hw hs_atom hc₀ hbw hsc₀ h_not_le h_meet_ne
  exact (IsAtom.eq_of_le ht h_meet_atom (le_inf ht_bw ht_sc₀)).symm

omit [ComplementedLattice L] in
theorem ladder_bridge (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {u₀ u₁ c₀ c₁ : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hu₁ : IsAtom u₁) (hu₁x : u₁ ≤ x) (hne : u₀ ≠ u₁)
    (hc₀ : IsAtom c₀) (hc₀_le : c₀ ≤ u₀ ⊔ w) (hc₀u : c₀ ≠ u₀) (hc₀w : c₀ ≠ w)
    (hc₁ : IsAtom c₁) (hc₁_le : c₁ ≤ u₁ ⊔ w) (hc₁u : c₁ ≠ u₁) (hc₁w : c₁ ≠ w) :
    c₀ ≠ c₁ ∧ IsAtom (project c₀ c₁ x) ∧ project c₀ c₁ x ≤ u₀ ⊔ u₁ ∧
      project c₀ c₁ x ≠ u₀ ∧ project c₀ c₁ x ≠ u₁ := by
  obtain ⟨hc₀x, hc₀_xw, hline₀, hline₀', hbase₀⟩ :=
    ladder_center hw hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
  obtain ⟨hc₁x, hc₁_xw, hline₁, hline₁', hbase₁⟩ :=
    ladder_center hw hwx hu₁ hu₁x hc₁ hc₁_le hc₁u hc₁w
  have hc₀c₁ : c₀ ≠ c₁ := by
    intro h
    have h1 : c₀ ≤ w := by
      have h2 := le_inf hc₀_le (h ▸ hc₁_le)
      rwa [ladder_axis_inf hw hwx hu₀ hu₀x hu₁ hu₁x hne] at h2
    exact hc₀w (IsAtom.eq_of_le hc₀ hw h1)
  have hd_atom : IsAtom (project c₀ c₁ x) :=
    ladder_trace_atom hw hwx hc₀ hc₀_xw hc₁ hc₁_xw hc₁x (Ne.symm hc₀c₁)
  have hd_le : project c₀ c₁ x ≤ u₀ ⊔ u₁ := by
    have h1 : c₁ ⊔ c₀ ≤ (u₁ ⊔ u₀) ⊔ w := by
      refine sup_le (hc₁_le.trans ?_) (hc₀_le.trans ?_)
      · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
      · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
    have h2 : project c₀ c₁ x ≤ ((u₁ ⊔ u₀) ⊔ w) ⊓ x :=
      le_inf (inf_le_left.trans h1) inf_le_right
    rw [sup_inf_assoc_of_le w (sup_le hu₁x hu₀x),
      inf_eq_bot_of_atom_not_le hw hwx, sup_bot_eq] at h2
    rwa [sup_comm u₁ u₀] at h2
  have hd_x : project c₀ c₁ x ≤ x := inf_le_right
  refine ⟨hc₀c₁, hd_atom, hd_le, ?_, ?_⟩
  · intro h
    have h1 : u₀ ≤ c₀ ⊔ c₁ := by
      rw [sup_comm]; exact h ▸ inf_le_left
    have h2 : c₀ ⊔ c₁ = c₀ ⊔ u₀ :=
      line_eq_of_atom_le hc₀ hc₁ hu₀ hc₀c₁ hc₀u
        (fun heq => hc₁x (heq ▸ hu₀x)) h1
    have h3 : c₁ ≤ u₀ ⊔ w := by
      calc c₁ ≤ c₀ ⊔ c₁ := le_sup_right
        _ = c₀ ⊔ u₀ := h2
        _ = u₀ ⊔ c₀ := sup_comm _ _
        _ = u₀ ⊔ w := hline₀
    have h4 : c₁ ≤ w := by
      have h5 := le_inf h3 hc₁_le
      rwa [ladder_axis_inf hw hwx hu₀ hu₀x hu₁ hu₁x hne] at h5
    exact hc₁w (IsAtom.eq_of_le hc₁ hw h4)
  · intro h
    have h1 : u₁ ≤ c₁ ⊔ c₀ := h ▸ inf_le_left
    have h2 : c₁ ⊔ c₀ = c₁ ⊔ u₁ :=
      line_eq_of_atom_le hc₁ hc₀ hu₁ (Ne.symm hc₀c₁) hc₁u
        (fun heq => hc₀x (heq ▸ hu₁x)) h1
    have h3 : c₀ ≤ u₁ ⊔ w := by
      calc c₀ ≤ c₁ ⊔ c₀ := le_sup_right
        _ = c₁ ⊔ u₁ := h2
        _ = u₁ ⊔ c₁ := sup_comm _ _
        _ = u₁ ⊔ w := hline₁
    have h4 : c₀ ≤ w := by
      have h5 := le_inf hc₀_le h3
      rwa [ladder_axis_inf hw hwx hu₀ hu₀x hu₁ hu₁x hne] at h5
    exact hc₀w (IsAtom.eq_of_le hc₀ hw h4)

omit [ComplementedLattice L] in
theorem ladder_shadow (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {u₀ u₁ c₀ c₁ t : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hu₁ : IsAtom u₁) (hu₁x : u₁ ≤ x) (hne : u₀ ≠ u₁)
    (hc₀ : IsAtom c₀) (hc₀_le : c₀ ≤ u₀ ⊔ w) (hc₀u : c₀ ≠ u₀) (hc₀w : c₀ ≠ w)
    (hc₁ : IsAtom c₁) (hc₁_le : c₁ ≤ u₁ ⊔ w) (hc₁u : c₁ ≠ u₁) (hc₁w : c₁ ≠ w)
    (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (_htw : t ≠ w)
    (htu₀w : ¬ t ≤ u₀ ⊔ w) :
    project c₁ t x ≤ project c₀ t x ⊔ project c₀ c₁ x := by
  obtain ⟨hc₀x, hc₀_xw, hline₀, hline₀', hbase₀⟩ :=
    ladder_center hw hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
  obtain ⟨hc₁x, hc₁_xw, hline₁, hline₁', hbase₁⟩ :=
    ladder_center hw hwx hu₁ hu₁x hc₁ hc₁_le hc₁u hc₁w
  obtain ⟨hc₀c₁, hd_atom, hd_le, hd_u₀, hd_u₁⟩ :=
    ladder_bridge hw hwx hu₀ hu₀x hu₁ hu₁x hne hc₀ hc₀_le hc₀u hc₀w
      hc₁ hc₁_le hc₁u hc₁w
  set s₀ := project c₀ t x with hs₀_def
  set d := project c₀ c₁ x with hd_def
  have hs₀x : s₀ ≤ x := inf_le_right
  have hdx : d ≤ x := inf_le_right
  have htc₀ : t ≠ c₀ := fun heq => htu₀w (heq ▸ hc₀_le)
  have ht_s₀c₀ : t ≤ s₀ ⊔ c₀ :=
    (ladder_regen hw hwx hc₀ hc₀_xw hc₀x ht ht_le htx htc₀).2
  have hd_c₀ : d ≠ c₀ := fun heq => hc₀x (heq ▸ hdx)
  have hd_line : d ≤ c₀ ⊔ c₁ := by rw [sup_comm]; exact inf_le_left
  have h1 : c₀ ⊔ c₁ = c₀ ⊔ d :=
    line_eq_of_atom_le hc₀ hc₁ hd_atom hc₀c₁ (Ne.symm hd_c₀)
      (fun heq : c₁ = d => hc₁x (heq ▸ hdx)) hd_line
  have hc₁_le_dc₀ : c₁ ≤ d ⊔ c₀ := by
    rw [sup_comm d c₀, ← h1]; exact le_sup_right
  have h2 : t ⊔ c₁ ≤ (s₀ ⊔ d) ⊔ c₀ := by
    refine sup_le (ht_s₀c₀.trans ?_) (hc₁_le_dc₀.trans ?_)
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have h3 : project c₁ t x ≤ ((s₀ ⊔ d) ⊔ c₀) ⊓ x :=
    le_inf (inf_le_left.trans h2) inf_le_right
  rwa [sup_inf_assoc_of_le c₀ (sup_le hs₀x hdx),
    inf_eq_bot_of_atom_not_le hc₀ hc₀x, sup_bot_eq] at h3

omit [ComplementedLattice L] in
theorem ladder_reverse (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {u₀ c₀ b s : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hc₀ : IsAtom c₀) (hc₀_le : c₀ ≤ u₀ ⊔ w) (hc₀u : c₀ ≠ u₀) (hc₀w : c₀ ≠ w)
    (hb : IsAtom b) (hbx : b ≤ x) (hbu₀ : b ≠ u₀)
    (hs : IsAtom s) (hs_x : s ≤ x) (hs_le : s ≤ b ⊔ u₀)
    (hsb : s ≠ b) (hsu₀ : s ≠ u₀) :
    ∃ t : L, IsAtom t ∧ t ≤ x ⊔ w ∧ ¬ t ≤ x ∧ t ≠ w ∧ ¬ t ≤ u₀ ⊔ w ∧
      project w t x = b ∧ project c₀ t x = s := by
  obtain ⟨hc₀x, hc₀_xw, hline₀, hline₀', hbase₀⟩ :=
    ladder_center hw hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
  have hsc₀ : s ≠ c₀ := fun heq => hc₀x (heq ▸ hs_x)
  have hbw : b ≠ w := fun heq => hwx (heq ▸ hbx)
  have hw_not_sc₀ : ¬ w ≤ s ⊔ c₀ := by
    intro hw_le
    have h1 : c₀ ⊔ s = c₀ ⊔ w :=
      line_eq_of_atom_le hc₀ hs hw hsc₀.symm hc₀w
        (fun heq : s = w => hwx (heq ▸ hs_x)) (by rw [sup_comm]; exact hw_le)
    have h2 : s ≤ u₀ ⊔ w := by
      calc s ≤ c₀ ⊔ s := le_sup_right
        _ = c₀ ⊔ w := h1
        _ = u₀ ⊔ w := hline₀'
    have h3 : s ≤ u₀ := by
      have h4 : s ≤ (u₀ ⊔ w) ⊓ x := le_inf h2 hs_x
      rwa [ladder_wline_trace hw hwx hu₀x] at h4
    exact hsu₀ (IsAtom.eq_of_le hs hu₀ h3)
  have hb_not_sc₀ : ¬ b ≤ s ⊔ c₀ := by
    intro h
    have h1 : b ≤ s := by
      have h2 : b ≤ (s ⊔ c₀) ⊓ x := le_inf h hbx
      rwa [ladder_line_trace hs_x hc₀ hc₀x] at h2
    exact hsb (IsAtom.eq_of_le hb hs h1).symm
  have hcov : s ⊔ c₀ ⋖ (s ⊔ c₀) ⊔ b := covBy_sup_atom hb hb_not_sc₀
  have hz : (s ⊔ c₀) ⊔ b = (b ⊔ u₀) ⊔ w := by
    have hu₀_bs : u₀ ≤ b ⊔ s := by
      have h1 : b ⊔ u₀ = b ⊔ s :=
        line_eq_of_atom_le hb hu₀ hs hbu₀ hsb.symm hsu₀.symm hs_le
      rw [← h1]; exact le_sup_right
    apply le_antisymm
    · refine sup_le (sup_le (hs_le.trans le_sup_left) (hc₀_le.trans ?_)) ?_
      · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
      · exact le_sup_left.trans le_sup_left
    · refine sup_le (sup_le le_sup_right ?_) ?_
      · exact hu₀_bs.trans (sup_le le_sup_right
          (le_sup_left.trans le_sup_left : s ≤ (s ⊔ c₀) ⊔ b))
      · have hw_le : w ≤ u₀ ⊔ c₀ := by rw [hline₀]; exact le_sup_right
        refine hw_le.trans (sup_le ?_ (le_sup_right.trans le_sup_left))
        exact hu₀_bs.trans (sup_le le_sup_right
          (le_sup_left.trans le_sup_left : s ≤ (s ⊔ c₀) ⊔ b))
  have h_not_le : ¬ b ⊔ w ≤ s ⊔ c₀ := fun h =>
    hw_not_sc₀ (le_sup_right.trans h)
  have hb_lt : b < b ⊔ w := lt_of_le_of_ne le_sup_left (fun heq => hwx
    ((le_sup_right.trans heq.ge).trans hbx))
  have h_meet_ne : (s ⊔ c₀) ⊓ (b ⊔ w) ≠ ⊥ := by
    have hcov' : s ⊔ c₀ ⋖ (b ⊔ u₀) ⊔ w := hz ▸ hcov
    exact lines_meet_if_coplanar hcov'
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (fun h => h_not_le h) hb hb_lt
  have h_meet_atom : IsAtom ((b ⊔ w) ⊓ (s ⊔ c₀)) :=
    meet_of_lines_is_atom hb hw hs hc₀ hbw hsc₀ h_not_le
      (by rw [inf_comm]; exact h_meet_ne)
  set t := (b ⊔ w) ⊓ (s ⊔ c₀) with ht_def
  have ht_bw : t ≤ b ⊔ w := inf_le_left
  have ht_sc₀ : t ≤ s ⊔ c₀ := inf_le_right
  have htx : ¬ t ≤ x := by
    intro h
    have h1 : t ≤ b := by
      have h2 : t ≤ (b ⊔ w) ⊓ x := le_inf ht_bw h
      rwa [ladder_wline_trace hw hwx hbx] at h2
    have h3 : t = b := IsAtom.eq_of_le h_meet_atom hb h1
    exact hb_not_sc₀ (h3 ▸ ht_sc₀)
  have htw : t ≠ w := by
    intro heq
    exact hw_not_sc₀ (heq ▸ ht_sc₀)
  have ht_xw : t ≤ x ⊔ w :=
    ht_bw.trans (sup_le (hbx.trans le_sup_left) le_sup_right)
  have hbase : project w t x = b :=
    (ladder_base_iff hw hwx h_meet_atom ht_xw htx htw hb hbx).mpr ht_bw
  have htu₀w : ¬ t ≤ u₀ ⊔ w := by
    intro h
    exact hbu₀ (hbase ▸
      (ladder_base_iff hw hwx h_meet_atom ht_xw htx htw hu₀ hu₀x).mpr h)
  have htc₀ : t ≠ c₀ := by
    intro heq
    apply hbu₀
    rw [← hbase, heq, hbase₀]
  have hshear : project c₀ t x = s := by
    have h1 : c₀ ⊔ s = c₀ ⊔ t :=
      line_eq_of_atom_le hc₀ hs h_meet_atom hsc₀.symm (Ne.symm htc₀)
        (fun heq : s = t => htx (heq ▸ hs_x)) (by rw [sup_comm]; exact ht_sc₀)
    show (t ⊔ c₀) ⊓ x = s
    rw [sup_comm t c₀, ← h1, sup_comm c₀ s]
    exact ladder_line_trace hs_x hc₀ hc₀x
  exact ⟨t, h_meet_atom, ht_xw, htx, htw, htu₀w, hbase, hshear⟩

end LadderLattice

/-! ## The algebra stratum: coefficient calculus in `K^n` -/

section LadderAlgebra

variable {K : Type*} [DivisionRing K] {n : ℕ}

theorem ladder_smul_zero {a : K} {v : Fin n → K} (hv : v ≠ 0)
    (h : a • v = 0) : a = 0 := by
  by_contra ha
  exact hv (by rw [← inv_smul_smul₀ ha v, h, smul_zero])

theorem ladder_pair_zero {u v : Fin n → K} (hu : u ≠ 0)
    (huv : v ∉ Submodule.span K {u}) {β γ : K}
    (h : β • u + γ • v = 0) : β = 0 ∧ γ = 0 := by
  have hγ : γ = 0 := by
    by_contra hγ
    apply huv
    have h1 : γ • v = (-β) • u := by
      rw [neg_smul]
      have h' : γ • v + β • u = 0 := by rw [add_comm]; exact h
      exact eq_neg_of_add_eq_zero_left h'
    have h2 : v = (γ⁻¹ * -β) • u := by
      rw [← smul_smul, ← h1, inv_smul_smul₀ hγ]
    exact h2 ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  refine ⟨?_, hγ⟩
  rw [hγ, zero_smul, add_zero] at h
  exact ladder_smul_zero hu h

theorem ladder_triple_zero {b u v : Fin n → K} (hu : u ≠ 0)
    (huv : v ∉ Submodule.span K {u}) (hb : b ∉ Submodule.span K {u, v})
    {α β γ : K} (h : α • b + β • u + γ • v = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have hα : α = 0 := by
    by_contra hα
    apply hb
    have h1 : α • b = (-β) • u + (-γ) • v := by
      rw [neg_smul, neg_smul, ← neg_add]
      refine neg_eq_of_add_eq_zero_right ?_ |>.symm
      rw [add_comm (β • u + γ • v) (α • b), ← add_assoc]
      exact h
    have h2 : b = (α⁻¹ * -β) • u + (α⁻¹ * -γ) • v := by
      rw [← smul_smul, ← smul_smul, ← smul_add, ← h1, inv_smul_smul₀ hα]
    exact Submodule.mem_span_pair.mpr ⟨α⁻¹ * -β, α⁻¹ * -γ, h2.symm⟩
  rw [hα, zero_smul, zero_add] at h
  obtain ⟨hβ, hγ⟩ := ladder_pair_zero hu huv h
  exact ⟨hα, hβ, hγ⟩

theorem ladder_triple_unique {b u v : Fin n → K} (hu : u ≠ 0)
    (huv : v ∉ Submodule.span K {u}) (hb : b ∉ Submodule.span K {u, v})
    {α β γ α' β' γ' : K}
    (h : α • b + β • u + γ • v = α' • b + β' • u + γ' • v) :
    α = α' ∧ β = β' ∧ γ = γ' := by
  have h1 : (α - α') • b + (β - β') • u + (γ - γ') • v = 0 := by
    rw [sub_smul, sub_smul, sub_smul]
    rw [show α • b - α' • b + (β • u - β' • u) + (γ • v - γ' • v)
      = α • b + β • u + γ • v - (α' • b + β' • u + γ' • v) by abel, h, sub_self]
  obtain ⟨h2, h3, h4⟩ := ladder_triple_zero hu huv hb h1
  exact ⟨sub_eq_zero.mp h2, sub_eq_zero.mp h3, sub_eq_zero.mp h4⟩

theorem ladder_pair_unique {u v : Fin n → K} (hu : u ≠ 0)
    (huv : v ∉ Submodule.span K {u}) {β γ β' γ' : K}
    (h : β • u + γ • v = β' • u + γ' • v) : β = β' ∧ γ = γ' := by
  have h1 : (β - β') • u + (γ - γ') • v = 0 := by
    rw [sub_smul, sub_smul]
    rw [show β • u - β' • u + (γ • v - γ' • v)
      = β • u + γ • v - (β' • u + γ' • v) by abel, h, sub_self]
  obtain ⟨h2, h3⟩ := ladder_pair_zero hu huv h1
  exact ⟨sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩

theorem ladder_span_pair_ne_top (h3 : 3 ≤ n) (a b : Fin n → K) :
    Submodule.span K ({a, b} : Set (Fin n → K)) ≠ ⊤ := by
  intro h
  have h1 : Module.finrank K
      (Submodule.span K ({a, b} : Set (Fin n → K))) ≤ 2 :=
    span_pair_finrank_le a b
  rw [h] at h1
  have h2 : Module.finrank K (⊤ : Submodule K (Fin n → K)) = n := by
    rw [finrank_top]
    simp
  omega

theorem ladder_avoid_two (h3 : 3 ≤ n) (a b c d : Fin n → K) :
    ∃ v : Fin n → K, v ∉ Submodule.span K ({a, b} : Set (Fin n → K)) ∧
      v ∉ Submodule.span K ({c, d} : Set (Fin n → K)) := by
  obtain ⟨va, _, hva⟩ := SetLike.exists_of_lt
    (lt_top_iff_ne_top.mpr (ladder_span_pair_ne_top h3 a b))
  obtain ⟨vc, _, hvc⟩ := SetLike.exists_of_lt
    (lt_top_iff_ne_top.mpr (ladder_span_pair_ne_top h3 c d))
  by_cases h1 : va ∈ Submodule.span K ({c, d} : Set (Fin n → K))
  · by_cases h2 : vc ∈ Submodule.span K ({a, b} : Set (Fin n → K))
    · refine ⟨va + vc, fun h => hva ?_, fun h => hvc ?_⟩
      · have := Submodule.sub_mem _ h h2
        rwa [add_sub_cancel_right] at this
      · have := Submodule.sub_mem _ h h1
        rwa [add_sub_cancel_left] at this
    · exact ⟨vc, h2, hvc⟩
  · exact ⟨va, hva, h1⟩

theorem ladder_span_dodge {z y nv b : Fin n → K}
    (hb : b ∈ Submodule.span K ({z, y} : Set (Fin n → K)))
    (hbz : b ∉ Submodule.span K {z})
    (hn : nv ∉ Submodule.span K ({z, y} : Set (Fin n → K))) :
    b ∉ Submodule.span K ({z, nv} : Set (Fin n → K)) := by
  intro hmem
  obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.mp hmem
  have hc : c ≠ 0 := by
    intro h0
    apply hbz
    rw [h0, zero_smul, add_zero] at hac
    exact hac ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
  apply hn
  have h1 : nv = c⁻¹ • b - (c⁻¹ * a) • z := by
    rw [← hac, smul_add]
    simp only [smul_smul]
    rw [inv_mul_cancel₀ hc, one_smul]
    abel
  rw [h1]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hb)
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))

theorem ladder_pair_swap {u v w' : Fin n → K} (hu : u ≠ 0)
    (hv : v ∉ Submodule.span K {u})
    (hw : w' ∉ Submodule.span K ({u, v} : Set (Fin n → K))) :
    v ∉ Submodule.span K ({u, w'} : Set (Fin n → K)) ∧
      u ∉ Submodule.span K ({v, w'} : Set (Fin n → K)) := by
  constructor
  · intro hmem
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
    have hb : b ≠ 0 := by
      intro h0
      apply hv
      rw [h0, zero_smul, add_zero] at hab
      exact hab ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    apply hw
    have h1 : w' = b⁻¹ • v - (b⁻¹ * a) • u := by
      rw [← hab, smul_add]
      simp only [smul_smul]
      rw [inv_mul_cancel₀ hb, one_smul]
      abel
    rw [h1]
    exact Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
  · intro hmem
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
    have hb : b ≠ 0 := by
      intro h0
      rw [h0, zero_smul, add_zero] at hab
      by_cases ha : a = 0
      · exact hu (by rw [← hab, ha, zero_smul])
      · apply hv
        have h1 : v = a⁻¹ • u := by
          rw [← hab, smul_smul, inv_mul_cancel₀ ha, one_smul]
        exact h1 ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    apply hw
    have h1 : w' = b⁻¹ • u - (b⁻¹ * a) • v := by
      rw [← hab, smul_add]
      simp only [smul_smul]
      rw [inv_mul_cancel₀ hb, one_smul]
      abel
    rw [h1]
    exact Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

theorem ladder_pin {bh ui uj si d sj : Fin n → K}
    (hui : ui ≠ 0) (huij : uj ∉ Submodule.span K {ui})
    (hbij : bh ∉ Submodule.span K ({ui, uj} : Set (Fin n → K)))
    {ai bi : K} (hai : ai ≠ 0) (hsi : si = ai • bh + bi • ui)
    {ki kj : K} (hki : ki ≠ 0) (_hkj : kj ≠ 0) (hd : d = ki • ui + kj • uj)
    (hsj_ne : sj ≠ 0)
    (hmem1 : sj ∈ Submodule.span K ({bh, uj} : Set (Fin n → K)))
    (hmem2 : sj ∈ Submodule.span K ({si, d} : Set (Fin n → K))) :
    ∃ aj : K, aj ≠ 0 ∧
      sj = aj • bh + (aj * ((ai⁻¹ * bi) * (-(ki⁻¹ * kj)))) • uj := by
  obtain ⟨z1, z2, hz⟩ := Submodule.mem_span_pair.mp hmem2
  obtain ⟨a0, b0, hab⟩ := Submodule.mem_span_pair.mp hmem1
  have hexp : (z1 * ai) • bh + (z1 * bi + z2 * ki) • ui + (z2 * kj) • uj
      = sj := by
    rw [← hz, hsi, hd]
    simp only [smul_add, smul_smul, add_smul]
    abel
  have hexp2 : a0 • bh + (0 : K) • ui + b0 • uj = sj := by
    rw [zero_smul, add_zero]
    exact hab
  obtain ⟨h1, h2, h3⟩ := ladder_triple_unique hui huij hbij
    (hexp.trans hexp2.symm)
  have hz1 : z1 ≠ 0 := by
    intro hz10
    apply hsj_ne
    have hzk : z2 * ki = 0 := by
      have h2' := h2
      rw [hz10, zero_mul, zero_add] at h2'
      exact h2'
    have hz2 : z2 = 0 := by
      rcases mul_eq_zero.mp hzk with h | h
      · exact h
      · exact absurd h hki
    rw [← hexp, hz10, hz2]
    simp
  have haj : z1 * ai ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h | h
    · exact hz1 h
    · exact hai h
  refine ⟨z1 * ai, haj, ?_⟩
  have hη : z2 * ki = -(z1 * bi) := by
    have h2' : z2 * ki + z1 * bi = 0 := by rw [add_comm]; exact h2
    exact eq_neg_of_add_eq_zero_left h2'
  have hz2 : z2 = -(z1 * bi) * ki⁻¹ := by
    rw [← hη, mul_assoc, mul_inv_cancel₀ hki, mul_one]
  have hcoef : z2 * kj = z1 * ai * (ai⁻¹ * bi * -(ki⁻¹ * kj)) := by
    rw [hz2, show z1 * ai * (ai⁻¹ * bi * -(ki⁻¹ * kj))
      = z1 * (ai * ai⁻¹) * (bi * -(ki⁻¹ * kj)) by simp only [mul_assoc],
      mul_inv_cancel₀ hai, mul_one]
    simp only [neg_mul, mul_neg, mul_assoc]
  rw [← hexp, h2, zero_smul, add_zero, hcoef]

theorem ladder_graph_comb {bp bq u0 sp sq sr : Fin n → K}
    (hbp : bp ≠ 0) (hpq : bq ∉ Submodule.span K {bp})
    (hu0 : u0 ∉ Submodule.span K ({bp, bq} : Set (Fin n → K)))
    {g : K} (hg : g ≠ 0)
    {lp lq lr xi eta : K}
    {ap aq ar : K} (har : ar ≠ 0)
    (hsp : sp = ap • bp + (ap * (lp * g)) • u0)
    (hsq : sq = aq • bq + (aq * (lq * g)) • u0)
    (hsr : sr = ar • (xi • bp + eta • bq) + (ar * (lr * g)) • u0)
    (hmem : sr ∈ Submodule.span K ({sp, sq} : Set (Fin n → K))) :
    lr = xi * lp + eta * lq := by
  obtain ⟨y1, y2, hy⟩ := Submodule.mem_span_pair.mp hmem
  have hexp : (y1 * (ap * (lp * g)) + y2 * (aq * (lq * g))) • u0
      + (y1 * ap) • bp + (y2 * aq) • bq = sr := by
    rw [← hy, hsp, hsq]
    simp only [smul_add, smul_smul, add_smul]
    abel
  have hexp2 : (ar * (lr * g)) • u0 + (ar * xi) • bp + (ar * eta) • bq
      = sr := by
    rw [hsr]
    simp only [smul_add, smul_smul]
    abel
  obtain ⟨h1, h2, h3⟩ := ladder_triple_unique hbp hpq hu0
    (hexp.trans hexp2.symm)
  have h5 : (y1 * ap * lp + y2 * aq * lq) * g = (ar * lr) * g := by
    have h4 : y1 * (ap * (lp * g)) + y2 * (aq * (lq * g))
        = (y1 * ap * lp + y2 * aq * lq) * g := by
      simp only [add_mul, mul_assoc]
    rw [← h4, h1, mul_assoc]
  have h6 : y1 * ap * lp + y2 * aq * lq = ar * lr := mul_right_cancel₀ hg h5
  have h7 : ar * (xi * lp + eta * lq) = ar * lr := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← h2, ← h3]
    exact h6
  exact (mul_left_cancel₀ har h7).symm

theorem ladder_conv_transfer {bp bq u0 sp sq sr br : Fin n → K}
    {g : K}
    {lp lq lr : K}
    {ap aq ar : K} (hap : ap ≠ 0) (haq : aq ≠ 0)
    (hsp : sp = ap • bp + (ap * (lp * g)) • u0)
    (hsq : sq = aq • bq + (aq * (lq * g)) • u0)
    (hsr : sr = ar • br + (ar * (lr * g)) • u0)
    {z1 z2 : K} (hbr : br = z1 • bp + z2 • bq)
    (hlr : lr = z1 * lp + z2 * lq) :
    sr ∈ Submodule.span K ({sp, sq} : Set (Fin n → K)) := by
  refine Submodule.mem_span_pair.mpr
    ⟨ar * z1 * ap⁻¹, ar * z2 * aq⁻¹, ?_⟩
  have hcp : ar * z1 * ap⁻¹ * ap = ar * z1 := by
    rw [mul_assoc, inv_mul_cancel₀ hap, mul_one]
  have hcq : ar * z2 * aq⁻¹ * aq = ar * z2 := by
    rw [mul_assoc, inv_mul_cancel₀ haq, mul_one]
  have hcp2 : ar * z1 * ap⁻¹ * (ap * (lp * g)) = ar * z1 * (lp * g) := by
    rw [← mul_assoc, hcp]
  have hcq2 : ar * z2 * aq⁻¹ * (aq * (lq * g)) = ar * z2 * (lq * g) := by
    rw [← mul_assoc, hcq]
  rw [hsp, hsq, hsr, hbr, hlr]
  simp only [smul_add, smul_smul]
  rw [hcp, hcq, hcp2, hcq2]
  simp only [add_mul, mul_add, add_smul, mul_assoc]
  abel

theorem ladder_snoc_add (u v : Fin n → K) (a b : K) :
    Fin.snoc u a + Fin.snoc v b = (Fin.snoc (u + v) (a + b) : Fin (n+1) → K) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j
    simp

theorem ladder_snoc_smul (z : K) (v : Fin n → K) (a : K) :
    z • (Fin.snoc v a : Fin (n+1) → K) = Fin.snoc (z • v) (z * a) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j
    simp

theorem ladder_snoc_zero : (Fin.snoc 0 0 : Fin (n+1) → K) = 0 := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j
    simp

omit [DivisionRing K] in
theorem ladder_snoc_eq_iff {u v : Fin n → K} {a b : K} :
    (Fin.snoc u a : Fin (n+1) → K) = Fin.snoc v b ↔ u = v ∧ a = b := by
  constructor
  · intro h
    constructor
    · funext i
      have := congrFun h i.castSucc
      simpa using this
    · have := congrFun h (Fin.last n)
      simpa using this
  · rintro ⟨rfl, rfl⟩
    rfl

theorem ladder_snoc_ne_zero {v : Fin n → K} {a : K} (h : v ≠ 0 ∨ a ≠ 0) :
    (Fin.snoc v a : Fin (n+1) → K) ≠ 0 := by
  intro heq
  rw [← ladder_snoc_zero, ladder_snoc_eq_iff] at heq
  rcases h with h | h
  · exact h heq.1
  · exact h heq.2

theorem ladder_snoc_comb (z₁ z₂ : K) (a b : Fin n → K) (al be : K) :
    z₁ • (Fin.snoc a al : Fin (n+1) → K) + z₂ • Fin.snoc b be
      = Fin.snoc (z₁ • a + z₂ • b) (z₁ * al + z₂ * be) := by
  rw [ladder_snoc_smul, ladder_snoc_smul, ladder_snoc_add]

omit [DivisionRing K] in
theorem ladder_snoc_strip (v : Fin (n+1) → K) :
    (Fin.snoc (v ∘ Fin.castSucc) (v (Fin.last n)) : Fin (n+1) → K) = v := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j
    simp

theorem ladder_span_singleton_smul {v : Fin n → K} {a : K} (ha : a ≠ 0) :
    Submodule.span K {a • v} = Submodule.span K {v} := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.mem_span_singleton.mpr
      ⟨a⁻¹, by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]⟩

theorem ladder_comb_ne_zero {a b : Fin n → K} (ha : a ≠ 0)
    (hab : b ∉ Submodule.span K {a}) (β : K) : a + β • b ≠ 0 := by
  intro h0
  by_cases hβ : β = 0
  · rw [hβ, zero_smul, add_zero] at h0
    exact ha h0
  · apply hab
    have h2 : β • b = -a := eq_neg_of_add_eq_zero_right h0
    have h3 : b = β⁻¹ • -a := by rw [← h2, inv_smul_smul₀ hβ]
    rw [h3, smul_neg]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _))

theorem ladder_comb_not_mem {a b s : Fin n → K} (ha : a ≠ 0)
    (hab : b ∉ Submodule.span K {a}) {ε μ : K} (hε : ε ≠ 0) (hμ : μ ≠ 0)
    (hs : s = ε • a + (ε * μ) • b) :
    s ∉ Submodule.span K {a} ∧ s ∉ Submodule.span K {b} := by
  constructor
  · intro hmem
    obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 : (ε - γ) • a + (ε * μ) • b = 0 := by
      rw [sub_smul]
      rw [show ε • a - γ • a + (ε * μ) • b = ε • a + (ε * μ) • b - γ • a by
        abel, ← hs, ← hγ, sub_self]
    obtain ⟨_, h3⟩ := ladder_pair_zero ha hab h1
    rcases mul_eq_zero.mp h3 with h | h
    · exact hε h
    · exact hμ h
  · intro hmem
    obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 : ε • a + (ε * μ - γ) • b = 0 := by
      rw [sub_smul]
      rw [show ε • a + ((ε * μ) • b - γ • b) = ε • a + (ε * μ) • b - γ • b by
        abel, ← hs, ← hγ, sub_self]
    obtain ⟨h2, _⟩ := ladder_pair_zero ha hab h1
    exact hε h2

theorem ladder_span_swap_last {v : Fin n → K} {lp lq : K} (h : lp ≠ lq) :
    Submodule.span K ({Fin.snoc v lp, Fin.snoc v lq} : Set (Fin (n+1) → K))
      = Submodule.span K ({Fin.snoc v lp, Fin.snoc 0 1} :
          Set (Fin (n+1) → K)) := by
  have hd : lp - lq ≠ 0 := sub_ne_zero.mpr h
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · refine Submodule.mem_span_pair.mpr ⟨1, lq - lp, ?_⟩
      rw [ladder_snoc_comb, one_smul, smul_zero, add_zero, one_mul,
        mul_one]
      congr 1
      abel
  · rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · refine Submodule.mem_span_pair.mpr
        ⟨(lp - lq)⁻¹, -((lp - lq)⁻¹), ?_⟩
      rw [ladder_snoc_comb]
      have h1 : (lp - lq)⁻¹ • v + (-(lp - lq)⁻¹) • v = 0 := by
        rw [neg_smul, add_neg_cancel]
      have h2 : (lp - lq)⁻¹ * lp + (-(lp - lq)⁻¹) * lq = 1 := by
        rw [neg_mul, ← sub_eq_add_neg, ← mul_sub, inv_mul_cancel₀ hd]
      rw [h1, h2]

end LadderAlgebra


/-! ## The construction: raw readings and their spec -/

section LadderRaw

variable {n : ℕ} {K : Type*} [DivisionRing K]

open Classical in
noncomputable def stepRaw {x : L} (P : PointSys x n K) (w c₀ u₀ t : L) : K :=
  if h : ∃ ξ α : K, α ≠ 0 ∧
      P.hv (project c₀ t x) = α • P.hv (project w t x) + (α * ξ) • P.hv u₀
  then h.choose else 0

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem stepRaw_spec {x : L} (P : PointSys x n K) {w c₀ u₀ t : L}
    (hb_ne : P.hv (project w t x) ≠ 0)
    (hu₀_ind : P.hv u₀ ∉ Submodule.span K {P.hv (project w t x)})
    {α ξ : K} (hα : α ≠ 0)
    (heq : P.hv (project c₀ t x)
      = α • P.hv (project w t x) + (α * ξ) • P.hv u₀) :
    stepRaw P w c₀ u₀ t = ξ := by
  have hex : ∃ ξ' α' : K, α' ≠ 0 ∧ P.hv (project c₀ t x)
      = α' • P.hv (project w t x) + (α' * ξ') • P.hv u₀ := ⟨ξ, α, hα, heq⟩
  unfold stepRaw
  rw [dif_pos hex]
  obtain ⟨α', hα', heq'⟩ := hex.choose_spec
  obtain ⟨h1, h2⟩ := ladder_pair_unique hb_ne hu₀_ind (heq'.symm.trans heq)
  rw [h1] at h2
  exact mul_left_cancel₀ hα h2

omit [ComplementedLattice L] in
theorem stepRaw_exists {x : L} (P : PointSys x n K) {w : L}
    (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {u₀ c₀ : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hc₀ : IsAtom c₀) (hc₀_le : c₀ ≤ u₀ ⊔ w) (hc₀u : c₀ ≠ u₀) (hc₀w : c₀ ≠ w)
    {t : L} (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (htw : t ≠ w)
    (htu₀w : ¬ t ≤ u₀ ⊔ w) :
    stepRaw P w c₀ u₀ t ≠ 0 ∧ ∃ α : K, α ≠ 0 ∧
      P.hv (project c₀ t x) = α • P.hv (project w t x)
        + (α * stepRaw P w c₀ u₀ t) • P.hv u₀ := by
  obtain ⟨hc₀x, hc₀_xw, hline, hline', hbase⟩ :=
    ladder_center hw hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
  have htc₀ : t ≠ c₀ := fun heq => htu₀w (heq ▸ hc₀_le)
  have hb_atom : IsAtom (project w t x) :=
    ladder_trace_atom hw hwx hw le_sup_right ht ht_le htx htw
  have hs_atom : IsAtom (project c₀ t x) :=
    ladder_trace_atom hw hwx hc₀ hc₀_xw ht ht_le htx htc₀
  have hb_x : project w t x ≤ x := inf_le_right
  have hs_x : project c₀ t x ≤ x := inf_le_right
  have hbu₀ : project w t x ≠ u₀ := fun h =>
    htu₀w ((ladder_base_iff hw hwx ht ht_le htx htw hu₀ hu₀x).mp h)
  have hsu₀ : project c₀ t x ≠ u₀ :=
    ladder_shear_ne_axis hw hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w ht htu₀w
  have hsb : project c₀ t x ≠ project w t x :=
    ladder_shear_ne_base hw hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w ht ht_le htx
      htw htu₀w
  have hs_le : project c₀ t x ≤ project w t x ⊔ u₀ :=
    ladder_shear_le hw hwx hu₀x hc₀_le ht ht_le htx htw
  have hmem : P.hv (project c₀ t x) ∈ Submodule.span K
      ({P.hv (project w t x), P.hv u₀} : Set (Fin n → K)) :=
    (P.collinear_iff hb_atom hb_x hu₀ hu₀x hs_atom hs_x hbu₀).mp hs_le
  obtain ⟨α, β, heq⟩ := Submodule.mem_span_pair.mp hmem
  have hb_ne : P.hv (project w t x) ≠ 0 := P.ne_zero hb_atom hb_x
  have hu₀_ind : P.hv u₀ ∉ Submodule.span K {P.hv (project w t x)} :=
    P.span_inj hb_atom hb_x hu₀ hu₀x hbu₀
  have hα : α ≠ 0 := by
    intro h0
    apply P.span_inj hu₀ hu₀x hs_atom hs_x (Ne.symm hsu₀)
    rw [← heq, h0, zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hβα : β = α * (α⁻¹ * β) := by
    rw [← mul_assoc, mul_inv_cancel₀ hα, one_mul]
  have heq' : P.hv (project c₀ t x)
      = α • P.hv (project w t x) + (α * (α⁻¹ * β)) • P.hv u₀ := by
    rw [← hβα]
    exact heq.symm
  have hspec : stepRaw P w c₀ u₀ t = α⁻¹ * β :=
    stepRaw_spec P hb_ne hu₀_ind hα heq'
  constructor
  · rw [hspec]
    intro h0
    have hβ : β = 0 := by rw [hβα, h0, mul_zero]
    apply P.span_inj hb_atom hb_x hs_atom hs_x (Ne.symm hsb)
    rw [← heq, hβ, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · refine ⟨α, hα, ?_⟩
    rw [hspec]
    exact heq'

end LadderRaw


/-! ## The transport engine: gauge symmetry, the cocycle, the central lemma -/

section LadderTransport

variable {n : ℕ} {K : Type*} [DivisionRing K]

omit [ComplementedLattice L] in
theorem step_transport {x : L} (P : PointSys x n K) {w : L}
    (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {ui ci uj cj : L}
    (hui : IsAtom ui) (hui_x : ui ≤ x)
    (hci : IsAtom ci) (hci_le : ci ≤ ui ⊔ w) (hciu : ci ≠ ui) (hciw : ci ≠ w)
    (huj : IsAtom uj) (huj_x : uj ≤ x)
    (hcj : IsAtom cj) (hcj_le : cj ≤ uj ⊔ w) (hcju : cj ≠ uj) (hcjw : cj ≠ w)
    (huij : ui ≠ uj)
    {t : L} (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (htw : t ≠ w)
    (hti : ¬ t ≤ ui ⊔ w) (htj : ¬ t ≤ uj ⊔ w)
    (hb_ind : P.hv (project w t x) ∉
      Submodule.span K ({P.hv ui, P.hv uj} : Set (Fin n → K))) :
    stepRaw P w cj uj t
      = stepRaw P w ci ui t * -(stepRaw P w ci ui cj)⁻¹ := by
  obtain ⟨hcix, hci_xw, hlinei, hlinei', hbasei⟩ :=
    ladder_center hw hwx hui hui_x hci hci_le hciu hciw
  obtain ⟨hcjx, hcj_xw, hlinej, hlinej', hbasej⟩ :=
    ladder_center hw hwx huj huj_x hcj hcj_le hcju hcjw
  have hcj_not_i : ¬ cj ≤ ui ⊔ w := by
    intro h
    have h1 := (ladder_base_iff hw hwx hcj hcj_xw hcjx hcjw hui hui_x).mpr h
    rw [hbasej] at h1
    exact huij h1.symm
  have hb_atom : IsAtom (project w t x) :=
    ladder_trace_atom hw hwx hw le_sup_right ht ht_le htx htw
  have hb_x : project w t x ≤ x := inf_le_right
  have hb_ne : P.hv (project w t x) ≠ 0 := P.ne_zero hb_atom hb_x
  have hbuj : project w t x ≠ uj := fun h =>
    htj ((ladder_base_iff hw hwx ht ht_le htx htw huj huj_x).mp h)
  obtain ⟨hrawi_ne, αi, hαi, hsi_eq⟩ :=
    stepRaw_exists P hw hwx hui hui_x hci hci_le hciu hciw ht ht_le htx htw hti
  obtain ⟨hγ_ne, κ, hκ, hd_eq⟩ :=
    stepRaw_exists P hw hwx hui hui_x hci hci_le hciu hciw hcj hcj_xw hcjx
      hcjw hcj_not_i
  rw [hbasej] at hd_eq
  have htci : t ≠ ci := fun heq => hti (heq ▸ hci_le)
  have htcj : t ≠ cj := fun heq => htj (heq ▸ hcj_le)
  have hsi_atom : IsAtom (project ci t x) :=
    ladder_trace_atom hw hwx hci hci_xw ht ht_le htx htci
  have hsi_x : project ci t x ≤ x := inf_le_right
  have hsj_atom : IsAtom (project cj t x) :=
    ladder_trace_atom hw hwx hcj hcj_xw ht ht_le htx htcj
  have hsj_x : project cj t x ≤ x := inf_le_right
  obtain ⟨hcicj, hd_atom, hd_le, hd_ui, hd_uj⟩ :=
    ladder_bridge hw hwx hui hui_x huj huj_x huij hci hci_le hciu hciw
      hcj hcj_le hcju hcjw
  have hd_x : project ci cj x ≤ x := inf_le_right
  have huj_ind : P.hv uj ∉ Submodule.span K {P.hv ui} :=
    P.span_inj hui hui_x huj huj_x huij
  have hsid : project ci t x ≠ project ci cj x := by
    intro heq
    have h1 : P.hv (project ci t x) = P.hv (project ci cj x) := by rw [heq]
    rw [hsi_eq, hd_eq] at h1
    have h2 : αi • P.hv (project w t x)
        + (αi * stepRaw P w ci ui t) • P.hv ui + (0:K) • P.hv uj
        = (0:K) • P.hv (project w t x)
          + (κ * stepRaw P w ci ui cj) • P.hv ui + κ • P.hv uj := by
      rw [zero_smul, zero_smul, add_zero, zero_add, h1]
      exact add_comm _ _
    obtain ⟨h3, _, _⟩ := ladder_triple_unique (P.ne_zero hui hui_x)
      huj_ind hb_ind h2
    exact hαi h3
  have hs_le : project cj t x ≤ project w t x ⊔ uj :=
    ladder_shear_le hw hwx huj_x hcj_le ht ht_le htx htw
  have hmem1 : P.hv (project cj t x) ∈ Submodule.span K
      ({P.hv (project w t x), P.hv uj} : Set (Fin n → K)) :=
    (P.collinear_iff hb_atom hb_x huj huj_x hsj_atom hsj_x hbuj).mp hs_le
  have hshadow : project cj t x ≤ project ci t x ⊔ project ci cj x :=
    ladder_shadow hw hwx hui hui_x huj huj_x huij hci hci_le hciu hciw
      hcj hcj_le hcju hcjw ht ht_le htx htw hti
  have hmem2 : P.hv (project cj t x) ∈ Submodule.span K
      ({P.hv (project ci t x), P.hv (project ci cj x)} : Set (Fin n → K)) :=
    (P.collinear_iff hsi_atom hsi_x hd_atom hd_x hsj_atom hsj_x hsid).mp
      hshadow
  have hd_eq' : P.hv (project ci cj x)
      = (κ * stepRaw P w ci ui cj) • P.hv ui + κ • P.hv uj := by
    rw [hd_eq]
    exact add_comm _ _
  obtain ⟨aj, haj, hsj_eq⟩ := ladder_pin (P.ne_zero hui hui_x) huj_ind hb_ind
    hαi hsi_eq (mul_ne_zero hκ hγ_ne) hκ hd_eq'
    (P.ne_zero hsj_atom hsj_x) hmem1 hmem2
  have hcoef : (αi⁻¹ * (αi * stepRaw P w ci ui t))
      * -((κ * stepRaw P w ci ui cj)⁻¹ * κ)
      = stepRaw P w ci ui t * -(stepRaw P w ci ui cj)⁻¹ := by
    rw [← mul_assoc αi⁻¹ αi _, inv_mul_cancel₀ hαi, one_mul, mul_inv_rev,
      mul_assoc (stepRaw P w ci ui cj)⁻¹ κ⁻¹ κ, inv_mul_cancel₀ hκ, mul_one]
  rw [hcoef] at hsj_eq
  exact stepRaw_spec P hb_ne (P.span_inj hb_atom hb_x huj huj_x hbuj) haj
    hsj_eq

omit [ComplementedLattice L] in
theorem step_gauge_symm {x : L} (P : PointSys x n K) {w : L}
    (hw : IsAtom w) (hwx : ¬ w ≤ x)
    {ui ci uj cj : L}
    (hui : IsAtom ui) (hui_x : ui ≤ x)
    (hci : IsAtom ci) (hci_le : ci ≤ ui ⊔ w) (hciu : ci ≠ ui) (hciw : ci ≠ w)
    (huj : IsAtom uj) (huj_x : uj ≤ x)
    (hcj : IsAtom cj) (hcj_le : cj ≤ uj ⊔ w) (hcju : cj ≠ uj) (hcjw : cj ≠ w)
    (huij : ui ≠ uj) :
    stepRaw P w ci ui cj * stepRaw P w cj uj ci = 1 := by
  obtain ⟨hcix, hci_xw, hlinei, hlinei', hbasei⟩ :=
    ladder_center hw hwx hui hui_x hci hci_le hciu hciw
  obtain ⟨hcjx, hcj_xw, hlinej, hlinej', hbasej⟩ :=
    ladder_center hw hwx huj huj_x hcj hcj_le hcju hcjw
  have hcj_not_i : ¬ cj ≤ ui ⊔ w := by
    intro h
    have h1 := (ladder_base_iff hw hwx hcj hcj_xw hcjx hcjw hui hui_x).mpr h
    rw [hbasej] at h1
    exact huij h1.symm
  have hci_not_j : ¬ ci ≤ uj ⊔ w := by
    intro h
    have h1 := (ladder_base_iff hw hwx hci hci_xw hcix hciw huj huj_x).mpr h
    rw [hbasei] at h1
    exact huij h1
  obtain ⟨hγ_ne, κ, hκ, hd_eq⟩ :=
    stepRaw_exists P hw hwx hui hui_x hci hci_le hciu hciw hcj hcj_xw hcjx
      hcjw hcj_not_i
  obtain ⟨hγ'_ne, κ', hκ', hd'_eq⟩ :=
    stepRaw_exists P hw hwx huj huj_x hcj hcj_le hcju hcjw hci hci_xw hcix
      hciw hci_not_j
  rw [hbasej] at hd_eq
  rw [hbasei] at hd'_eq
  have hdd : project ci cj x = project cj ci x := by
    unfold project
    rw [sup_comm]
  rw [← hdd] at hd'_eq
  have h1 := hd_eq.symm.trans hd'_eq
  have h2 : (κ * stepRaw P w ci ui cj) • P.hv ui + κ • P.hv uj
      = κ' • P.hv ui + (κ' * stepRaw P w cj uj ci) • P.hv uj := by
    rw [add_comm ((κ * stepRaw P w ci ui cj) • P.hv ui) (κ • P.hv uj)]
    exact h1
  obtain ⟨h3, h4⟩ := ladder_pair_unique (P.ne_zero hui hui_x)
    (P.span_inj hui hui_x huj huj_x huij) h2
  have h5 : κ * (stepRaw P w ci ui cj * stepRaw P w cj uj ci) = κ := by
    rw [← mul_assoc, h3, ← h4]
  have h6 := mul_left_cancel₀ hκ (h5.trans (mul_one κ).symm)
  exact h6

omit [ComplementedLattice L] in
theorem step_cocycle {x : L} (P : PointSys x n K) {w : L}
    (hw : IsAtom w) (hwx : ¬ w ≤ x)
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    {ui ci uj cj uk ck : L}
    (hui : IsAtom ui) (hui_x : ui ≤ x)
    (hci : IsAtom ci) (hci_le : ci ≤ ui ⊔ w) (hciu : ci ≠ ui) (hciw : ci ≠ w)
    (huj : IsAtom uj) (huj_x : uj ≤ x)
    (hcj : IsAtom cj) (hcj_le : cj ≤ uj ⊔ w) (hcju : cj ≠ uj) (hcjw : cj ≠ w)
    (huk : IsAtom uk) (huk_x : uk ≤ x)
    (hck : IsAtom ck) (hck_le : ck ≤ uk ⊔ w) (hcku : ck ≠ uk) (hckw : ck ≠ w)
    (hij : P.hv uj ∉ Submodule.span K {P.hv ui})
    (hijk : P.hv uk ∉ Submodule.span K ({P.hv ui, P.hv uj} : Set (Fin n → K))) :
    -(stepRaw P w ci ui ck)⁻¹
      = -(stepRaw P w ci ui cj)⁻¹ * -(stepRaw P w cj uj ck)⁻¹ := by
  have huij : ui ≠ uj := by
    intro h
    exact hij (h ▸ Submodule.mem_span_singleton_self _)
  have huik : ui ≠ uk := by
    intro h
    exact hijk (h ▸ Submodule.subset_span (Set.mem_insert _ _))
  have hujk : uj ≠ uk := by
    intro h
    exact hijk (h ▸ Submodule.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  obtain ⟨hswap1, hswap2⟩ := ladder_pair_swap (P.ne_zero hui hui_x) hij hijk
  have hv_ne : P.hv ui + P.hv uj + P.hv uk ≠ 0 := by
    intro h0
    apply hijk
    have h1 : P.hv uk = -(P.hv ui + P.hv uj) :=
      eq_neg_of_add_eq_zero_right h0
    rw [h1]
    exact Submodule.neg_mem _ (Submodule.add_mem _
      (Submodule.subset_span (Set.mem_insert _ _))
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  obtain ⟨b, hb_atom, hb_x, hb_span⟩ :=
    P.span_surj (P.hv ui + P.hv uj + P.hv uk) hv_ne
  have hb_mem : P.hv b ∈ Submodule.span K {P.hv ui + P.hv uj + P.hv uk} := by
    rw [← hb_span]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨δ, hδ⟩ := Submodule.mem_span_singleton.mp hb_mem
  have hδ_ne : δ ≠ 0 := by
    intro h0
    apply P.ne_zero hb_atom hb_x
    rw [← hδ, h0, zero_smul]
  have hvstar_of : ∀ S : Submodule K (Fin n → K),
      P.hv b ∈ S → P.hv ui + P.hv uj + P.hv uk ∈ S := by
    intro S hS
    have h1 : P.hv ui + P.hv uj + P.hv uk = δ⁻¹ • P.hv b := by
      rw [← hδ, smul_smul, inv_mul_cancel₀ hδ_ne, one_smul]
    rw [h1]
    exact Submodule.smul_mem _ _ hS
  have hb_ij : P.hv b ∉ Submodule.span K
      ({P.hv ui, P.hv uj} : Set (Fin n → K)) := by
    intro h
    apply hijk
    have h1 := hvstar_of _ h
    have h2 : P.hv uk = (P.hv ui + P.hv uj + P.hv uk)
        - P.hv ui - P.hv uj := by abel
    rw [h2]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1
      (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hb_ik : P.hv b ∉ Submodule.span K
      ({P.hv ui, P.hv uk} : Set (Fin n → K)) := by
    intro h
    apply hswap1
    have h1 := hvstar_of _ h
    have h2 : P.hv uj = (P.hv ui + P.hv uj + P.hv uk)
        - P.hv ui - P.hv uk := by abel
    rw [h2]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1
      (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hb_jk : P.hv b ∉ Submodule.span K
      ({P.hv uj, P.hv uk} : Set (Fin n → K)) := by
    intro h
    apply hswap2
    have h1 := hvstar_of _ h
    have h2 : P.hv ui = (P.hv ui + P.hv uj + P.hv uk)
        - P.hv uj - P.hv uk := by abel
    rw [h2]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1
      (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hbw : b ≠ w := fun h => hwx (h ▸ hb_x)
  obtain ⟨t, ht_atom, ht_le', htb, htw⟩ := h_irred b w hb_atom hw hbw
  have ht_xw : t ≤ x ⊔ w :=
    ht_le'.trans (sup_le (hb_x.trans le_sup_left) le_sup_right)
  have htx : ¬ t ≤ x := by
    intro h
    apply htb
    have h1 : t ≤ (b ⊔ w) ⊓ x := le_inf ht_le' h
    rw [ladder_wline_trace hw hwx hb_x] at h1
    exact IsAtom.eq_of_le ht_atom hb_atom h1
  have hbase_t : project w t x = b :=
    (ladder_base_iff hw hwx ht_atom ht_xw htx htw hb_atom hb_x).mpr ht_le'
  have hb_ne_of : ∀ {z : L}, IsAtom z → z ≤ x →
      P.hv b ∉ Submodule.span K {P.hv z} → b ≠ z := by
    intro z hz hz_x hspan h
    exact hspan (h ▸ Submodule.mem_span_singleton_self _)
  have hti : ¬ t ≤ ui ⊔ w := by
    intro h
    have h1 := (ladder_base_iff hw hwx ht_atom ht_xw htx htw hui hui_x).mpr h
    rw [hbase_t] at h1
    exact hb_ij (h1 ▸ Submodule.subset_span (Set.mem_insert _ _))
  have htj : ¬ t ≤ uj ⊔ w := by
    intro h
    have h1 := (ladder_base_iff hw hwx ht_atom ht_xw htx htw huj huj_x).mpr h
    rw [hbase_t] at h1
    exact hb_ij (h1 ▸ Submodule.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have htk : ¬ t ≤ uk ⊔ w := by
    intro h
    have h1 := (ladder_base_iff hw hwx ht_atom ht_xw htx htw huk huk_x).mpr h
    rw [hbase_t] at h1
    exact hb_ik (h1 ▸ Submodule.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hb_ind_ij : P.hv (project w t x) ∉ Submodule.span K
      ({P.hv ui, P.hv uj} : Set (Fin n → K)) := by rw [hbase_t]; exact hb_ij
  have hb_ind_ik : P.hv (project w t x) ∉ Submodule.span K
      ({P.hv ui, P.hv uk} : Set (Fin n → K)) := by rw [hbase_t]; exact hb_ik
  have hb_ind_jk : P.hv (project w t x) ∉ Submodule.span K
      ({P.hv uj, P.hv uk} : Set (Fin n → K)) := by rw [hbase_t]; exact hb_jk
  have T_ij := step_transport P hw hwx hui hui_x hci hci_le hciu hciw
    huj huj_x hcj hcj_le hcju hcjw huij ht_atom ht_xw htx htw hti htj
    hb_ind_ij
  have T_ik := step_transport P hw hwx hui hui_x hci hci_le hciu hciw
    huk huk_x hck hck_le hcku hckw huik ht_atom ht_xw htx htw hti htk
    hb_ind_ik
  have T_jk := step_transport P hw hwx huj huj_x hcj hcj_le hcju hcjw
    huk huk_x hck hck_le hcku hckw hujk ht_atom ht_xw htx htw htj htk
    hb_ind_jk
  have hraw_ne : stepRaw P w ci ui t ≠ 0 :=
    (stepRaw_exists P hw hwx hui hui_x hci hci_le hciu hciw ht_atom ht_xw
      htx htw hti).1
  have h1 : stepRaw P w ci ui t * -(stepRaw P w ci ui ck)⁻¹
      = stepRaw P w ci ui t
        * (-(stepRaw P w ci ui cj)⁻¹ * -(stepRaw P w cj uj ck)⁻¹) := by
    rw [← T_ik, ← mul_assoc, ← T_ij, ← T_jk]
  exact mul_left_cancel₀ hraw_ne h1

end LadderTransport


/-! ## The step frame: heights, extended coordinates, the central lemma -/

section LadderFrame

variable {n : ℕ} {K : Type*} [DivisionRing K] {x : L}

omit [ComplementedLattice L]

structure StepFrame (P : PointSys x n K) (w : L) where
  hn : 3 ≤ n
  h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
    ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b
  hw : IsAtom w
  hwx : ¬ w ≤ x
  u : L
  hu : IsAtom u
  hux : u ≤ x
  u' : L
  hu' : IsAtom u'
  hu'x : u' ≤ x
  huu' : P.hv u' ∉ Submodule.span K {P.hv u}
  c : L
  hc : IsAtom c
  hc_le : c ≤ u ⊔ w
  hcu : c ≠ u
  hcw : c ≠ w
  e : L
  he : IsAtom e
  he_le : e ≤ u' ⊔ w
  heu : e ≠ u'
  hew : e ≠ w

variable {P : PointSys x n K} {w : L}

omit [IsModularLattice L] [IsAtomistic L] in
theorem StepFrame.u_ne_u' (F : StepFrame P w) : F.u ≠ F.u' := fun h =>
  F.huu' (by rw [h]; exact Submodule.mem_span_singleton_self _)

omit [IsModularLattice L] [IsAtomistic L] in
theorem StepFrame.u'_ne_u (F : StepFrame P w) : F.u' ≠ F.u :=
  (F.u_ne_u').symm

open Classical in
noncomputable def StepFrame.lam (F : StepFrame P w) (t : L) : K :=
  if t ≤ F.u ⊔ w
  then -(stepRaw P w F.e F.u' t * stepRaw P w F.c F.u F.e)
  else stepRaw P w F.c F.u t

omit [IsModularLattice L] [IsAtomistic L] in
theorem StepFrame.lam_visible (F : StepFrame P w) {t : L}
    (h : ¬ t ≤ F.u ⊔ w) : F.lam t = stepRaw P w F.c F.u t := by
  unfold StepFrame.lam
  rw [if_neg h]

omit [IsModularLattice L] [IsAtomistic L] in
theorem StepFrame.lam_blind (F : StepFrame P w) {t : L}
    (h : t ≤ F.u ⊔ w) :
    F.lam t = -(stepRaw P w F.e F.u' t * stepRaw P w F.c F.u F.e) := by
  unfold StepFrame.lam
  rw [if_pos h]

open Classical in
noncomputable def StepFrame.hv' (F : StepFrame P w) (t : L) : Fin (n+1) → K :=
  if t ≤ x then Fin.snoc (P.hv t) 0
  else if t = w then Fin.snoc 0 1
  else Fin.snoc (P.hv (project w t x)) (F.lam t)

omit [IsModularLattice L] [IsAtomistic L] in
theorem StepFrame.hv'_of_le (F : StepFrame P w) {t : L} (h : t ≤ x) :
    F.hv' t = Fin.snoc (P.hv t) 0 := by
  unfold StepFrame.hv'
  rw [if_pos h]

omit [IsModularLattice L] [IsAtomistic L] in
theorem StepFrame.hv'_w (F : StepFrame P w) :
    F.hv' w = Fin.snoc 0 1 := by
  unfold StepFrame.hv'
  rw [if_neg F.hwx, if_pos rfl]

omit [IsModularLattice L] [IsAtomistic L] in
theorem StepFrame.hv'_affine (F : StepFrame P w) {t : L}
    (htx : ¬ t ≤ x) (htw : t ≠ w) :
    F.hv' t = Fin.snoc (P.hv (project w t x)) (F.lam t) := by
  unfold StepFrame.hv'
  rw [if_neg htx, if_neg htw]

theorem StepFrame.blind_not_mirror (F : StepFrame P w) {t : L}
    (ht : IsAtom t) (htw : t ≠ w) (h : t ≤ F.u ⊔ w) : ¬ t ≤ F.u' ⊔ w := by
  intro h'
  have h1 : t ≤ w := by
    have h2 := le_inf h h'
    rwa [ladder_axis_inf F.hw F.hwx F.hu F.hux F.hu' F.hu'x F.u_ne_u'] at h2
  exact htw (IsAtom.eq_of_le ht F.hw h1)

theorem StepFrame.e_not_primary (F : StepFrame P w) : ¬ F.e ≤ F.u ⊔ w := by
  intro h
  obtain ⟨hex, he_xw, _, _, hbase⟩ :=
    ladder_center F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu F.hew
  have h2 := (ladder_base_iff F.hw F.hwx F.he he_xw hex F.hew F.hu F.hux).mpr h
  rw [hbase] at h2
  exact F.u_ne_u' h2.symm

theorem StepFrame.c_not_mirror (F : StepFrame P w) : ¬ F.c ≤ F.u' ⊔ w := by
  intro h
  obtain ⟨hcx, hc_xw, _, _, hbase⟩ :=
    ladder_center F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu F.hcw
  have h2 := (ladder_base_iff F.hw F.hwx F.hc hc_xw hcx F.hcw F.hu' F.hu'x).mpr h
  rw [hbase] at h2
  exact F.u_ne_u' h2

theorem StepFrame.lam_ne_zero (F : StepFrame P w) {t : L}
    (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (htw : t ≠ w) :
    F.lam t ≠ 0 := by
  by_cases hvis : t ≤ F.u ⊔ w
  · rw [F.lam_blind hvis]
    have h1 :=
      (stepRaw_exists P F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu F.hew
        ht ht_le htx htw (F.blind_not_mirror ht htw hvis)).1
    obtain ⟨hex, he_xw, _, _, _⟩ :=
      ladder_center F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu F.hew
    have h2 :=
      (stepRaw_exists P F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu F.hcw
        F.he he_xw hex F.hew F.e_not_primary).1
    exact neg_ne_zero.mpr (mul_ne_zero h1 h2)
  · rw [F.lam_visible hvis]
    exact (stepRaw_exists P F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu F.hcw
      ht ht_le htx htw hvis).1

theorem StepFrame.central (F : StepFrame P w)
    {u₀ c₀ : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hu₀_ind : P.hv u₀ ∉ Submodule.span K
      ({P.hv F.u, P.hv F.u'} : Set (Fin n → K)))
    (hc₀ : IsAtom c₀) (hc₀_le : c₀ ≤ u₀ ⊔ w) (hc₀u : c₀ ≠ u₀) (hc₀w : c₀ ≠ w)
    {t : L} (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x) (htw : t ≠ w)
    (htu₀w : ¬ t ≤ u₀ ⊔ w) :
    stepRaw P w c₀ u₀ t = F.lam t * -(F.lam c₀)⁻¹ := by
  have hu₀u : u₀ ≠ F.u := by
    intro h
    apply hu₀_ind
    rw [h]
    exact Submodule.subset_span (Set.mem_insert _ _)
  have hu₀u' : u₀ ≠ F.u' := by
    intro h
    apply hu₀_ind
    rw [h]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨hc₀x, hc₀_xw, hline₀, hline₀', hbase₀⟩ :=
    ladder_center F.hw F.hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
  have hc₀_vis : ¬ c₀ ≤ F.u ⊔ w := by
    intro h
    have h1 := (ladder_base_iff F.hw F.hwx hc₀ hc₀_xw hc₀x hc₀w
      F.hu F.hux).mpr h
    rw [hbase₀] at h1
    exact hu₀u h1
  rw [F.lam_visible hc₀_vis]
  by_cases hvis : t ≤ F.u ⊔ w
  · rw [F.lam_blind hvis]
    have ht_mir : ¬ t ≤ F.u' ⊔ w := F.blind_not_mirror ht htw hvis
    have hbase_t : project w t x = F.u :=
      (ladder_base_iff F.hw F.hwx ht ht_le htx htw F.hu F.hux).mpr hvis
    have hu₀_ind' : P.hv u₀ ∉ Submodule.span K
        ({P.hv F.u', P.hv F.u} : Set (Fin n → K)) := by
      rw [Set.pair_comm]
      exact hu₀_ind
    have hswap := ladder_pair_swap (P.ne_zero F.hu' F.hu'x)
      (P.span_inj F.hu' F.hu'x F.hu F.hux F.u'_ne_u) hu₀_ind'
    have hb_ind : P.hv (project w t x) ∉ Submodule.span K
        ({P.hv F.u', P.hv u₀} : Set (Fin n → K)) := by
      rw [hbase_t]
      exact hswap.1
    have T := step_transport P F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu
      F.hew hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w hu₀u'.symm ht ht_le htx htw
      ht_mir htu₀w hb_ind
    have C := step_cocycle P F.hw F.hwx F.h_irred
      F.hu' F.hu'x F.he F.he_le F.heu F.hew
      F.hu F.hux F.hc F.hc_le F.hcu F.hcw
      hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
      (P.span_inj F.hu' F.hu'x F.hu F.hux F.u'_ne_u) hu₀_ind'
    have S := step_gauge_symm P F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu
      F.hcw F.hu' F.hu'x F.he F.he_le F.heu F.hew F.u_ne_u'
    have hS : stepRaw P w F.c F.u F.e = (stepRaw P w F.e F.u' F.c)⁻¹ :=
      eq_inv_of_mul_eq_one_left S
    rw [T, C, hS]
    simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
  · rw [F.lam_visible hvis]
    have hbu : project w t x ≠ F.u := fun h =>
      hvis ((ladder_base_iff F.hw F.hwx ht ht_le htx htw F.hu F.hux).mp h)
    have hbu₀ : project w t x ≠ u₀ := fun h =>
      htu₀w ((ladder_base_iff F.hw F.hwx ht ht_le htx htw hu₀ hu₀x).mp h)
    have hb_atom : IsAtom (project w t x) :=
      ladder_trace_atom F.hw F.hwx F.hw le_sup_right ht ht_le htx htw
    have hb_x : project w t x ≤ x := inf_le_right
    by_cases hcase : P.hv (project w t x) ∈ Submodule.span K
        ({P.hv F.u, P.hv u₀} : Set (Fin n → K))
    · obtain ⟨v₁, hv₁a, _⟩ := ladder_avoid_two F.hn (P.hv F.u) (P.hv u₀)
        (P.hv F.u) (P.hv u₀)
      have hv₁_ne : v₁ ≠ 0 := fun h => hv₁a (h ▸ Submodule.zero_mem _)
      obtain ⟨u₁, hu₁, hu₁x, hu₁_span⟩ := P.span_surj v₁ hv₁_ne
      have hu₁_ind : P.hv u₁ ∉ Submodule.span K
          ({P.hv F.u, P.hv u₀} : Set (Fin n → K)) := by
        intro h
        apply hv₁a
        have h1 : v₁ ∈ Submodule.span K {P.hv u₁} := by
          rw [hu₁_span]
          exact Submodule.mem_span_singleton_self _
        obtain ⟨δ, hδ⟩ := Submodule.mem_span_singleton.mp h1
        rw [← hδ]
        exact Submodule.smul_mem _ _ h
      have hu₁w : u₁ ≠ w := fun h => F.hwx (h ▸ hu₁x)
      obtain ⟨c₁, hc₁, hc₁_le, hc₁u, hc₁w⟩ := F.h_irred u₁ w hu₁ F.hw hu₁w
      have hu₁_u : u₁ ≠ F.u := by
        intro h
        apply hu₁_ind
        rw [h]
        exact Submodule.subset_span (Set.mem_insert _ _)
      have hu₁_u₀ : u₁ ≠ u₀ := by
        intro h
        apply hu₁_ind
        rw [h]
        exact Submodule.subset_span
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have hb_not_u : P.hv (project w t x) ∉ Submodule.span K {P.hv F.u} :=
        P.span_inj F.hu F.hux hb_atom hb_x (Ne.symm hbu)
      have hb_not_u₀ : P.hv (project w t x) ∉ Submodule.span K {P.hv u₀} :=
        P.span_inj hu₀ hu₀x hb_atom hb_x (Ne.symm hbu₀)
      have hdodge1 : P.hv (project w t x) ∉ Submodule.span K
          ({P.hv F.u, P.hv u₁} : Set (Fin n → K)) :=
        ladder_span_dodge hcase hb_not_u hu₁_ind
      have hcase' : P.hv (project w t x) ∈ Submodule.span K
          ({P.hv u₀, P.hv F.u} : Set (Fin n → K)) := by
        rw [Set.pair_comm]
        exact hcase
      have hu₁_ind' : P.hv u₁ ∉ Submodule.span K
          ({P.hv u₀, P.hv F.u} : Set (Fin n → K)) := by
        rw [Set.pair_comm]
        exact hu₁_ind
      have hdodge2 : P.hv (project w t x) ∉ Submodule.span K
          ({P.hv u₀, P.hv u₁} : Set (Fin n → K)) :=
        ladder_span_dodge hcase' hb_not_u₀ hu₁_ind'
      have hdodge2' : P.hv (project w t x) ∉ Submodule.span K
          ({P.hv u₁, P.hv u₀} : Set (Fin n → K)) := by
        rw [Set.pair_comm]
        exact hdodge2
      have hbu₁ : project w t x ≠ u₁ := by
        intro h
        apply hu₁_ind
        rw [← h]
        exact hcase
      have ht_u₁ : ¬ t ≤ u₁ ⊔ w := fun h =>
        hbu₁ ((ladder_base_iff F.hw F.hwx ht ht_le htx htw hu₁ hu₁x).mpr h)
      have T1 := step_transport P F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu
        F.hcw hu₁ hu₁x hc₁ hc₁_le hc₁u hc₁w hu₁_u.symm ht ht_le htx htw
        hvis ht_u₁ hdodge1
      have T2 := step_transport P F.hw F.hwx hu₁ hu₁x hc₁ hc₁_le hc₁u hc₁w
        hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w hu₁_u₀ ht ht_le htx htw ht_u₁ htu₀w
        hdodge2'
      have hu₁_not_u : P.hv u₁ ∉ Submodule.span K {P.hv F.u} := by
        intro h
        apply hu₁_ind
        exact Submodule.span_mono
          (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) h
      have hu₀_not_uu₁ : P.hv u₀ ∉ Submodule.span K
          ({P.hv F.u, P.hv u₁} : Set (Fin n → K)) := by
        intro h
        obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h
        have hb0 : b ≠ 0 := by
          intro h0
          rw [h0, zero_smul, add_zero] at hab
          apply P.span_inj F.hu F.hux hu₀ hu₀x (Ne.symm hu₀u)
          rw [← hab]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        apply hu₁_ind
        have h1 : P.hv u₁ = b⁻¹ • P.hv u₀ - (b⁻¹ * a) • P.hv F.u := by
          rw [← hab, smul_add]
          simp only [smul_smul]
          rw [inv_mul_cancel₀ hb0, one_smul]
          abel
        rw [h1]
        exact Submodule.sub_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      have C := step_cocycle P F.hw F.hwx F.h_irred
        F.hu F.hux F.hc F.hc_le F.hcu F.hcw
        hu₁ hu₁x hc₁ hc₁_le hc₁u hc₁w
        hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
        hu₁_not_u hu₀_not_uu₁
      rw [T2, T1, C, mul_assoc]
    · exact step_transport P F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu F.hcw
        hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w hu₀u.symm ht ht_le htx htw hvis htu₀w
        hcase

end LadderFrame


/-! ## The step's point system: injectivity and surjectivity -/

section LadderStep

variable {n : ℕ} {K : Type*} [DivisionRing K] {x : L}
variable {P : PointSys x n K} {w : L}

omit [ComplementedLattice L] in
theorem StepFrame.hv'_ne_zero (F : StepFrame P w) {t : L}
    (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) : F.hv' t ≠ 0 := by
  by_cases htx : t ≤ x
  · rw [F.hv'_of_le htx]
    exact ladder_snoc_ne_zero (Or.inl (P.ne_zero ht htx))
  · by_cases htw : t = w
    · rw [htw, F.hv'_w]
      exact ladder_snoc_ne_zero (Or.inr one_ne_zero)
    · rw [F.hv'_affine htx htw]
      have hb_atom : IsAtom (project w t x) :=
        ladder_trace_atom F.hw F.hwx F.hw le_sup_right ht ht_le htx htw
      exact ladder_snoc_ne_zero (Or.inl (P.ne_zero hb_atom inf_le_right))

omit [ComplementedLattice L] in
theorem StepFrame.lam_inj (F : StepFrame P w) {p q : L}
    (hp : IsAtom p) (hp_le : p ≤ x ⊔ w) (hpx : ¬ p ≤ x) (hpw : p ≠ w)
    (hq : IsAtom q) (hq_le : q ≤ x ⊔ w) (hqx : ¬ q ≤ x) (hqw : q ≠ w)
    (hbase : project w p x = project w q x) (hlam : F.lam p = F.lam q) :
    p = q := by
  have hb_atom : IsAtom (project w p x) :=
    ladder_trace_atom F.hw F.hwx F.hw le_sup_right hp hp_le hpx hpw
  have hb_x : project w p x ≤ x := inf_le_right
  by_cases hvis : p ≤ F.u ⊔ w
  · have hbase_p : project w p x = F.u :=
      (ladder_base_iff F.hw F.hwx hp hp_le hpx hpw F.hu F.hux).mpr hvis
    have hqvis : q ≤ F.u ⊔ w := by
      rw [← hbase_p, hbase]
      exact (ladder_regen F.hw F.hwx F.hw le_sup_right F.hwx hq hq_le hqx
        hqw).2
    have hp_mir : ¬ p ≤ F.u' ⊔ w := F.blind_not_mirror hp hpw hvis
    have hq_mir : ¬ q ≤ F.u' ⊔ w := F.blind_not_mirror hq hqw hqvis
    rw [F.lam_blind hvis, F.lam_blind hqvis] at hlam
    obtain ⟨hex, he_xw, _, _, _⟩ :=
      ladder_center F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu F.hew
    have hce_ne : stepRaw P w F.c F.u F.e ≠ 0 :=
      (stepRaw_exists P F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu F.hcw
        F.he he_xw hex F.hew F.e_not_primary).1
    have hraw_eq : stepRaw P w F.e F.u' p = stepRaw P w F.e F.u' q := by
      have h1 := neg_injective hlam
      exact mul_right_cancel₀ hce_ne h1
    obtain ⟨hrp_ne, αp, hαp, hsp⟩ :=
      stepRaw_exists P F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu F.hew
        hp hp_le hpx hpw hp_mir
    obtain ⟨hrq_ne, αq, hαq, hsq⟩ :=
      stepRaw_exists P F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu F.hew
        hq hq_le hqx hqw hq_mir
    rw [← hbase, ← hraw_eq] at hsq
    have hs_eq : project F.e p x = project F.e q x := by
      by_contra hne
      have hsp_atom : IsAtom (project F.e p x) :=
        ladder_trace_atom F.hw F.hwx F.he he_xw hp hp_le hpx
          (fun heq => hp_mir (heq ▸ F.he_le))
      have hsq_atom : IsAtom (project F.e q x) :=
        ladder_trace_atom F.hw F.hwx F.he he_xw hq hq_le hqx
          (fun heq => hq_mir (heq ▸ F.he_le))
      apply P.span_inj hsp_atom inf_le_right hsq_atom inf_le_right hne
      rw [hsq, hsp]
      have h2 : αq • P.hv (project w p x)
          + (αq * stepRaw P w F.e F.u' p) • P.hv F.u'
          = (αq * αp⁻¹) • (αp • P.hv (project w p x)
            + (αp * stepRaw P w F.e F.u' p) • P.hv F.u') := by
        simp only [smul_add, smul_smul]
        rw [mul_assoc αq αp⁻¹ αp, inv_mul_cancel₀ hαp, mul_one,
          mul_assoc αq αp⁻¹ _, ← mul_assoc αp⁻¹ αp _,
          inv_mul_cancel₀ hαp, one_mul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    calc p = (project w p x ⊔ w) ⊓ (project F.e p x ⊔ F.e) :=
          (ladder_recover F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu F.hew
            hp hp_le hpx hpw hp_mir).symm
      _ = (project w q x ⊔ w) ⊓ (project F.e q x ⊔ F.e) := by
          rw [hbase, hs_eq]
      _ = q := ladder_recover F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu
          F.hew hq hq_le hqx hqw hq_mir
  · have hqvis : ¬ q ≤ F.u ⊔ w := by
      intro h
      apply hvis
      have h1 := (ladder_base_iff F.hw F.hwx hq hq_le hqx hqw F.hu
        F.hux).mpr h
      rw [← hbase] at h1
      exact (ladder_base_iff F.hw F.hwx hp hp_le hpx hpw F.hu F.hux).mp h1
    rw [F.lam_visible hvis, F.lam_visible hqvis] at hlam
    obtain ⟨hrp_ne, αp, hαp, hsp⟩ :=
      stepRaw_exists P F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu F.hcw
        hp hp_le hpx hpw hvis
    obtain ⟨hrq_ne, αq, hαq, hsq⟩ :=
      stepRaw_exists P F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu F.hcw
        hq hq_le hqx hqw hqvis
    rw [← hbase, ← hlam] at hsq
    have hs_eq : project F.c p x = project F.c q x := by
      by_contra hne
      have hsp_atom : IsAtom (project F.c p x) :=
        ladder_trace_atom F.hw F.hwx F.hc
          (F.hc_le.trans (sup_le (F.hux.trans le_sup_left) le_sup_right))
          hp hp_le hpx (fun heq => hvis (heq ▸ F.hc_le))
      have hsq_atom : IsAtom (project F.c q x) :=
        ladder_trace_atom F.hw F.hwx F.hc
          (F.hc_le.trans (sup_le (F.hux.trans le_sup_left) le_sup_right))
          hq hq_le hqx (fun heq => hqvis (heq ▸ F.hc_le))
      apply P.span_inj hsp_atom inf_le_right hsq_atom inf_le_right hne
      rw [hsq, hsp]
      have h2 : αq • P.hv (project w p x)
          + (αq * stepRaw P w F.c F.u p) • P.hv F.u
          = (αq * αp⁻¹) • (αp • P.hv (project w p x)
            + (αp * stepRaw P w F.c F.u p) • P.hv F.u) := by
        simp only [smul_add, smul_smul]
        rw [mul_assoc αq αp⁻¹ αp, inv_mul_cancel₀ hαp, mul_one,
          mul_assoc αq αp⁻¹ _, ← mul_assoc αp⁻¹ αp _,
          inv_mul_cancel₀ hαp, one_mul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    calc p = (project w p x ⊔ w) ⊓ (project F.c p x ⊔ F.c) :=
          (ladder_recover F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu F.hcw
            hp hp_le hpx hpw hvis).symm
      _ = (project w q x ⊔ w) ⊓ (project F.c q x ⊔ F.c) := by
          rw [hbase, hs_eq]
      _ = q := ladder_recover F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu
          F.hcw hq hq_le hqx hqw hqvis

omit [ComplementedLattice L] in
theorem StepFrame.hv'_span_inj (F : StepFrame P w) {p q : L}
    (hp : IsAtom p) (hp_le : p ≤ x ⊔ w) (hq : IsAtom q) (hq_le : q ≤ x ⊔ w)
    (hpq : p ≠ q) : F.hv' q ∉ Submodule.span K {F.hv' p} := by
  intro hmem
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp hmem
  have hγ_ne : γ ≠ 0 := by
    intro h0
    apply F.hv'_ne_zero hq hq_le
    rw [← hγ, h0, zero_smul]
  by_cases hpx : p ≤ x
  · rw [F.hv'_of_le hpx, ladder_snoc_smul] at hγ
    by_cases hqx : q ≤ x
    · rw [F.hv'_of_le hqx] at hγ
      obtain ⟨h1, _⟩ := ladder_snoc_eq_iff.mp hγ.symm
      apply P.span_inj hp hpx hq hqx hpq
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · by_cases hqw : q = w
      · rw [hqw, F.hv'_w] at hγ
        obtain ⟨_, h2⟩ := ladder_snoc_eq_iff.mp hγ.symm
        rw [mul_zero] at h2
        exact one_ne_zero h2
      · rw [F.hv'_affine hqx hqw] at hγ
        obtain ⟨_, h2⟩ := ladder_snoc_eq_iff.mp hγ.symm
        rw [mul_zero] at h2
        exact F.lam_ne_zero hq hq_le hqx hqw h2
  · by_cases hpw : p = w
    · rw [hpw, F.hv'_w, ladder_snoc_smul, smul_zero, mul_one] at hγ
      by_cases hqx : q ≤ x
      · rw [F.hv'_of_le hqx] at hγ
        obtain ⟨h1, _⟩ := ladder_snoc_eq_iff.mp hγ.symm
        exact P.ne_zero hq hqx h1
      · by_cases hqw : q = w
        · exact hpq (hpw.trans hqw.symm)
        · rw [F.hv'_affine hqx hqw] at hγ
          obtain ⟨h1, _⟩ := ladder_snoc_eq_iff.mp hγ.symm
          have hb_atom : IsAtom (project w q x) :=
            ladder_trace_atom F.hw F.hwx F.hw le_sup_right hq hq_le hqx hqw
          exact P.ne_zero hb_atom inf_le_right h1
    · rw [F.hv'_affine hpx hpw, ladder_snoc_smul] at hγ
      have hbp_atom : IsAtom (project w p x) :=
        ladder_trace_atom F.hw F.hwx F.hw le_sup_right hp hp_le hpx hpw
      by_cases hqx : q ≤ x
      · rw [F.hv'_of_le hqx] at hγ
        obtain ⟨_, h2⟩ := ladder_snoc_eq_iff.mp hγ.symm
        rcases mul_eq_zero.mp h2.symm with h | h
        · exact hγ_ne h
        · exact F.lam_ne_zero hp hp_le hpx hpw h
      · by_cases hqw : q = w
        · rw [hqw, F.hv'_w] at hγ
          obtain ⟨h1, _⟩ := ladder_snoc_eq_iff.mp hγ.symm
          exact hγ_ne (ladder_smul_zero
            (P.ne_zero hbp_atom inf_le_right) h1.symm)
        · rw [F.hv'_affine hqx hqw] at hγ
          obtain ⟨h1, h2⟩ := ladder_snoc_eq_iff.mp hγ.symm
          have hbq_atom : IsAtom (project w q x) :=
            ladder_trace_atom F.hw F.hwx F.hw le_sup_right hq hq_le hqx hqw
          have hbase : project w q x = project w p x := by
            by_contra hne
            apply P.span_inj hbp_atom inf_le_right hbq_atom inf_le_right
              (fun h => hne h.symm)
            rw [h1]
            exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
          have hγ1 : γ = 1 := by
            have h3 : (1 - γ) • P.hv (project w p x) = 0 := by
              rw [sub_smul, one_smul, ← h1, hbase, sub_self]
            have h4 := ladder_smul_zero (P.ne_zero hbp_atom inf_le_right) h3
            rw [sub_eq_zero] at h4
            exact h4.symm
          rw [hγ1, one_mul] at h2
          exact hpq (F.lam_inj hp hp_le hpx hpw hq hq_le hqx hqw hbase.symm
            h2.symm)

omit [ComplementedLattice L] in
theorem StepFrame.hv'_span_surj (F : StepFrame P w)
    (v : Fin (n+1) → K) (hv_ne : v ≠ 0) :
    ∃ p : L, IsAtom p ∧ p ≤ x ⊔ w ∧
      Submodule.span K {F.hv' p} = Submodule.span K {v} := by
  have hsplit : (Fin.snoc (v ∘ Fin.castSucc) (v (Fin.last n)) :
      Fin (n+1) → K) = v := ladder_snoc_strip v
  by_cases hv₀ : v ∘ Fin.castSucc = 0
  · have hξ : v (Fin.last n) ≠ 0 := by
      intro h0
      apply hv_ne
      rw [← hsplit, hv₀, h0, ladder_snoc_zero]
    refine ⟨w, F.hw, le_sup_right, ?_⟩
    rw [F.hv'_w, ← hsplit, hv₀]
    have h1 : (Fin.snoc 0 (v (Fin.last n)) : Fin (n+1) → K)
        = v (Fin.last n) • Fin.snoc 0 1 := by
      rw [ladder_snoc_smul, smul_zero, mul_one]
    rw [h1, ladder_span_singleton_smul hξ]
  · obtain ⟨b, hb, hb_x, hb_span⟩ := P.span_surj _ hv₀
    have h1 : P.hv b ∈ Submodule.span K {v ∘ Fin.castSucc} := by
      rw [← hb_span]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨δ, hδ⟩ := Submodule.mem_span_singleton.mp h1
    have hδ_ne : δ ≠ 0 := fun h0 =>
      P.ne_zero hb hb_x (by rw [← hδ, h0, zero_smul])
    by_cases hξ : v (Fin.last n) = 0
    · refine ⟨b, hb, hb_x.trans le_sup_left, ?_⟩
      rw [F.hv'_of_le hb_x, ← hsplit, hξ, ← hδ]
      have h2 : (Fin.snoc (δ • (v ∘ Fin.castSucc)) 0 : Fin (n+1) → K)
          = δ • Fin.snoc (v ∘ Fin.castSucc) 0 := by
        rw [ladder_snoc_smul, mul_zero]
      rw [h2, ladder_span_singleton_smul hδ_ne]
    · have hδξ : δ * v (Fin.last n) ≠ 0 := mul_ne_zero hδ_ne hξ
      have hfinish : ∀ t : L, IsAtom t → t ≤ x ⊔ w → ¬ t ≤ x → t ≠ w →
          project w t x = b → F.lam t = δ * v (Fin.last n) →
          Submodule.span K {F.hv' t} = Submodule.span K {v} := by
        intro t ht ht_le htx htw hbase hlam
        rw [F.hv'_affine htx htw, hbase, hlam, ← hδ]
        have h3 : (Fin.snoc (δ • (v ∘ Fin.castSucc)) (δ * v (Fin.last n)) :
            Fin (n+1) → K) = δ • Fin.snoc (v ∘ Fin.castSucc) (v (Fin.last n)) :=
          (ladder_snoc_smul δ _ _).symm
        rw [h3, hsplit, ladder_span_singleton_smul hδ_ne]
      by_cases hbu : b = F.u
      · obtain ⟨hex, he_xw, _, _, _⟩ :=
          ladder_center F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu F.hew
        have hce_ne : stepRaw P w F.c F.u F.e ≠ 0 :=
          (stepRaw_exists P F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu F.hcw
            F.he he_xw hex F.hew F.e_not_primary).1
        have hρ_ne : -(δ * v (Fin.last n)) * (stepRaw P w F.c F.u F.e)⁻¹
            ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hδξ) (inv_ne_zero hce_ne)
        have hvs_ne : P.hv F.u
            + (-(δ * v (Fin.last n)) * (stepRaw P w F.c F.u F.e)⁻¹)
              • P.hv F.u' ≠ 0 :=
          ladder_comb_ne_zero (P.ne_zero F.hu F.hux) F.huu' _
        obtain ⟨s, hs, hs_x, hs_span⟩ := P.span_surj _ hvs_ne
        have h2 : P.hv s ∈ Submodule.span K {P.hv F.u
            + (-(δ * v (Fin.last n)) * (stepRaw P w F.c F.u F.e)⁻¹)
              • P.hv F.u'} := by
          rw [← hs_span]
          exact Submodule.mem_span_singleton_self _
        obtain ⟨ε, hε⟩ := Submodule.mem_span_singleton.mp h2
        have hε_ne : ε ≠ 0 := fun h0 =>
          P.ne_zero hs hs_x (by rw [← hε, h0, zero_smul])
        have hs_eq : P.hv s = ε • P.hv F.u
            + (ε * (-(δ * v (Fin.last n))
              * (stepRaw P w F.c F.u F.e)⁻¹)) • P.hv F.u' := by
          rw [← hε, smul_add, smul_smul]
        obtain ⟨hs_nu, hs_nu'⟩ := ladder_comb_not_mem
          (P.ne_zero F.hu F.hux) F.huu' hε_ne hρ_ne hs_eq
        have hs_ne_u : s ≠ F.u := fun h =>
          hs_nu (h ▸ Submodule.mem_span_singleton_self _)
        have hs_ne_u' : s ≠ F.u' := fun h =>
          hs_nu' (h ▸ Submodule.mem_span_singleton_self _)
        have hs_le : s ≤ F.u ⊔ F.u' :=
          (P.collinear_iff F.hu F.hux F.hu' F.hu'x hs hs_x F.u_ne_u').mpr
            (Submodule.mem_span_pair.mpr ⟨ε, ε * (-(δ * v (Fin.last n))
              * (stepRaw P w F.c F.u F.e)⁻¹), hs_eq.symm⟩)
        obtain ⟨t, ht, ht_le, htx, htw, htu', hbase, hshear⟩ :=
          ladder_reverse F.hw F.hwx F.hu' F.hu'x F.he F.he_le F.heu F.hew
            F.hu F.hux F.u_ne_u' hs hs_x hs_le hs_ne_u hs_ne_u'
        have hbase_b : project w t x = b := by rw [hbase, hbu]
        have hblind : t ≤ F.u ⊔ w := by
          rw [← hbu]
          exact (ladder_base_iff F.hw F.hwx ht ht_le htx htw
            (hbu ▸ F.hu) (hbu ▸ F.hux)).mp hbase_b
        have hraw : stepRaw P w F.e F.u' t
            = -(δ * v (Fin.last n)) * (stepRaw P w F.c F.u F.e)⁻¹ := by
          apply stepRaw_spec P (by rw [hbase]; exact P.ne_zero F.hu F.hux)
            (by rw [hbase]; exact F.huu') hε_ne
          rw [hshear, hbase]
          exact hs_eq
        refine ⟨t, ht, ht_le, hfinish t ht ht_le htx htw hbase_b ?_⟩
        rw [F.lam_blind hblind, hraw, mul_assoc,
          inv_mul_cancel₀ hce_ne, mul_one, neg_neg]
      · have hbu_ind : P.hv F.u ∉ Submodule.span K {P.hv b} :=
          P.span_inj hb hb_x F.hu F.hux hbu
        have hvs_ne : P.hv b + (δ * v (Fin.last n)) • P.hv F.u ≠ 0 :=
          ladder_comb_ne_zero (P.ne_zero hb hb_x) hbu_ind _
        obtain ⟨s, hs, hs_x, hs_span⟩ := P.span_surj _ hvs_ne
        have h2 : P.hv s ∈ Submodule.span K
            {P.hv b + (δ * v (Fin.last n)) • P.hv F.u} := by
          rw [← hs_span]
          exact Submodule.mem_span_singleton_self _
        obtain ⟨ε, hε⟩ := Submodule.mem_span_singleton.mp h2
        have hε_ne : ε ≠ 0 := fun h0 =>
          P.ne_zero hs hs_x (by rw [← hε, h0, zero_smul])
        have hs_eq : P.hv s = ε • P.hv b
            + (ε * (δ * v (Fin.last n))) • P.hv F.u := by
          rw [← hε, smul_add, smul_smul]
        obtain ⟨hs_nb, hs_nu⟩ := ladder_comb_not_mem
          (P.ne_zero hb hb_x) hbu_ind hε_ne hδξ hs_eq
        have hs_ne_b : s ≠ b := fun h =>
          hs_nb (h ▸ Submodule.mem_span_singleton_self _)
        have hs_ne_u : s ≠ F.u := fun h =>
          hs_nu (h ▸ Submodule.mem_span_singleton_self _)
        have hs_le : s ≤ b ⊔ F.u :=
          (P.collinear_iff hb hb_x F.hu F.hux hs hs_x hbu).mpr
            (Submodule.mem_span_pair.mpr
              ⟨ε, ε * (δ * v (Fin.last n)), hs_eq.symm⟩)
        obtain ⟨t, ht, ht_le, htx, htw, htu, hbase, hshear⟩ :=
          ladder_reverse F.hw F.hwx F.hu F.hux F.hc F.hc_le F.hcu F.hcw
            hb hb_x hbu hs hs_x hs_le hs_ne_b hs_ne_u
        have hraw : stepRaw P w F.c F.u t = δ * v (Fin.last n) := by
          apply stepRaw_spec P (by rw [hbase]; exact P.ne_zero hb hb_x)
            (by rw [hbase]; exact hbu_ind) hε_ne
          rw [hshear, hbase]
          exact hs_eq
        refine ⟨t, ht, ht_le, hfinish t ht ht_le htx htw hbase ?_⟩
        rw [F.lam_visible htu, hraw]

omit [ComplementedLattice L] in
theorem StepFrame.base_form (F : StepFrame P w) {t : L}
    (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htw : t ≠ w) :
    IsAtom (project w t x) ∧ project w t x ≤ x ∧ t ≤ project w t x ⊔ w ∧
      ∃ lt : K, F.hv' t = Fin.snoc (P.hv (project w t x)) lt := by
  by_cases htx : t ≤ x
  · have hbt : project w t x = t := by
      show (t ⊔ w) ⊓ x = t
      exact ladder_wline_trace F.hw F.hwx htx
    rw [hbt]
    exact ⟨ht, htx, le_sup_left, 0, F.hv'_of_le htx⟩
  · refine ⟨ladder_trace_atom F.hw F.hwx F.hw le_sup_right ht ht_le htx htw,
      inf_le_right,
      (ladder_regen F.hw F.hwx F.hw le_sup_right F.hwx ht ht_le htx htw).2,
      F.lam t, F.hv'_affine htx htw⟩

omit [ComplementedLattice L] in
theorem StepFrame.shear_form (F : StepFrame P w)
    {u₀ c₀ : L} (hu₀ : IsAtom u₀) (hu₀x : u₀ ≤ x)
    (hu₀_ind : P.hv u₀ ∉ Submodule.span K
      ({P.hv F.u, P.hv F.u'} : Set (Fin n → K)))
    (hc₀ : IsAtom c₀) (hc₀_le : c₀ ≤ u₀ ⊔ w) (hc₀u : c₀ ≠ u₀) (hc₀w : c₀ ≠ w)
    {t : L} (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htw : t ≠ w)
    (htu₀ : ¬ t ≤ u₀ ⊔ w)
    {lt : K} (hlt : F.hv' t = Fin.snoc (P.hv (project w t x)) lt) :
    IsAtom (project c₀ t x) ∧ project c₀ t x ≤ x ∧
      t ≤ project c₀ t x ⊔ c₀ ∧
      ∃ α : K, α ≠ 0 ∧ P.hv (project c₀ t x)
        = α • P.hv (project w t x)
          + (α * (lt * -(F.lam c₀)⁻¹)) • P.hv u₀ := by
  obtain ⟨hc₀x, hc₀_xw, _, _, _⟩ :=
    ladder_center F.hw F.hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
  by_cases htx : t ≤ x
  · have hbt : project w t x = t := by
      show (t ⊔ w) ⊓ x = t
      exact ladder_wline_trace F.hw F.hwx htx
    have hst : project c₀ t x = t := by
      show (t ⊔ c₀) ⊓ x = t
      exact ladder_line_trace htx hc₀ hc₀x
    have hlt0 : lt = 0 := by
      rw [F.hv'_of_le htx, hbt] at hlt
      exact (ladder_snoc_eq_iff.mp hlt).2.symm
    rw [hst, hbt, hlt0]
    refine ⟨ht, htx, le_sup_left, 1, one_ne_zero, ?_⟩
    rw [zero_mul, mul_zero, zero_smul, add_zero, one_smul]
  · have hlam : lt = F.lam t := by
      rw [F.hv'_affine htx htw] at hlt
      exact (ladder_snoc_eq_iff.mp hlt).2.symm
    have htc₀ : t ≠ c₀ := fun heq => htu₀ (heq ▸ hc₀_le)
    obtain ⟨_, α, hα, heq⟩ :=
      stepRaw_exists P F.hw F.hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
        ht ht_le htx htw htu₀
    have hcentral := F.central hu₀ hu₀x hu₀_ind hc₀ hc₀_le hc₀u hc₀w
      ht ht_le htx htw htu₀
    rw [hcentral] at heq
    rw [hlam]
    exact ⟨ladder_trace_atom F.hw F.hwx hc₀ hc₀_xw ht ht_le htx htc₀,
      inf_le_right,
      (ladder_regen F.hw F.hwx hc₀ hc₀_xw hc₀x ht ht_le htx htc₀).2,
      α, hα, heq⟩

omit [ComplementedLattice L] in
theorem StepFrame.collinear_w (F : StepFrame P w) {p r : L}
    (hp : IsAtom p) (hp_le : p ≤ x ⊔ w) (hpw : p ≠ w)
    (hr : IsAtom r) (hr_le : r ≤ x ⊔ w) :
    r ≤ p ⊔ w ↔ F.hv' r ∈ Submodule.span K
      ({F.hv' p, F.hv' w} : Set (Fin (n+1) → K)) := by
  obtain ⟨hbp_atom, hbp_x, hp_line, lp, hp_form⟩ := F.base_form hp hp_le hpw
  have hline : p ⊔ w = project w p x ⊔ w := by
    apply le_antisymm
    · exact sup_le hp_line le_sup_right
    · exact sup_le ((inf_le_left : project w p x ≤ p ⊔ w)) le_sup_right
  constructor
  · intro hr_pw
    by_cases hrw : r = w
    · rw [hrw]
      exact Submodule.subset_span
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · obtain ⟨hbr_atom, hbr_x, hr_line, lr, hr_form⟩ := F.base_form hr hr_le hrw
      have hbr : project w r x = project w p x := by
        have h1 : project w r x ≤ project w p x := by
          have h2 : (r ⊔ w) ⊓ x ≤ (project w p x ⊔ w) ⊓ x :=
            inf_le_inf_right x (sup_le (hr_pw.trans hline.le) le_sup_right)
          rwa [ladder_wline_trace F.hw F.hwx hbp_x] at h2
        exact IsAtom.eq_of_le hbr_atom hbp_atom h1
      refine Submodule.mem_span_pair.mpr ⟨1, lr - lp, ?_⟩
      rw [hp_form, F.hv'_w, hr_form, hbr, ladder_snoc_comb, one_smul,
        smul_zero, add_zero, one_mul, mul_one]
      congr 1
      abel
  · intro hmem
    by_cases hrw : r = w
    · rw [hrw]
      exact le_sup_right
    · obtain ⟨hbr_atom, hbr_x, hr_line, lr, hr_form⟩ := F.base_form hr hr_le hrw
      obtain ⟨z₁, z₂, hz⟩ := Submodule.mem_span_pair.mp hmem
      rw [hp_form, F.hv'_w, ladder_snoc_comb, hr_form] at hz
      obtain ⟨h1, _⟩ := ladder_snoc_eq_iff.mp hz
      rw [smul_zero, add_zero] at h1
      have hz₁ : z₁ ≠ 0 := by
        intro h0
        apply P.ne_zero hbr_atom hbr_x
        rw [← h1, h0, zero_smul]
      have hbr : project w r x = project w p x := by
        by_contra hne
        apply P.span_inj hbp_atom hbp_x hbr_atom hbr_x (fun h => hne h.symm)
        rw [← h1]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      calc r ≤ project w r x ⊔ w := hr_line
        _ = project w p x ⊔ w := by rw [hbr]
        _ = p ⊔ w := hline.symm

omit [ComplementedLattice L] in
theorem StepFrame.wline_eq (F : StepFrame P w) {t : L}
    (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htw : t ≠ w) :
    t ⊔ w = project w t x ⊔ w := by
  obtain ⟨_, _, ht_line, _, _⟩ := F.base_form (K := K) ht ht_le htw
  exact le_antisymm (sup_le ht_line le_sup_right)
    (sup_le (inf_le_left : project w t x ≤ t ⊔ w) le_sup_right)

omit [ComplementedLattice L] in
theorem StepFrame.main_setup (F : StepFrame P w) {p q : L}
    (hp : IsAtom p) (hp_le : p ≤ x ⊔ w) (hpw : p ≠ w)
    (hq : IsAtom q) (hq_le : q ≤ x ⊔ w) (hqw : q ≠ w) (hpq : p ≠ q)
    (hbase_ne : project w p x ≠ project w q x) :
    ¬ w ≤ p ⊔ q ∧ p ⊔ q ⊔ w = project w p x ⊔ project w q x ⊔ w ∧
      (p ⊔ q ⊔ w) ⊓ x = project w p x ⊔ project w q x := by
  obtain ⟨hbp_atom, hbp_x, hp_line, lp, hp_form⟩ :=
    F.base_form (K := K) hp hp_le hpw
  obtain ⟨hbq_atom, hbq_x, hq_line, lq, hq_form⟩ :=
    F.base_form (K := K) hq hq_le hqw
  have hw_pq : ¬ w ≤ p ⊔ q := by
    intro h
    apply hbase_ne
    have h1 : p ⊔ q = p ⊔ w := line_eq_of_atom_le hp hq F.hw hpq hpw hqw h
    have h2 : q ≤ project w p x ⊔ w := by
      calc q ≤ p ⊔ q := le_sup_right
        _ = p ⊔ w := h1
        _ = project w p x ⊔ w := F.wline_eq hp hp_le hpw
    have h3 : project w q x ≤ project w p x := by
      have h4 : (q ⊔ w) ⊓ x ≤ (project w p x ⊔ w) ⊓ x :=
        inf_le_inf_right x (sup_le h2 le_sup_right)
      rwa [ladder_wline_trace F.hw F.hwx hbp_x] at h4
    exact (IsAtom.eq_of_le hbq_atom hbp_atom h3).symm
  have hPQ : p ⊔ q ⊔ w = project w p x ⊔ project w q x ⊔ w := by
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · exact hp_line.trans (sup_le
          (le_sup_left.trans le_sup_left) le_sup_right)
      · exact hq_line.trans (sup_le
          (le_sup_right.trans le_sup_left) le_sup_right)
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · exact (inf_le_left : project w p x ≤ p ⊔ w).trans
          (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      · exact (inf_le_left : project w q x ≤ q ⊔ w).trans
          (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  refine ⟨hw_pq, hPQ, ?_⟩
  rw [hPQ]
  exact ladder_wline_trace F.hw F.hwx (sup_le hbp_x hbq_x)

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem StepFrame.shear_ne (F : StepFrame P w) {p q u₀ c₀ : L}
    (hu₀_pq : P.hv u₀ ∉ Submodule.span K
      ({P.hv (project w p x), P.hv (project w q x)} : Set (Fin n → K)))
    (hbp_ne : P.hv (project w p x) ≠ 0)
    (hbq_ind : P.hv (project w q x) ∉
      Submodule.span K {P.hv (project w p x)})
    {lp lq : K} {αp αq : K} (hαp : αp ≠ 0) (_hαq : αq ≠ 0)
    (hsp : P.hv (project c₀ p x) = αp • P.hv (project w p x)
      + (αp * (lp * -(F.lam c₀)⁻¹)) • P.hv u₀)
    (hsq : P.hv (project c₀ q x) = αq • P.hv (project w q x)
      + (αq * (lq * -(F.lam c₀)⁻¹)) • P.hv u₀) :
    project c₀ p x ≠ project c₀ q x := by
  intro heq
  have h1 : P.hv (project c₀ p x) = P.hv (project c₀ q x) := by rw [heq]
  rw [hsp, hsq] at h1
  have h2 : (αp * (lp * -(F.lam c₀)⁻¹)) • P.hv u₀
      + αp • P.hv (project w p x) + (0 : K) • P.hv (project w q x)
      = (αq * (lq * -(F.lam c₀)⁻¹)) • P.hv u₀
        + (0 : K) • P.hv (project w p x)
        + αq • P.hv (project w q x) := by
    rw [zero_smul, zero_smul, add_zero, add_zero,
      add_comm ((αp * (lp * -(F.lam c₀)⁻¹)) • P.hv u₀)
        (αp • P.hv (project w p x)),
      add_comm ((αq * (lq * -(F.lam c₀)⁻¹)) • P.hv u₀)
        (αq • P.hv (project w q x))]
    exact h1
  obtain ⟨_, h3, _⟩ := ladder_triple_unique hbp_ne hbq_ind hu₀_pq h2
  exact hαp h3

omit [ComplementedLattice L] in
theorem StepFrame.collinear_main (F : StepFrame P w) {p q r : L}
    (hp : IsAtom p) (hp_le : p ≤ x ⊔ w) (hpw : p ≠ w)
    (hq : IsAtom q) (hq_le : q ≤ x ⊔ w) (hqw : q ≠ w) (hpq : p ≠ q)
    (hr : IsAtom r) (hr_le : r ≤ x ⊔ w)
    (hbase_ne : project w p x ≠ project w q x) :
    r ≤ p ⊔ q ↔ F.hv' r ∈ Submodule.span K
      ({F.hv' p, F.hv' q} : Set (Fin (n+1) → K)) := by
  obtain ⟨hbp_atom, hbp_x, hp_line, lp, hp_form⟩ :=
    F.base_form (K := K) hp hp_le hpw
  obtain ⟨hbq_atom, hbq_x, hq_line, lq, hq_form⟩ :=
    F.base_form (K := K) hq hq_le hqw
  obtain ⟨hw_pq, hPQ, htrace⟩ := F.main_setup hp hp_le hpw hq hq_le hqw hpq
    hbase_ne
  have hbp_ne : P.hv (project w p x) ≠ 0 := P.ne_zero hbp_atom hbp_x
  have hbq_ind : P.hv (project w q x) ∉
      Submodule.span K {P.hv (project w p x)} :=
    P.span_inj hbp_atom hbp_x hbq_atom hbq_x hbase_ne
  obtain ⟨v₀, hv₀a, hv₀b⟩ := ladder_avoid_two F.hn
    (P.hv (project w p x)) (P.hv (project w q x)) (P.hv F.u) (P.hv F.u')
  have hv₀_ne : v₀ ≠ 0 := fun h => hv₀a (h ▸ Submodule.zero_mem _)
  obtain ⟨u₀, hu₀, hu₀x, hu₀_span⟩ := P.span_surj v₀ hv₀_ne
  have hu₀_of : ∀ (a b : Fin n → K),
      v₀ ∉ Submodule.span K ({a, b} : Set (Fin n → K)) →
      P.hv u₀ ∉ Submodule.span K ({a, b} : Set (Fin n → K)) := by
    intro a b hv₀m hmem
    apply hv₀m
    have h1 : v₀ ∈ Submodule.span K {P.hv u₀} := by
      rw [hu₀_span]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨δ, hδ⟩ := Submodule.mem_span_singleton.mp h1
    rw [← hδ]
    exact Submodule.smul_mem _ _ hmem
  have hu₀_pq := hu₀_of _ _ hv₀a
  have hu₀_ind := hu₀_of _ _ hv₀b
  have hu₀w : u₀ ≠ w := fun h => F.hwx (h ▸ hu₀x)
  obtain ⟨c₀, hc₀, hc₀_le, hc₀u, hc₀w⟩ := F.h_irred u₀ w hu₀ F.hw hu₀w
  obtain ⟨hc₀x, hc₀_xw, hline₀, hline₀', hbase₀⟩ :=
    ladder_center F.hw F.hwx hu₀ hu₀x hc₀ hc₀_le hc₀u hc₀w
  have hlamc₀ : F.lam c₀ ≠ 0 := F.lam_ne_zero hc₀ hc₀_xw hc₀x hc₀w
  have hg_ne : -(F.lam c₀)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hlamc₀)
  have hbase_of : ∀ {t : L}, IsAtom (project w t x) → t ≤ u₀ ⊔ w →
      project w t x = u₀ := by
    intro t hbt h
    have h1 : project w t x ≤ u₀ := by
      have h2 : (t ⊔ w) ⊓ x ≤ (u₀ ⊔ w) ⊓ x :=
        inf_le_inf_right x (sup_le h le_sup_right)
      rwa [ladder_wline_trace F.hw F.hwx hu₀x] at h2
    exact IsAtom.eq_of_le hbt hu₀ h1
  have htu₀p : ¬ p ≤ u₀ ⊔ w := by
    intro h
    apply hu₀_pq
    rw [← hbase_of hbp_atom h]
    exact Submodule.subset_span (Set.mem_insert _ _)
  have htu₀q : ¬ q ≤ u₀ ⊔ w := by
    intro h
    apply hu₀_pq
    rw [← hbase_of hbq_atom h]
    exact Submodule.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨hsp_atom, hsp_x, hp_sline, αp, hαp, hsp⟩ :=
    F.shear_form hu₀ hu₀x hu₀_ind hc₀ hc₀_le hc₀u hc₀w hp hp_le hpw htu₀p
      hp_form
  obtain ⟨hsq_atom, hsq_x, hq_sline, αq, hαq, hsq⟩ :=
    F.shear_form hu₀ hu₀x hu₀_ind hc₀ hc₀_le hc₀u hc₀w hq hq_le hqw htu₀q
      hq_form
  have hs_ne : project c₀ p x ≠ project c₀ q x :=
    F.shear_ne hu₀_pq hbp_ne hbq_ind hαp hαq hsp hsq
  have hQ_eq : p ⊔ q ⊔ c₀ = project c₀ p x ⊔ project c₀ q x ⊔ c₀ := by
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · exact hp_sline.trans (sup_le
          (le_sup_left.trans le_sup_left) le_sup_right)
      · exact hq_sline.trans (sup_le
          (le_sup_right.trans le_sup_left) le_sup_right)
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · exact (inf_le_left : project c₀ p x ≤ p ⊔ c₀).trans
          (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      · exact (inf_le_left : project c₀ q x ≤ q ⊔ c₀).trans
          (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hQ_trace : (p ⊔ q ⊔ c₀) ⊓ x = project c₀ p x ⊔ project c₀ q x := by
    rw [hQ_eq]
    exact ladder_line_trace (sup_le hsp_x hsq_x) hc₀ hc₀x
  constructor
  · intro hr_pq
    have hrw : r ≠ w := fun h => hw_pq (h ▸ hr_pq)
    obtain ⟨hbr_atom, hbr_x, hr_line, lr, hr_form⟩ :=
      F.base_form (K := K) hr hr_le hrw
    have hbr_le : project w r x ≤ project w p x ⊔ project w q x := by
      have h1 : (r ⊔ w) ⊓ x ≤ (p ⊔ q ⊔ w) ⊓ x :=
        inf_le_inf_right x (sup_le (hr_pq.trans le_sup_left) le_sup_right)
      rwa [htrace] at h1
    have htu₀r : ¬ r ≤ u₀ ⊔ w := by
      intro h
      apply hu₀_pq
      rw [← hbase_of hbr_atom h]
      exact (P.collinear_iff hbp_atom hbp_x hbq_atom hbq_x hbr_atom hbr_x
        hbase_ne).mp hbr_le
    obtain ⟨hsr_atom, hsr_x, hr_sline, αr, hαr, hsr⟩ :=
      F.shear_form hu₀ hu₀x hu₀_ind hc₀ hc₀_le hc₀u hc₀w hr hr_le hrw htu₀r
        hr_form
    obtain ⟨ξ, η, hξη⟩ := Submodule.mem_span_pair.mp
      ((P.collinear_iff hbp_atom hbp_x hbq_atom hbq_x hbr_atom hbr_x
        hbase_ne).mp hbr_le)
    have hsr_le : project c₀ r x ≤ project c₀ p x ⊔ project c₀ q x := by
      have h1 : (r ⊔ c₀) ⊓ x ≤ (p ⊔ q ⊔ c₀) ⊓ x :=
        inf_le_inf_right x (sup_le (hr_pq.trans le_sup_left) le_sup_right)
      rwa [hQ_trace] at h1
    have hmem_s : P.hv (project c₀ r x) ∈ Submodule.span K
        ({P.hv (project c₀ p x), P.hv (project c₀ q x)} :
          Set (Fin n → K)) :=
      (P.collinear_iff hsp_atom hsp_x hsq_atom hsq_x hsr_atom hsr_x
        hs_ne).mp hsr_le
    have hsr' : P.hv (project c₀ r x)
        = αr • (ξ • P.hv (project w p x) + η • P.hv (project w q x))
          + (αr * (lr * -(F.lam c₀)⁻¹)) • P.hv u₀ := by
      rw [hsr, hξη]
    have hlr : lr = ξ * lp + η * lq :=
      ladder_graph_comb hbp_ne hbq_ind hu₀_pq hg_ne hαr hsp hsq hsr' hmem_s
    refine Submodule.mem_span_pair.mpr ⟨ξ, η, ?_⟩
    rw [hp_form, hq_form, hr_form, ladder_snoc_comb, hξη, hlr]
  · intro hmem
    have hrw : r ≠ w := by
      intro h
      rw [h, F.hv'_w, hp_form, hq_form] at hmem
      obtain ⟨z₁, z₂, hz⟩ := Submodule.mem_span_pair.mp hmem
      rw [ladder_snoc_comb] at hz
      obtain ⟨h1, h2⟩ := ladder_snoc_eq_iff.mp hz
      obtain ⟨hz₁, hz₂⟩ := ladder_pair_zero hbp_ne hbq_ind h1
      rw [hz₁, hz₂, zero_mul, zero_mul, add_zero] at h2
      exact one_ne_zero h2.symm
    obtain ⟨hbr_atom, hbr_x, hr_line, lr, hr_form⟩ :=
      F.base_form (K := K) hr hr_le hrw
    obtain ⟨z₁, z₂, hz⟩ := Submodule.mem_span_pair.mp hmem
    rw [hp_form, hq_form, hr_form, ladder_snoc_comb] at hz
    obtain ⟨h_first, h_last⟩ := ladder_snoc_eq_iff.mp hz
    have htu₀r : ¬ r ≤ u₀ ⊔ w := by
      intro h
      apply hu₀_pq
      rw [← hbase_of hbr_atom h, ← h_first]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.smul_mem _ _ (Submodule.subset_span
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    obtain ⟨hsr_atom, hsr_x, hr_sline, αr, hαr, hsr⟩ :=
      F.shear_form hu₀ hu₀x hu₀_ind hc₀ hc₀_le hc₀u hc₀w hr hr_le hrw htu₀r
        hr_form
    have hbr_le : project w r x ≤ project w p x ⊔ project w q x :=
      (P.collinear_iff hbp_atom hbp_x hbq_atom hbq_x hbr_atom hbr_x
        hbase_ne).mpr (Submodule.mem_span_pair.mpr ⟨z₁, z₂, h_first⟩)
    have hmem_s : P.hv (project c₀ r x) ∈ Submodule.span K
        ({P.hv (project c₀ p x), P.hv (project c₀ q x)} :
          Set (Fin n → K)) :=
      ladder_conv_transfer hαp hαq hsp hsq hsr h_first.symm h_last.symm
    have hsr_le : project c₀ r x ≤ project c₀ p x ⊔ project c₀ q x :=
      (P.collinear_iff hsp_atom hsp_x hsq_atom hsq_x hsr_atom hsr_x
        hs_ne).mpr hmem_s
    have hr_P : r ≤ p ⊔ q ⊔ w := by
      calc r ≤ project w r x ⊔ w := hr_line
        _ ≤ (project w p x ⊔ project w q x) ⊔ w :=
            sup_le (hbr_le.trans le_sup_left) le_sup_right
        _ = p ⊔ q ⊔ w := by rw [hPQ]
    have hr_Q : r ≤ p ⊔ q ⊔ c₀ := by
      calc r ≤ project c₀ r x ⊔ c₀ := hr_sline
        _ ≤ (project c₀ p x ⊔ project c₀ q x) ⊔ c₀ :=
            sup_le (hsr_le.trans le_sup_left) le_sup_right
        _ = p ⊔ q ⊔ c₀ := by rw [hQ_eq]
    have hcov : p ⊔ q ⋖ p ⊔ q ⊔ w := covBy_sup_atom F.hw hw_pq
    have hne_PQ : ¬ p ⊔ q ⊔ w ≤ p ⊔ q ⊔ c₀ := by
      intro hle
      have hw_Q : w ≤ p ⊔ q ⊔ c₀ := le_sup_right.trans hle
      have hu₀_Q : u₀ ≤ p ⊔ q ⊔ c₀ := by
        have h1 : u₀ ≤ c₀ ⊔ w := by
          rw [hline₀']
          exact le_sup_left
        exact h1.trans (sup_le le_sup_right hw_Q)
      have hu₀_ss : u₀ ≤ project c₀ p x ⊔ project c₀ q x := by
        have h1 : u₀ ≤ (p ⊔ q ⊔ c₀) ⊓ x := le_inf hu₀_Q hu₀x
        rwa [hQ_trace] at h1
      have hmem_u₀ : P.hv u₀ ∈ Submodule.span K
          ({P.hv (project c₀ p x), P.hv (project c₀ q x)} :
            Set (Fin n → K)) :=
        (P.collinear_iff hsp_atom hsp_x hsq_atom hsq_x hu₀ hu₀x hs_ne).mp
          hu₀_ss
      obtain ⟨y₁, y₂, hy⟩ := Submodule.mem_span_pair.mp hmem_u₀
      have h11 : (y₁ * (αp * (lp * -(F.lam c₀)⁻¹))
            + y₂ * (αq * (lq * -(F.lam c₀)⁻¹))) • P.hv u₀
          + (y₁ * αp) • P.hv (project w p x)
          + (y₂ * αq) • P.hv (project w q x)
          = y₁ • P.hv (project c₀ p x) + y₂ • P.hv (project c₀ q x) := by
        rw [hsp, hsq, add_smul]
        simp only [smul_add, smul_smul]
        abel
      have h12 : (y₁ * (αp * (lp * -(F.lam c₀)⁻¹))
            + y₂ * (αq * (lq * -(F.lam c₀)⁻¹))) • P.hv u₀
          + (y₁ * αp) • P.hv (project w p x)
          + (y₂ * αq) • P.hv (project w q x)
          = (1 : K) • P.hv u₀ + (0 : K) • P.hv (project w p x)
            + (0 : K) • P.hv (project w q x) := by
        rw [one_smul, zero_smul, zero_smul, add_zero, add_zero]
        exact h11.trans hy
      obtain ⟨h_one, hy₁, hy₂⟩ := ladder_triple_unique hbp_ne hbq_ind
        hu₀_pq h12
      have hy₁0 : y₁ = 0 := by
        rcases mul_eq_zero.mp hy₁ with h | h
        · exact h
        · exact absurd h hαp
      have hy₂0 : y₂ = 0 := by
        rcases mul_eq_zero.mp hy₂ with h | h
        · exact h
        · exact absurd h hαq
      rw [hy₁0, hy₂0, zero_mul, zero_mul, add_zero] at h_one
      exact zero_ne_one h_one
    rcases hcov.eq_or_eq (le_inf le_sup_left le_sup_left)
      (inf_le_left : (p ⊔ q ⊔ w) ⊓ (p ⊔ q ⊔ c₀) ≤ p ⊔ q ⊔ w) with hm | hm
    · rw [← hm]
      exact le_inf hr_P hr_Q
    · exfalso
      apply hne_PQ
      rw [← hm]
      exact inf_le_right

omit [ComplementedLattice L] in
theorem StepFrame.hv'_collinear_iff (F : StepFrame P w) {p q r : L}
    (hp : IsAtom p) (hp_le : p ≤ x ⊔ w) (hq : IsAtom q) (hq_le : q ≤ x ⊔ w)
    (hr : IsAtom r) (hr_le : r ≤ x ⊔ w) (hpq : p ≠ q) :
    r ≤ p ⊔ q ↔ F.hv' r ∈ Submodule.span K
      ({F.hv' p, F.hv' q} : Set (Fin (n+1) → K)) := by
  by_cases hqw : q = w
  · rw [hqw]
    exact F.collinear_w hp hp_le (fun h => hpq (h.trans hqw.symm)) hr hr_le
  by_cases hpw : p = w
  · rw [hpw, sup_comm w q, Set.pair_comm (F.hv' w) (F.hv' q)]
    exact F.collinear_w hq hq_le hqw hr hr_le
  by_cases hbase : project w p x = project w q x
  · obtain ⟨hbp_atom, hbp_x, hp_line, lp, hp_form⟩ :=
      F.base_form (K := K) hp hp_le hpw
    obtain ⟨hbq_atom, hbq_x, hq_line, lq, hq_form⟩ :=
      F.base_form (K := K) hq hq_le hqw
    have hq_pw : q ≤ p ⊔ w := by
      calc q ≤ project w q x ⊔ w := hq_line
        _ = project w p x ⊔ w := by rw [hbase]
        _ = p ⊔ w := (F.wline_eq hp hp_le hpw).symm
    have hline : p ⊔ w = p ⊔ q :=
      line_eq_of_atom_le hp F.hw hq hpw hpq (fun h => hqw h.symm) hq_pw
    have hlam_ne : lp ≠ lq := by
      intro h
      apply F.hv'_span_inj hp hp_le hq hq_le hpq
      rw [hq_form, hp_form, ← hbase, ← h]
      exact Submodule.mem_span_singleton_self _
    have hspan_eq : Submodule.span K
        ({F.hv' p, F.hv' q} : Set (Fin (n+1) → K))
        = Submodule.span K ({F.hv' p, F.hv' w} : Set (Fin (n+1) → K)) := by
      rw [hp_form, hq_form, ← hbase, F.hv'_w]
      exact ladder_span_swap_last hlam_ne
    rw [← hline, hspan_eq]
    exact F.collinear_w hp hp_le hpw hr hr_le
  · exact F.collinear_main hp hp_le hpw hq hq_le hqw hpq hr hr_le hbase

omit [ComplementedLattice L] in
noncomputable def StepFrame.toPointSys (F : StepFrame P w) :
    PointSys (x ⊔ w) (n+1) K where
  hv := F.hv'
  ne_zero := fun hp hp_le => F.hv'_ne_zero hp hp_le
  span_inj := fun hp hp_le hq hq_le hpq =>
    F.hv'_span_inj hp hp_le hq hq_le hpq
  span_surj := F.hv'_span_surj
  collinear_iff := fun hp hp_le hq hq_le hr hr_le hpq =>
    F.hv'_collinear_iff hp hp_le hq hq_le hr hr_le hpq

omit [ComplementedLattice L] in
theorem StepFrame.toPointSys_of_le (F : StepFrame P w) {p : L} (h : p ≤ x) :
    F.toPointSys.hv p = Fin.snoc (P.hv p) 0 :=
  F.hv'_of_le h

omit [ComplementedLattice L] in
theorem StepFrame.toPointSys_w (F : StepFrame P w) :
    F.toPointSys.hv w = Fin.snoc 0 1 :=
  F.hv'_w

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem stepFrame_exists {x : L} {n : ℕ} {K : Type*} [DivisionRing K]
    (P : PointSys x n K) {w : L} (hn : 3 ≤ n)
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (hw : IsAtom w) (hwx : ¬ w ≤ x) :
    Nonempty (StepFrame P w) := by
  have hone : (1 : Fin n → K) ≠ 0 := by
    intro h
    have h1 := congrFun h ⟨0, by omega⟩
    exact one_ne_zero h1
  obtain ⟨u, hu, hux, hu_span⟩ := P.span_surj 1 hone
  obtain ⟨v', hv'a, _⟩ := ladder_avoid_two hn (P.hv u) (P.hv u)
    (P.hv u) (P.hv u)
  have hv'_ne : v' ≠ 0 := fun h => hv'a (h ▸ Submodule.zero_mem _)
  obtain ⟨u', hu', hu'x, hu'_span⟩ := P.span_surj v' hv'_ne
  have huu' : P.hv u' ∉ Submodule.span K {P.hv u} := by
    intro h
    apply hv'a
    have h1 : v' ∈ Submodule.span K {P.hv u'} := by
      rw [hu'_span]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨δ, hδ⟩ := Submodule.mem_span_singleton.mp h1
    rw [← hδ]
    apply Submodule.smul_mem
    rw [Set.pair_eq_singleton]
    exact h
  have huw : u ≠ w := fun h => hwx (h ▸ hux)
  have hu'w : u' ≠ w := fun h => hwx (h ▸ hu'x)
  obtain ⟨c, hc, hc_le, hcu, hcw⟩ := h_irred u w hu hw huw
  obtain ⟨e, he, he_le, heu, hew⟩ := h_irred u' w hu' hw hu'w
  exact ⟨⟨hn, h_irred, hw, hwx, u, hu, hux, u', hu', hu'x, huu',
    c, hc, hc_le, hcu, hcw, e, he, he_le, heu, hew⟩⟩

omit [ComplementedLattice L] in
theorem PointSys.step {x : L} {n : ℕ} {K : Type*} [DivisionRing K]
    (P : PointSys x n K) {w : L} (hn : 3 ≤ n)
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (hw : IsAtom w) (hwx : ¬ w ≤ x) :
    ∃ Q : PointSys (x ⊔ w) (n+1) K,
      (∀ p : L, p ≤ x → Q.hv p = Fin.snoc (P.hv p) 0) ∧
      Q.hv w = Fin.snoc 0 1 := by
  obtain ⟨F⟩ := stepFrame_exists P hn h_irred hw hwx
  exact ⟨F.toPointSys, fun p hp => F.toPointSys_of_le hp, F.toPointSys_w⟩

end LadderStep


end Foam.Bridges

/-! ## Axiom audit -/

/-- info: 'Foam.Bridges.PointSys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.PointSys

/-- info: 'Foam.Bridges.ladder_trace_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_trace_atom

/-- info: 'Foam.Bridges.ladder_regen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_regen

/-- info: 'Foam.Bridges.ladder_wline_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_wline_trace

/-- info: 'Foam.Bridges.ladder_base_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_base_iff

/-- info: 'Foam.Bridges.ladder_center' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_center

/-- info: 'Foam.Bridges.ladder_axis_inf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_axis_inf

/-- info: 'Foam.Bridges.ladder_line_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_line_trace

/-- info: 'Foam.Bridges.ladder_shear_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_shear_le

/-- info: 'Foam.Bridges.ladder_shear_ne_axis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_shear_ne_axis

/-- info: 'Foam.Bridges.ladder_shear_ne_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_shear_ne_base

/-- info: 'Foam.Bridges.ladder_recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_recover

/-- info: 'Foam.Bridges.ladder_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_bridge

/-- info: 'Foam.Bridges.ladder_shadow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_shadow

/-- info: 'Foam.Bridges.ladder_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_reverse

/-- info: 'Foam.Bridges.ladder_smul_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_smul_zero

/-- info: 'Foam.Bridges.ladder_pair_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_pair_zero

/-- info: 'Foam.Bridges.ladder_triple_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_triple_zero

/-- info: 'Foam.Bridges.ladder_triple_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_triple_unique

/-- info: 'Foam.Bridges.ladder_pair_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_pair_unique

/-- info: 'Foam.Bridges.ladder_span_pair_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_span_pair_ne_top

/-- info: 'Foam.Bridges.ladder_avoid_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_avoid_two

/-- info: 'Foam.Bridges.ladder_span_dodge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_span_dodge

/-- info: 'Foam.Bridges.ladder_pair_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_pair_swap

/-- info: 'Foam.Bridges.ladder_pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_pin

/-- info: 'Foam.Bridges.ladder_graph_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_graph_comb

/-- info: 'Foam.Bridges.ladder_conv_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_conv_transfer

/-- info: 'Foam.Bridges.ladder_snoc_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_snoc_add

/-- info: 'Foam.Bridges.ladder_snoc_smul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_snoc_smul

/-- info: 'Foam.Bridges.ladder_snoc_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_snoc_zero

/-- info: 'Foam.Bridges.ladder_snoc_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_snoc_eq_iff

/-- info: 'Foam.Bridges.ladder_snoc_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_snoc_ne_zero

/-- info: 'Foam.Bridges.ladder_snoc_comb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_snoc_comb

/-- info: 'Foam.Bridges.ladder_snoc_strip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_snoc_strip

/-- info: 'Foam.Bridges.ladder_span_singleton_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_span_singleton_smul

/-- info: 'Foam.Bridges.ladder_comb_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_comb_ne_zero

/-- info: 'Foam.Bridges.ladder_comb_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_comb_not_mem

/-- info: 'Foam.Bridges.ladder_span_swap_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ladder_span_swap_last

/-- info: 'Foam.Bridges.stepRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.stepRaw

/-- info: 'Foam.Bridges.stepRaw_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.stepRaw_spec

/-- info: 'Foam.Bridges.stepRaw_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.stepRaw_exists

/-- info: 'Foam.Bridges.step_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.step_transport

/-- info: 'Foam.Bridges.step_gauge_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.step_gauge_symm

/-- info: 'Foam.Bridges.step_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.step_cocycle

/-- info: 'Foam.Bridges.StepFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame

/-- info: 'Foam.Bridges.StepFrame.u_ne_u'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.u_ne_u

/-- info: 'Foam.Bridges.StepFrame.u'_ne_u' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.u

/-- info: 'Foam.Bridges.StepFrame.lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.lam

/-- info: 'Foam.Bridges.StepFrame.lam_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.lam_visible

/-- info: 'Foam.Bridges.StepFrame.lam_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.lam_blind

/-- info: 'Foam.Bridges.StepFrame.hv'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.hv

/-- info: 'Foam.Bridges.StepFrame.hv'_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.hv

/-- info: 'Foam.Bridges.StepFrame.hv'_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.hv

/-- info: 'Foam.Bridges.StepFrame.hv'_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.hv

/-- info: 'Foam.Bridges.StepFrame.blind_not_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.blind_not_mirror

/-- info: 'Foam.Bridges.StepFrame.e_not_primary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.e_not_primary

/-- info: 'Foam.Bridges.StepFrame.c_not_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.c_not_mirror

/-- info: 'Foam.Bridges.StepFrame.lam_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.lam_ne_zero

/-- info: 'Foam.Bridges.StepFrame.central' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.central

/-- info: 'Foam.Bridges.StepFrame.hv'_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.hv

/-- info: 'Foam.Bridges.StepFrame.lam_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.lam_inj

/-- info: 'Foam.Bridges.StepFrame.hv'_span_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.hv

/-- info: 'Foam.Bridges.StepFrame.hv'_span_surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.hv

/-- info: 'Foam.Bridges.StepFrame.base_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.base_form

/-- info: 'Foam.Bridges.StepFrame.shear_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.shear_form

/-- info: 'Foam.Bridges.StepFrame.collinear_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.collinear_w

/-- info: 'Foam.Bridges.StepFrame.wline_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.wline_eq

/-- info: 'Foam.Bridges.StepFrame.main_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.main_setup

/-- info: 'Foam.Bridges.StepFrame.shear_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.shear_ne

/-- info: 'Foam.Bridges.StepFrame.collinear_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.collinear_main

/-- info: 'Foam.Bridges.StepFrame.hv'_collinear_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.hv

/-- info: 'Foam.Bridges.StepFrame.toPointSys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.toPointSys

/-- info: 'Foam.Bridges.StepFrame.toPointSys_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.toPointSys_of_le

/-- info: 'Foam.Bridges.StepFrame.toPointSys_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.StepFrame.toPointSys_w

/-- info: 'Foam.Bridges.stepFrame_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.stepFrame_exists

/-- info: 'Foam.Bridges.PointSys.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.PointSys.step
