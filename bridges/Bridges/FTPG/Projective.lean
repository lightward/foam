import Mathlib.Order.ModularLattice
import Mathlib.Order.Atoms
import Mathlib.Order.KrullDimension
import Mathlib.Order.Height
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projectivization.Basic

namespace Foam.Bridges

universe u

def ftpg_statement : Prop :=
  ∀ (L : Type u) [Lattice L] [BoundedOrder L]
    [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]
    (_h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (_h_height : ∃ (a b c d : L), ⊥ < a ∧ a < b ∧ b < c ∧ c < d),
    ∃ (D : Type u) (_ : DivisionRing D)
      (V : Type u) (_ : AddCommGroup V) (_ : Module D V),
    Nonempty (L ≃o Submodule D V)

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in

theorem IsAtom.eq_of_le {a b : L} (ha : IsAtom a) (hb : IsAtom b) (h : a ≤ b) :
    a = b :=
  (hb.le_iff.mp h).resolve_left ha.1

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in

theorem atoms_disjoint {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    a ⊓ b = ⊥ := by
  rcases ha.le_iff.mp inf_le_left with h | h
  · exact h
  · exfalso; apply hab
    have hab' : a ≤ b := h ▸ inf_le_right
    exact le_antisymm hab' (hb.le_iff.mp hab' |>.resolve_left ha.1 ▸ le_refl b)

omit [ComplementedLattice L] [IsAtomistic L] in

theorem atom_covBy_join {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    a ⋖ a ⊔ b := by
  have h_meet : a ⊓ b = ⊥ := atoms_disjoint ha hb hab
  exact covBy_sup_of_inf_covBy_of_inf_covBy_left (h_meet ▸ ha.bot_covBy) (h_meet ▸ hb.bot_covBy)

omit [ComplementedLattice L] [IsAtomistic L] in

theorem third_atom_on_line {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b ∧ a ⊔ b = a ⊔ c := by
  obtain ⟨c, hc_atom, hc_le, hc_ne_a, hc_ne_b⟩ := h_irred a b ha hb hab
  refine ⟨c, hc_atom, hc_le, hc_ne_a, hc_ne_b, ?_⟩
  have h_cov := atom_covBy_join ha hb hab
  have h_c_not_le_a : ¬ c ≤ a := by
    intro hle
    exact hc_ne_a (le_antisymm hle (ha.le_iff.mp hle |>.resolve_left hc_atom.1 ▸ le_refl a))
  have h_a_lt_ac : a < a ⊔ c := lt_of_le_of_ne le_sup_left (by
    intro heq; exact h_c_not_le_a (heq ▸ le_sup_right))
  have h_ac_le_ab : a ⊔ c ≤ a ⊔ b := sup_le le_sup_left hc_le
  exact ((h_cov.eq_or_eq h_a_lt_ac.le h_ac_le_ab).resolve_left (ne_of_gt h_a_lt_ac)).symm

omit [ComplementedLattice L] [IsAtomistic L] in

theorem line_covers_its_atoms {a b c : L}
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (hc : IsAtom c) (hc_le : c ≤ a ⊔ b) :
    c ⋖ a ⊔ b := by
  by_cases hca : c = a
  · subst hca; exact atom_covBy_join hc hb hab
  by_cases hcb : c = b
  · subst hcb; rw [sup_comm]; exact atom_covBy_join hc ha (Ne.symm hab)
  · have h_cov_ab := atom_covBy_join ha hb hab
    have h_c_not_le_a : ¬ c ≤ a := by
      intro hle; exact hca (le_antisymm hle (ha.le_iff.mp hle |>.resolve_left hc.1 ▸ le_refl a))
    have h_a_lt_ac : a < a ⊔ c := lt_of_le_of_ne le_sup_left (by
      intro heq; exact h_c_not_le_a (heq ▸ le_sup_right))
    have h_eq : a ⊔ b = a ⊔ c :=
      ((h_cov_ab.eq_or_eq h_a_lt_ac.le (sup_le le_sup_left hc_le)).resolve_left
        (ne_of_gt h_a_lt_ac)).symm
    have hac : a ≠ c := fun h => hca h.symm
    have h_cov_ca := atom_covBy_join hc ha hac.symm
    rwa [sup_comm c a, ← h_eq] at h_cov_ca

omit [ComplementedLattice L] [IsAtomistic L] in

theorem line_eq_of_atom_le {a b c : L}
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (hab : a ≠ b) (hac : a ≠ c) (_hbc : b ≠ c)
    (hc_le : c ≤ a ⊔ b) :
    a ⊔ b = a ⊔ c := by
  have h_cov := atom_covBy_join ha hb hab
  have h_c_not_le_a : ¬ c ≤ a := by
    intro hle; exact hac.symm (le_antisymm hle (ha.le_iff.mp hle |>.resolve_left hc.1 ▸ le_refl a))
  have h_a_lt_ac : a < a ⊔ c := lt_of_le_of_ne le_sup_left (by
    intro heq; exact h_c_not_le_a (heq ▸ le_sup_right))
  exact ((h_cov.eq_or_eq h_a_lt_ac.le (sup_le le_sup_left hc_le)).resolve_left
    (ne_of_gt h_a_lt_ac)).symm

omit [ComplementedLattice L] in

theorem line_height_two {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    {x : L} (hx_pos : ⊥ < x) (hx_lt : x < a ⊔ b) :
    IsAtom x := by
  obtain ⟨s, hs_lub, hs_atoms⟩ := IsAtomistic.isLUB_atoms x
  have hs_ne : s.Nonempty := by
    by_contra hs_empty
    simp only [Set.not_nonempty_iff_eq_empty] at hs_empty
    subst hs_empty
    have : x ≤ ⊥ := hs_lub.2 (fun _ hx => (Set.mem_empty_iff_false _).mp hx |>.elim)
    exact ne_of_gt hx_pos (le_antisymm this bot_le)
  obtain ⟨p, hp_mem⟩ := hs_ne
  have hp_atom := hs_atoms p hp_mem
  have hp_le_x : p ≤ x := hs_lub.1 hp_mem
  have hp_cov := line_covers_its_atoms ha hb hab hp_atom (le_trans hp_le_x hx_lt.le)
  rcases hp_cov.eq_or_eq hp_le_x hx_lt.le with h | h
  · exact h ▸ hp_atom
  · exact absurd h (ne_of_lt hx_lt)

omit [ComplementedLattice L] [IsAtomistic L] in

theorem line_covBy_plane {a b c : L}
    (_ha : IsAtom a) (_hb : IsAtom b) (hc : IsAtom c)
    (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (h_not_collinear : ¬ c ≤ a ⊔ b) :
    a ⊔ b ⋖ a ⊔ b ⊔ c := by
  have h_meet : c ⊓ (a ⊔ b) = ⊥ := by
    rcases hc.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) h_not_collinear
  have h1 := covBy_sup_of_inf_covBy_left (h_meet ▸ hc.bot_covBy)
  rw [show c ⊔ (a ⊔ b) = a ⊔ b ⊔ c from sup_comm _ _] at h1
  exact h1

omit [ComplementedLattice L] [IsAtomistic L] in

theorem modular_intersection {a b c : L}
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h_not_collinear : ¬ c ≤ a ⊔ b) :
    (a ⊔ b) ⊓ (a ⊔ c) = a := by
  rw [sup_inf_assoc_of_le b (le_sup_left : a ≤ a ⊔ c)]
  have : b ⊓ (a ⊔ c) = ⊥ := by
    rcases hb.le_iff.mp inf_le_left with h | h
    · exact h
    · exfalso; apply h_not_collinear
      have hb_le : b ≤ a ⊔ c := h ▸ inf_le_right
      exact (line_eq_of_atom_le ha hc hb hac hab hbc.symm hb_le) ▸ le_sup_right
  rw [this, sup_bot_eq]

omit [ComplementedLattice L] [IsAtomistic L] in

theorem covBy_inf_disjoint_atom {x y z : L}
    (h_cov : x ⋖ z) (hy_le : y ≤ z) (hy_not_le : ¬ y ≤ x) (h_disj : x ⊓ y = ⊥) :
    ⊥ ⋖ y := by
  have h_join : x ⊔ y = z := by
    have h_lt : x < x ⊔ y := lt_of_le_of_ne le_sup_left
      (fun h => hy_not_le (le_trans le_sup_right (ge_of_eq h)))
    exact (h_cov.eq_or_eq h_lt.le (sup_le h_cov.le hy_le)).resolve_left (ne_of_gt h_lt)
  have h_inf_cov : x ⊓ y ⋖ y := by
    rw [← h_join] at h_cov
    exact IsLowerModularLattice.inf_covBy_of_covBy_sup h_cov
  rwa [h_disj] at h_inf_cov

omit [ComplementedLattice L] [IsAtomistic L] in

theorem lines_meet_if_coplanar {l₁ l₂ z : L}
    (h_cov : l₁ ⋖ z) (hl₂_le : l₂ ≤ z) (hl₂_not : ¬ l₂ ≤ l₁)
    {p : L} (hp : IsAtom p) (hp_lt : p < l₂) :
    l₁ ⊓ l₂ ≠ ⊥ := by
  intro h_disj
  exact (covBy_inf_disjoint_atom h_cov hl₂_le hl₂_not h_disj).2 hp.bot_lt hp_lt

omit [ComplementedLattice L] [IsAtomistic L] in

theorem veblen_young {a b c d : L}
    (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c) (hd : IsAtom d)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d)
    (h_nc : ¬ c ≤ a ⊔ b)
    (hd_le : d ≤ a ⊔ b ⊔ c)
    (_hd_not_bc : ¬ d ≤ b ⊔ c) :
    (b ⊔ c) ⊓ (a ⊔ d) ≠ ⊥ := by
  have ha_not_bc : ¬ a ≤ b ⊔ c := by
    intro hle; apply h_nc
    calc c ≤ b ⊔ c := le_sup_right
      _ = b ⊔ a := line_eq_of_atom_le hb hc ha hbc hab.symm hac.symm hle
      _ = a ⊔ b := sup_comm b a
  have ha_meet_bc : a ⊓ (b ⊔ c) = ⊥ := by
    rcases ha.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) ha_not_bc
  have h_plane_covers_bc : b ⊔ c ⋖ a ⊔ (b ⊔ c) :=
    covBy_sup_of_inf_covBy_left (ha_meet_bc ▸ ha.bot_covBy)
  have h_ad_le_plane : a ⊔ d ≤ a ⊔ b ⊔ c :=
    sup_le (le_sup_of_le_left le_sup_left) hd_le
  have h_join_le : (b ⊔ c) ⊔ (a ⊔ d) ≤ a ⊔ (b ⊔ c) := by
    rw [(sup_assoc a b c).symm]
    exact sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right) h_ad_le_plane
  have h_bc_lt_join : b ⊔ c < (b ⊔ c) ⊔ (a ⊔ d) :=
    lt_of_le_of_ne le_sup_left (fun h => ha_not_bc
      (le_trans le_sup_left (le_trans le_sup_right (ge_of_eq h))))
  have h_join_eq : (b ⊔ c) ⊔ (a ⊔ d) = a ⊔ (b ⊔ c) :=
    (h_plane_covers_bc.eq_or_eq h_bc_lt_join.le h_join_le).resolve_left
      (ne_of_gt h_bc_lt_join)
  intro h_disjoint
  rw [← h_join_eq] at h_plane_covers_bc
  have h_cov_ad : (b ⊔ c) ⊓ (a ⊔ d) ⋖ (a ⊔ d) :=
    IsLowerModularLattice.inf_covBy_of_covBy_sup h_plane_covers_bc
  rw [h_disjoint] at h_cov_ad
  exact h_cov_ad.2
    (show ⊥ < a from ha.bot_lt)
    (show a < a ⊔ d from lt_of_le_of_ne le_sup_left (by
      intro heq
      exact had (le_antisymm (ha.le_iff.mp (heq ▸ le_sup_right) |>.resolve_left hd.1 ▸ le_refl a)
        (heq ▸ le_sup_right))))

omit [ComplementedLattice L] in

theorem meet_of_lines_is_atom {a b c d : L}
    (ha : IsAtom a) (hb : IsAtom b) (_hc : IsAtom c) (_hd : IsAtom d)
    (hab : a ≠ b) (_hcd : c ≠ d)
    (h_not_le : ¬ a ⊔ b ≤ c ⊔ d)
    (h_meet_ne : (a ⊔ b) ⊓ (c ⊔ d) ≠ ⊥) :
    IsAtom ((a ⊔ b) ⊓ (c ⊔ d)) :=
  line_height_two ha hb hab
    (bot_lt_iff_ne_bot.mpr h_meet_ne)
    (lt_of_le_of_ne inf_le_left (fun heq => h_not_le (heq ▸ inf_le_right)))

omit [ComplementedLattice L] [IsAtomistic L] in

theorem two_lines {X Y Z l₁ : L}
    (hX : IsAtom X) (hY : IsAtom Y) (hZ : IsAtom Z)
    (hXZ : X ≠ Z)
    (hX_l : X ≤ l₁) (hY_l : Y ≤ l₁)
    (hY_XZ : Y ≤ X ⊔ Z)
    (hZ_not_l : ¬ Z ≤ l₁)
    (hX_cov : X ⋖ l₁) :
    X = Y := by

  have h_not_le : ¬ l₁ ≤ X ⊔ Z := by
    intro hle
    exact hZ_not_l (((atom_covBy_join hX hZ hXZ).eq_or_eq hX_cov.lt.le hle).resolve_left
      (ne_of_gt hX_cov.lt) ▸ le_sup_right)
  have h_lt : l₁ ⊓ (X ⊔ Z) < l₁ := lt_of_le_of_ne inf_le_left
    (fun h => h_not_le (h ▸ inf_le_right))
  have h_meet_eq_X : l₁ ⊓ (X ⊔ Z) = X :=
    (hX_cov.eq_or_eq (le_inf hX_l le_sup_left) h_lt.le).resolve_right h_lt.ne
  have hY_le_X : Y ≤ X := h_meet_eq_X ▸ le_inf hY_l hY_XZ
  exact ((hX.le_iff.mp hY_le_X).resolve_left hY.1).symm

noncomputable def project (c p l : L) : L := (p ⊔ c) ⊓ l

omit [ComplementedLattice L] in

theorem project_is_atom {c p a b : L}
    (hc : IsAtom c) (hp : IsAtom p) (hcp : c ≠ p)
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (hc_not_l : ¬ c ≤ a ⊔ b) (hp_not_l : ¬ p ≤ a ⊔ b)
    (h_coplanar : p ⊔ c ≤ (a ⊔ b) ⊔ c) :
    IsAtom (project c p (a ⊔ b)) := by
  unfold project
  have hc_meet : c ⊓ (a ⊔ b) = ⊥ := by
    rcases hc.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hc_not_l
  have h_plane_cov : (a ⊔ b) ⋖ (a ⊔ b) ⊔ c := by
    rw [show (a ⊔ b) ⊔ c = c ⊔ (a ⊔ b) from sup_comm _ _]
    exact covBy_sup_of_inf_covBy_left (hc_meet ▸ hc.bot_covBy)
  have h_pc_not_le : ¬ p ⊔ c ≤ a ⊔ b :=
    fun h => hc_not_l (le_trans le_sup_right h)
  have h_c_not_le_p : ¬ c ≤ p := by
    intro hle
    exact hcp.symm (le_antisymm (hp.le_iff.mp hle |>.resolve_left hc.1 ▸ le_refl p) hle)
  have h_p_lt_pc : p < p ⊔ c := lt_of_le_of_ne le_sup_left
    (fun h => h_c_not_le_p (h ▸ le_sup_right))
  have h_meet_ne : (a ⊔ b) ⊓ (p ⊔ c) ≠ ⊥ :=
    lines_meet_if_coplanar h_plane_cov h_coplanar h_pc_not_le hp h_p_lt_pc
  apply line_height_two ha hb hab
  · exact bot_lt_iff_ne_bot.mpr (by rwa [inf_comm] at h_meet_ne)
  · apply lt_of_le_of_ne inf_le_right
    intro heq
    have hab_le : a ⊔ b ≤ p ⊔ c := heq ▸ inf_le_left
    have ha_cov_pc := line_covers_its_atoms hp hc hcp.symm ha (le_trans le_sup_left hab_le)
    rcases ha_cov_pc.eq_or_eq (atom_covBy_join ha hb hab |>.lt |>.le) hab_le with h | h
    · exact ne_of_gt (atom_covBy_join ha hb hab |>.lt) h
    · exact hp_not_l (h ▸ le_sup_left)

omit [BoundedOrder L] [ComplementedLattice L] [IsAtomistic L] in

theorem planes_meet_covBy {π₁ π₂ s : L}
    (h₁ : π₁ ⋖ s) (h₂ : π₂ ⋖ s) (h_ne : π₁ ≠ π₂) :
    (π₁ ⊓ π₂) ⋖ π₁ ∧ (π₁ ⊓ π₂) ⋖ π₂ := by
  have h₂_not_le : ¬ π₂ ≤ π₁ := by
    intro hle
    rcases h₂.eq_or_eq hle h₁.le with h | h
    · exact h_ne h
    · exact ne_of_lt h₁.lt h
  have h_join : π₁ ⊔ π₂ = s := by
    have h_lt : π₁ < π₁ ⊔ π₂ := lt_of_le_of_ne le_sup_left
      (fun h => h₂_not_le (le_trans le_sup_right (ge_of_eq h)))
    exact (h₁.eq_or_eq h_lt.le (sup_le h₁.le h₂.le)).resolve_left (ne_of_gt h_lt)
  constructor
  ·
    rw [← h_join] at h₂
    rw [sup_comm] at h₂
    have := IsLowerModularLattice.inf_covBy_of_covBy_sup h₂
    rwa [inf_comm] at this
  ·
    rw [← h_join] at h₁
    exact IsLowerModularLattice.inf_covBy_of_covBy_sup h₁

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in

theorem desargues_nonplanar
    {o a₁ a₂ a₃ b₁ b₂ b₃ : L}

    (_ho : IsAtom o) (_ha₁ : IsAtom a₁) (_ha₂ : IsAtom a₂) (_ha₃ : IsAtom a₃)
    (_hb₁ : IsAtom b₁) (_hb₂ : IsAtom b₂) (_hb₃ : IsAtom b₃)

    (_hb₁_on : b₁ ≤ o ⊔ a₁) (_hb₂_on : b₂ ≤ o ⊔ a₂) (_hb₃_on : b₃ ≤ o ⊔ a₃)

    (πA : L) (hπA : πA = a₁ ⊔ a₂ ⊔ a₃)
    (πB : L) (hπB : πB = b₁ ⊔ b₂ ⊔ b₃)

    :

    (a₁ ⊔ a₂) ⊓ (b₁ ⊔ b₂) ≤ πA ⊓ πB ∧
    (a₁ ⊔ a₃) ⊓ (b₁ ⊔ b₃) ≤ πA ⊓ πB ∧
    (a₂ ⊔ a₃) ⊓ (b₂ ⊔ b₃) ≤ πA ⊓ πB := by
  subst hπA; subst hπB

  refine ⟨le_inf (inf_le_left.trans ?_) (inf_le_right.trans ?_),
          le_inf (inf_le_left.trans ?_) (inf_le_right.trans ?_),
          le_inf (inf_le_left.trans ?_) (inf_le_right.trans ?_)⟩

  ·
    exact le_sup_left
  ·
    exact le_sup_left
  ·
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  ·
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  ·
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  ·
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

omit [ComplementedLattice L] in

theorem project_injective {c a b p q : L}
    (hc : IsAtom c) (hp : IsAtom p) (hq : IsAtom q)
    (ha : IsAtom a) (hb : IsAtom b)
    (hcp : c ≠ p) (hcq : c ≠ q) (hpq : p ≠ q) (hab : a ≠ b)
    (hc_not_l : ¬ c ≤ a ⊔ b)
    (hp_not_l : ¬ p ≤ a ⊔ b) (_hq_not_l : ¬ q ≤ a ⊔ b)
    (hp_coplanar : p ⊔ c ≤ (a ⊔ b) ⊔ c)
    (_hq_coplanar : q ⊔ c ≤ (a ⊔ b) ⊔ c)

    (hpq_diff : p ⊔ c ≠ q ⊔ c) :
    project c p (a ⊔ b) ≠ project c q (a ⊔ b) := by
  unfold project
  intro heq

  have hm_atom := project_is_atom hc hp hcp ha hb hab hc_not_l hp_not_l hp_coplanar
  unfold project at hm_atom

  have hm_le_pc : (p ⊔ c) ⊓ (a ⊔ b) ≤ p ⊔ c := inf_le_left
  have hm_le_qc : (p ⊔ c) ⊓ (a ⊔ b) ≤ q ⊔ c := heq ▸ inf_le_left
  have hm_le_ab : (p ⊔ c) ⊓ (a ⊔ b) ≤ a ⊔ b := inf_le_right

  have hm_le_meet : (p ⊔ c) ⊓ (a ⊔ b) ≤ (p ⊔ c) ⊓ (q ⊔ c) :=
    le_inf hm_le_pc hm_le_qc

  have hq_not_pc : ¬ q ≤ p ⊔ c := by
    intro hle
    apply hpq_diff
    rw [sup_comm p c, sup_comm q c]
    exact line_eq_of_atom_le hc hp hq hcp hcq hpq (sup_comm p c ▸ hle)

  have h_meet_eq : (c ⊔ p) ⊓ (c ⊔ q) = c :=
    modular_intersection hc hp hq hcp hcq hpq (sup_comm c p ▸ hq_not_pc)

  have hm_le_c : (p ⊔ c) ⊓ (a ⊔ b) ≤ c := by
    calc (p ⊔ c) ⊓ (a ⊔ b)
        ≤ (p ⊔ c) ⊓ (q ⊔ c) := hm_le_meet
      _ = (c ⊔ p) ⊓ (c ⊔ q) := by rw [sup_comm p c, sup_comm q c]
      _ = c := h_meet_eq

  rcases hc.le_iff.mp hm_le_c with h | h
  · exact hm_atom.1 h
  · exact hc_not_l (h ▸ hm_le_ab)

def AtomsOn (l : L) : Type u := {a : L // IsAtom a ∧ a ≤ l}

def AtomsOn.mk_left {a b : L} (ha : IsAtom a) (_hb : IsAtom b) (_hab : a ≠ b) :
    AtomsOn (a ⊔ b) :=
  ⟨a, ha, le_sup_left⟩

def AtomsOn.mk_right {a b : L} (_ha : IsAtom a) (hb : IsAtom b) (_hab : a ≠ b) :
    AtomsOn (a ⊔ b) :=
  ⟨b, hb, le_sup_right⟩

noncomputable def projectOn {c a b : L}
    (hc : IsAtom c) (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (hc_not : ¬ c ≤ a ⊔ b) :

    {p : L // IsAtom p ∧ ¬ p ≤ a ⊔ b ∧ p ⊔ c ≤ (a ⊔ b) ⊔ c ∧ c ≠ p} →
    AtomsOn (a ⊔ b) :=
  fun ⟨p, hp_atom, hp_not, hp_cop, hcp⟩ =>
    ⟨project c p (a ⊔ b),
     project_is_atom hc hp_atom hcp ha hb hab hc_not hp_not hp_cop,
     inf_le_right⟩

omit [ComplementedLattice L] in

theorem perspect_atom {p c a₂ b₂ : L}
    (hc : IsAtom c) (hp : IsAtom p) (hpc : p ≠ c)
    (_ha₂ : IsAtom a₂) (_hb₂ : IsAtom b₂) (_hab₂ : a₂ ≠ b₂)
    (hc_not : ¬ c ≤ a₂ ⊔ b₂)
    (h_in_plane : p ⊔ c ≤ (a₂ ⊔ b₂) ⊔ c) :
    IsAtom ((p ⊔ c) ⊓ (a₂ ⊔ b₂)) := by

  have hc_meet : c ⊓ (a₂ ⊔ b₂) = ⊥ := by
    rcases hc.le_iff.mp inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hc_not
  have h_cov : (a₂ ⊔ b₂) ⋖ (a₂ ⊔ b₂) ⊔ c := by
    rw [show (a₂ ⊔ b₂) ⊔ c = c ⊔ (a₂ ⊔ b₂) from sup_comm _ _]
    exact covBy_sup_of_inf_covBy_left (hc_meet ▸ hc.bot_covBy)

  have h_pc_not : ¬ p ⊔ c ≤ a₂ ⊔ b₂ :=
    fun h => hc_not (le_trans le_sup_right h)

  have hc_not_le_p : ¬ c ≤ p := by
    intro hle
    exact hpc.symm (hp.le_iff.mp hle |>.resolve_left hc.1)
  have hp_lt_pc : p < p ⊔ c := lt_of_le_of_ne le_sup_left
    (fun h => hc_not_le_p (h ▸ le_sup_right))

  have h_meet_ne : (a₂ ⊔ b₂) ⊓ (p ⊔ c) ≠ ⊥ :=
    lines_meet_if_coplanar h_cov h_in_plane h_pc_not hp hp_lt_pc

  exact line_height_two hp hc hpc
    (bot_lt_iff_ne_bot.mpr (by rwa [inf_comm] at h_meet_ne))
    (lt_of_le_of_ne inf_le_left (fun h => h_pc_not (h ▸ inf_le_right)))

noncomputable def perspectivity {c a₁ b₁ a₂ b₂ : L}
    (hc : IsAtom c) (_ha₁ : IsAtom a₁) (_hb₁ : IsAtom b₁) (ha₂ : IsAtom a₂) (hb₂ : IsAtom b₂)
    (_hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂)
    (hc_not_l₁ : ¬ c ≤ a₁ ⊔ b₁) (hc_not_l₂ : ¬ c ≤ a₂ ⊔ b₂)
    (h_coplanar : a₁ ⊔ b₁ ⊔ c = a₂ ⊔ b₂ ⊔ c) :
    AtomsOn (a₁ ⊔ b₁) → AtomsOn (a₂ ⊔ b₂) :=
  fun ⟨p, hp_atom, hp_le⟩ =>
    have hpc : p ≠ c := fun h => hc_not_l₁ (h ▸ hp_le)
    have hp_in_plane : p ⊔ c ≤ (a₂ ⊔ b₂) ⊔ c :=
      h_coplanar ▸ sup_le (le_sup_of_le_left hp_le) le_sup_right
    ⟨(p ⊔ c) ⊓ (a₂ ⊔ b₂),
     perspect_atom hc hp_atom hpc ha₂ hb₂ hab₂ hc_not_l₂ hp_in_plane,
     inf_le_right⟩

omit [ComplementedLattice L] in

theorem perspectivity_injective {c a₁ b₁ a₂ b₂ : L}
    (hc : IsAtom c)
    (ha₁ : IsAtom a₁) (hb₁ : IsAtom b₁) (ha₂ : IsAtom a₂) (hb₂ : IsAtom b₂)
    (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂)
    (hc_not_l₁ : ¬ c ≤ a₁ ⊔ b₁) (hc_not_l₂ : ¬ c ≤ a₂ ⊔ b₂)
    (h_coplanar : a₁ ⊔ b₁ ⊔ c = a₂ ⊔ b₂ ⊔ c)
    {p q : AtomsOn (a₁ ⊔ b₁)} (hpq : p ≠ q) :
    perspectivity hc ha₁ hb₁ ha₂ hb₂ hab₁ hab₂ hc_not_l₁ hc_not_l₂ h_coplanar p ≠
    perspectivity hc ha₁ hb₁ ha₂ hb₂ hab₁ hab₂ hc_not_l₁ hc_not_l₂ h_coplanar q := by
  obtain ⟨p, hp_atom, hp_le⟩ := p
  obtain ⟨q, hq_atom, hq_le⟩ := q

  have hpq_val : p ≠ q := fun h => hpq (Subtype.ext h)
  simp only [perspectivity]
  intro heq

  have heq_val : (p ⊔ c) ⊓ (a₂ ⊔ b₂) = (q ⊔ c) ⊓ (a₂ ⊔ b₂) := congrArg Subtype.val heq
  have hpc : p ≠ c := fun h => hc_not_l₁ (h ▸ hp_le)
  have hqc : q ≠ c := fun h => hc_not_l₁ (h ▸ hq_le)
  by_cases h_lines : p ⊔ c = q ⊔ c
  ·
    have h_ne : a₁ ⊔ b₁ ≠ p ⊔ c := fun h => hc_not_l₁ (h ▸ le_sup_right)
    have hl₁_not_le : ¬ (a₁ ⊔ b₁) ≤ p ⊔ c := by
      intro hle
      apply h_ne
      have ha₁_cov := line_covers_its_atoms hp_atom hc hpc ha₁ (le_trans le_sup_left hle)
      exact (ha₁_cov.eq_or_eq (atom_covBy_join ha₁ hb₁ hab₁).lt.le hle).resolve_left
        (ne_of_gt (atom_covBy_join ha₁ hb₁ hab₁).lt)
    have hp_le_meet : p ≤ (a₁ ⊔ b₁) ⊓ (p ⊔ c) := le_inf hp_le le_sup_left
    have hq_le_meet : q ≤ (a₁ ⊔ b₁) ⊓ (p ⊔ c) := le_inf hq_le (h_lines ▸ le_sup_left)
    have h_meet_atom : IsAtom ((a₁ ⊔ b₁) ⊓ (p ⊔ c)) :=
      line_height_two ha₁ hb₁ hab₁
        (bot_lt_iff_ne_bot.mpr (fun h => hp_atom.1 (le_antisymm (h ▸ hp_le_meet) bot_le)))
        (lt_of_le_of_ne inf_le_left (fun h => hl₁_not_le (h ▸ inf_le_right)))
    have hp_eq := le_antisymm hp_le_meet
      (h_meet_atom.le_iff.mp hp_le_meet |>.resolve_left hp_atom.1 ▸ le_refl _)
    have hq_eq := le_antisymm hq_le_meet
      (h_meet_atom.le_iff.mp hq_le_meet |>.resolve_left hq_atom.1 ▸ le_refl _)
    exact absurd (hp_eq.trans hq_eq.symm) hpq_val
  ·
    have hm_le_pc : (p ⊔ c) ⊓ (a₂ ⊔ b₂) ≤ p ⊔ c := inf_le_left
    have hm_le_qc : (p ⊔ c) ⊓ (a₂ ⊔ b₂) ≤ q ⊔ c := heq_val ▸ inf_le_left
    have hq_not_pc : ¬ q ≤ p ⊔ c := by
      intro hle
      apply h_lines
      rw [sup_comm p c, sup_comm q c]
      exact line_eq_of_atom_le hc hp_atom hq_atom hpc.symm hqc.symm hpq_val
        (sup_comm p c ▸ hle)
    have h_meet_eq : (c ⊔ p) ⊓ (c ⊔ q) = c :=
      modular_intersection hc hp_atom hq_atom hpc.symm hqc.symm hpq_val
        (sup_comm c p ▸ hq_not_pc)
    have hm_le_c : (p ⊔ c) ⊓ (a₂ ⊔ b₂) ≤ c := by
      calc (p ⊔ c) ⊓ (a₂ ⊔ b₂)
          ≤ (p ⊔ c) ⊓ (q ⊔ c) := le_inf hm_le_pc hm_le_qc
        _ = (c ⊔ p) ⊓ (c ⊔ q) := by rw [sup_comm p c, sup_comm q c]
        _ = c := h_meet_eq
    have hp_in_plane : p ⊔ c ≤ (a₂ ⊔ b₂) ⊔ c :=
      h_coplanar ▸ sup_le (le_sup_of_le_left hp_le) le_sup_right
    have hm_atom := perspect_atom hc hp_atom hpc ha₂ hb₂ hab₂ hc_not_l₂ hp_in_plane
    rcases hc.le_iff.mp hm_le_c with h | h
    · exact absurd h hm_atom.1
    · exact absurd (h ▸ inf_le_right : c ≤ a₂ ⊔ b₂) hc_not_l₂

omit [ComplementedLattice L] [IsAtomistic L] in

theorem perspect_line_eq {p c l : L}
    (hc : IsAtom c) (hp : IsAtom p) (hpc : p ≠ c)
    (hc_not : ¬ c ≤ l)
    (_h_in_plane : p ⊔ c ≤ l ⊔ c)
    (hq_atom : IsAtom ((p ⊔ c) ⊓ l)) :
    ((p ⊔ c) ⊓ l) ⊔ c = p ⊔ c := by

  have hqc_le : ((p ⊔ c) ⊓ l) ⊔ c ≤ p ⊔ c := sup_le inf_le_left le_sup_right

  have hqc_ne : (p ⊔ c) ⊓ l ≠ c := fun h => hc_not (h ▸ inf_le_right)

  have hc_lt_qc : c < ((p ⊔ c) ⊓ l) ⊔ c := by
    apply lt_of_le_of_ne le_sup_right
    intro h

    have q_le_c : (p ⊔ c) ⊓ l ≤ c := le_sup_left.trans h.symm.le
    rcases hc.le_iff.mp q_le_c with h | h
    · exact hq_atom.1 h
    · exact hqc_ne h

  have hc_cov_pc : c ⋖ p ⊔ c := by
    rw [sup_comm]; exact atom_covBy_join hc hp hpc.symm
  exact (hc_cov_pc.eq_or_eq hc_lt_qc.le hqc_le).resolve_left (ne_of_gt hc_lt_qc)

omit [ComplementedLattice L] in

theorem perspect_roundtrip {p c a₁ b₁ a₂ b₂ : L}
    (hc : IsAtom c) (hp : IsAtom p) (hpc : p ≠ c)
    (ha₁ : IsAtom a₁) (hb₁ : IsAtom b₁) (hab₁ : a₁ ≠ b₁)
    (ha₂ : IsAtom a₂) (hb₂ : IsAtom b₂) (hab₂ : a₂ ≠ b₂)
    (hc_not_l₁ : ¬ c ≤ a₁ ⊔ b₁) (hc_not_l₂ : ¬ c ≤ a₂ ⊔ b₂)
    (h_coplanar : a₁ ⊔ b₁ ⊔ c = a₂ ⊔ b₂ ⊔ c)
    (hp_le : p ≤ a₁ ⊔ b₁) :
    ((p ⊔ c) ⊓ (a₂ ⊔ b₂) ⊔ c) ⊓ (a₁ ⊔ b₁) = p := by

  have hp_in_plane : p ⊔ c ≤ (a₂ ⊔ b₂) ⊔ c :=
    h_coplanar ▸ sup_le (le_sup_of_le_left hp_le) le_sup_right
  have hq_atom := perspect_atom hc hp hpc ha₂ hb₂ hab₂ hc_not_l₂ hp_in_plane
  have h_line_eq : (p ⊔ c) ⊓ (a₂ ⊔ b₂) ⊔ c = p ⊔ c :=
    perspect_line_eq hc hp hpc hc_not_l₂ hp_in_plane hq_atom

  rw [h_line_eq]

  have hp_le_meet : p ≤ (p ⊔ c) ⊓ (a₁ ⊔ b₁) := le_inf le_sup_left hp_le

  have hq_in_plane : p ⊔ c ≤ (a₁ ⊔ b₁) ⊔ c :=
    sup_le (le_sup_of_le_left hp_le) le_sup_right
  have h_meet_atom := perspect_atom hc hp hpc ha₁ hb₁ hab₁ hc_not_l₁ hq_in_plane

  exact (h_meet_atom.le_iff.mp hp_le_meet |>.resolve_left hp.1).symm

omit [ComplementedLattice L] in

theorem perspect_fixes_intersection {p c a₁ b₁ a₂ b₂ : L}
    (hc : IsAtom c) (hp : IsAtom p) (hpc : p ≠ c)
    (_ha₂ : IsAtom a₂) (_hb₂ : IsAtom b₂) (_hab₂ : a₂ ≠ b₂)
    (hc_not_l₂ : ¬ c ≤ a₂ ⊔ b₂)
    (_hp_le₁ : p ≤ a₁ ⊔ b₁) (hp_le₂ : p ≤ a₂ ⊔ b₂)
    (h_in_plane : p ⊔ c ≤ (a₂ ⊔ b₂) ⊔ c) :
    (p ⊔ c) ⊓ (a₂ ⊔ b₂) = p := by

  have hp_le_meet : p ≤ (p ⊔ c) ⊓ (a₂ ⊔ b₂) := le_inf le_sup_left hp_le₂

  have h_atom := perspect_atom hc hp hpc _ha₂ _hb₂ _hab₂ hc_not_l₂ h_in_plane

  exact (h_atom.le_iff.mp hp_le_meet |>.resolve_left hp.1).symm

/-- info: 'Foam.Bridges.ftpg_statement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ftpg_statement

/-- info: 'Foam.Bridges.IsAtom.eq_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsAtom.eq_of_le

/-- info: 'Foam.Bridges.atoms_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms atoms_disjoint

/-- info: 'Foam.Bridges.atom_covBy_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms atom_covBy_join

/-- info: 'Foam.Bridges.third_atom_on_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms third_atom_on_line

/-- info: 'Foam.Bridges.line_covers_its_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms line_covers_its_atoms

/-- info: 'Foam.Bridges.line_eq_of_atom_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms line_eq_of_atom_le

/-- info: 'Foam.Bridges.line_height_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms line_height_two

/-- info: 'Foam.Bridges.line_covBy_plane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms line_covBy_plane

/-- info: 'Foam.Bridges.modular_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms modular_intersection

/-- info: 'Foam.Bridges.covBy_inf_disjoint_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms covBy_inf_disjoint_atom

/-- info: 'Foam.Bridges.lines_meet_if_coplanar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lines_meet_if_coplanar

/-- info: 'Foam.Bridges.veblen_young' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms veblen_young

/-- info: 'Foam.Bridges.meet_of_lines_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meet_of_lines_is_atom

/-- info: 'Foam.Bridges.two_lines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms two_lines

/-- info: 'Foam.Bridges.project_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms project_is_atom

/-- info: 'Foam.Bridges.planes_meet_covBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms planes_meet_covBy

/-- info: 'Foam.Bridges.desargues_nonplanar' does not depend on any axioms -/
#guard_msgs in #print axioms desargues_nonplanar

/-- info: 'Foam.Bridges.project_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms project_injective

/-- info: 'Foam.Bridges.AtomsOn' does not depend on any axioms -/
#guard_msgs in #print axioms AtomsOn

/-- info: 'Foam.Bridges.AtomsOn.mk_left' does not depend on any axioms -/
#guard_msgs in #print axioms AtomsOn.mk_left

/-- info: 'Foam.Bridges.AtomsOn.mk_right' does not depend on any axioms -/
#guard_msgs in #print axioms AtomsOn.mk_right

/-- info: 'Foam.Bridges.perspect_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms perspect_atom

/-- info: 'Foam.Bridges.perspectivity_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms perspectivity_injective

/-- info: 'Foam.Bridges.perspect_line_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms perspect_line_eq

/-- info: 'Foam.Bridges.perspect_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms perspect_roundtrip

/-- info: 'Foam.Bridges.perspect_fixes_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms perspect_fixes_intersection

end Foam.Bridges
