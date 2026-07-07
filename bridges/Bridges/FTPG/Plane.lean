import Bridges.FTPG.Line
import Bridges.FTPG.Instance
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Pi

/-!
# Camp three, first pitch: the plane's point system

The camp-two summit (`Line.lean`) made every line of the frame plane an
algebraic graph.  This file packages that summit as homogeneous coordinates:
the atoms of the frame plane `π = O ⊔ U ⊔ V` embed into the projective plane
over `Dᵐᵒᵖ` (`D = Coordinate Γ`), with collinearity transported both ways.

Orientation: the line equation reads `y = s * x + b` with the slope
multiplying on the LEFT (`le_line_iff`), so the homogeneous coordinate space
is a RIGHT `D`-vector space — a left vector space over `Dᵐᵒᵖ`, which Mathlib
knows is a division ring.  The classical FTPG existential is free to hand
over `Dᵐᵒᵖ`; nothing is lost.

* `hvec` — the homogeneous coordinate vector of a plane atom: affine
  `p ↦ (x, y, 1)`, direction `S ↦ (1, slope S, 0)`, vertical direction
  `V ↦ (0, 1, 0)` (entries in `Dᵐᵒᵖ`, spans taken on the left over `Dᵐᵒᵖ`).
* `plane_line_cases` — the trichotomy: every line of the plane is `m`, a
  vertical `x ⊔ V`, or an intercept-direction pair `B ⊔ S`.
* `line_form_exists` — every line of the plane is the kernel of a nonzero
  linear form on the coordinates.
* `plane_collinear_iff` — the summit: `r ≤ p ⊔ q ↔ hvec r ∈ span {hvec p,
  hvec q}` — the plane's incidence IS the projective plane of `Dᵐᵒᵖ`.
* `hvec_span_inj` / `hvec_span_surj` — the atom-level correspondence is a
  bijection onto the projective points.
-/

namespace Foam.Bridges

universe u

/-! ## The abstract linear side: forms, kernels, spans over a division ring -/

section PlaneLinear

open Module

variable {K : Type*} [DivisionRing K]

/-- The linear form on `Fin 3 → K` with (right-acting) coefficients `c`. -/
def planeForm (c : Fin 3 → K) : (Fin 3 → K) →ₗ[K] K :=
  ∑ i, (LinearMap.toSpanSingleton K K (c i)).comp (LinearMap.proj i)

theorem planeForm_apply (c : Fin 3 → K) (v : Fin 3 → K) :
    planeForm c v = v 0 * c 0 + v 1 * c 1 + v 2 * c 2 := by
  simp [planeForm, Fin.sum_univ_three, LinearMap.toSpanSingleton_apply, smul_eq_mul]

theorem planeForm_surjective (c : Fin 3 → K) (hc : c ≠ 0) :
    Function.Surjective (planeForm c) := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    exact hc (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  intro e
  refine ⟨Pi.single i (e * (c i)⁻¹), ?_⟩
  have h1 : planeForm c (Pi.single i (e * (c i)⁻¹)) = (e * (c i)⁻¹) * c i := by
    simp only [planeForm, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h1, mul_assoc, inv_mul_cancel₀ hi, mul_one]

theorem finrank_ker_planeForm (c : Fin 3 → K) (hc : c ≠ 0) :
    Module.finrank K (LinearMap.ker (planeForm c)) = 2 := by
  have hrange : LinearMap.range (planeForm c) = ⊤ :=
    LinearMap.range_eq_top.mpr (planeForm_surjective c hc)
  have h := LinearMap.finrank_range_add_finrank_ker (planeForm c)
  rw [hrange] at h
  have h3 : Module.finrank K (Fin 3 → K) = 3 := by simp
  have h1 : Module.finrank K (⊤ : Submodule K K) = 1 := by
    rw [finrank_top]
    exact Module.finrank_self _
  rw [h1, h3] at h
  omega

theorem plane_pair_independent {V : Type*} [AddCommGroup V] [Module K V]
    {u v : V} (hu : u ≠ 0) (hv : v ∉ Submodule.span K {u}) :
    LinearIndependent K ![u, v] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h | h
    · exact ⟨h, rfl⟩
    · exact absurd h hu
  · exfalso
    apply hv
    have h1 : t • v = -(s • u) := eq_neg_of_add_eq_zero_right hst
    have h2 : v = (-(t⁻¹ * s)) • u := by
      calc v = (t⁻¹ * t) • v := by rw [inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • (t • v) := by rw [mul_smul]
        _ = t⁻¹ • (-(s • u)) := by rw [h1]
        _ = -(t⁻¹ • s • u) := by rw [smul_neg]
        _ = (-(t⁻¹ * s)) • u := by rw [neg_smul, mul_smul]
    exact h2 ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)

theorem plane_span_pair_finrank {V : Type*} [AddCommGroup V] [Module K V]
    {u v : V} (hu : u ≠ 0) (hv : v ∉ Submodule.span K {u}) :
    Module.finrank K (Submodule.span K ({u, v} : Set V)) = 2 := by
  have h := finrank_span_eq_card (R := K) (plane_pair_independent hu hv)
  have hrange : Set.range ![u, v] = ({u, v} : Set V) := by
    ext w
    simp [Matrix.range_cons, Matrix.range_empty, or_comm]
  rw [hrange] at h
  simpa using h

theorem plane_span_pair_eq_ker {u v : Fin 3 → K} (c : Fin 3 → K) (hc : c ≠ 0)
    (hu : u ≠ 0) (hv : v ∉ Submodule.span K {u})
    (hu_mem : u ∈ LinearMap.ker (planeForm c))
    (hv_mem : v ∈ LinearMap.ker (planeForm c)) :
    Submodule.span K {u, v} = LinearMap.ker (planeForm c) := by
  have h_le : Submodule.span K {u, v} ≤ LinearMap.ker (planeForm c) := by
    rw [Submodule.span_le]
    rintro w (rfl | rfl)
    · exact hu_mem
    · exact hv_mem
  refine Submodule.eq_of_le_of_finrank_le h_le ?_
  rw [finrank_ker_planeForm c hc, plane_span_pair_finrank hu hv]

theorem neg_add_eq_zero' {G : Type*} [AddGroup G] {a b : G} :
    -a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have h1 := congrArg (fun z => a + z) h
    rw [← add_assoc, add_neg_cancel, zero_add, add_zero] at h1
    exact h1.symm
  · intro h
    rw [h, neg_add_cancel]

theorem add_neg_eq_zero' {G : Type*} [AddGroup G] {a b : G} :
    a + -b = 0 ↔ a = b := by
  constructor
  · intro h
    have h1 := congrArg (fun z => z + b) h
    rwa [add_assoc, neg_add_cancel, add_zero, zero_add] at h1
  · intro h
    rw [h, add_neg_cancel]

theorem shift_eq_iff {G : Type*} [AddGroup G] {A y b : G} :
    -A + y + -b = 0 ↔ y = A + b := by
  constructor
  · intro h0
    have h1 := congrArg (fun z => A + z) h0
    rw [add_zero] at h1
    have h2 : A + (-A + y + -b) = y + -b := by
      rw [← add_assoc, ← add_assoc, add_neg_cancel, zero_add]
    rw [h2] at h1
    have h3 := congrArg (fun z => z + b) h1
    rw [add_assoc, neg_add_cancel, add_zero] at h3
    exact h3
  · intro h0
    rw [h0, ← add_assoc, neg_add_cancel, zero_add, add_neg_cancel]

theorem span_singleton_smul {K : Type*} [DivisionRing K] {V : Type*}
    [AddCommGroup V] [Module K V] {a : K} (ha : a ≠ 0) (v : V) :
    Submodule.span K {a • v} = Submodule.span K {v} := by
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · rw [Submodule.span_singleton_le_iff_mem]
    have h : a⁻¹ • (a • v) ∈ Submodule.span K {a • v} :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h

end PlaneLinear

/-! ## The lattice side: two atoms regenerate their line, traces are atoms,
and every line of the plane is `m`, a vertical, or an intercept-direction pair -/

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

omit [ComplementedLattice L] [IsAtomistic L] in
theorem line_eq_of_two_atoms_le {a b p q : L}
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (hp : IsAtom p) (hq : IsAtom q) (hpq : p ≠ q)
    (hp_le : p ≤ a ⊔ b) (hq_le : q ≤ a ⊔ b) :
    p ⊔ q = a ⊔ b := by
  have hp_cov := line_covers_its_atoms ha hb hab hp hp_le
  have h_lt : p < p ⊔ q := lt_of_le_of_ne le_sup_left
    (fun h => hpq (IsAtom.eq_of_le hq hp (h ▸ le_sup_right)).symm)
  exact (hp_cov.eq_or_eq h_lt.le (sup_le hp_le hq_le)).resolve_left (ne_of_gt h_lt)

omit [ComplementedLattice L] in
theorem trace_atom {p q w z : L}
    (hp : IsAtom p) (hq : IsAtom q) (hpq : p ≠ q)
    (h_cov : w ⋖ z) (h_le : p ⊔ q ≤ z) (h_not : ¬ p ⊔ q ≤ w) :
    IsAtom ((p ⊔ q) ⊓ w) := by
  have hp_lt : p < p ⊔ q := lt_of_le_of_ne le_sup_left
    (fun h => hpq (IsAtom.eq_of_le hq hp (h ▸ le_sup_right)).symm)
  have h_ne_bot : w ⊓ (p ⊔ q) ≠ ⊥ :=
    lines_meet_if_coplanar h_cov h_le h_not hp hp_lt
  exact line_height_two hp hq hpq
    (bot_lt_iff_ne_bot.mpr (by rwa [inf_comm] at h_ne_bot))
    (lt_of_le_of_ne inf_le_left (fun h => h_not (inf_eq_left.mp h)))

variable {Γ : CoordSystem L}

theorem CoordSystem.plane_line_cases (Γ : CoordSystem L) {p q : L}
    (hp : IsAtom p) (hq : IsAtom q) (hpq : p ≠ q)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hq_π : q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    p ⊔ q = Γ.U ⊔ Γ.V ∨
    (∃ x, IsAtom x ∧ x ≤ Γ.O ⊔ Γ.U ∧ x ≠ Γ.U ∧ p ⊔ q = x ⊔ Γ.V) ∨
    (∃ S B, IsAtom S ∧ S ≤ Γ.U ⊔ Γ.V ∧ S ≠ Γ.V ∧
      IsAtom B ∧ B ≤ Γ.O ⊔ Γ.V ∧ B ≠ Γ.V ∧ p ⊔ q = B ⊔ S) := by
  have hpq_π : p ⊔ q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := sup_le hp_π hq_π
  by_cases hm : p ⊔ q ≤ Γ.U ⊔ Γ.V
  · exact Or.inl (line_eq_of_two_atoms_le Γ.hU Γ.hV Γ.hUV hp hq hpq
      (le_sup_left.trans hm) (le_sup_right.trans hm))
  · have hS_atom : IsAtom ((p ⊔ q) ⊓ (Γ.U ⊔ Γ.V)) :=
      trace_atom hp hq hpq Γ.m_covBy_π hpq_π hm
    have hS_le : (p ⊔ q) ⊓ (Γ.U ⊔ Γ.V) ≤ p ⊔ q := inf_le_left
    have hS_m : (p ⊔ q) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V := inf_le_right
    by_cases hSV : (p ⊔ q) ⊓ (Γ.U ⊔ Γ.V) = Γ.V
    · have hV_le : Γ.V ≤ p ⊔ q := hSV ▸ hS_le
      have h_not_l : ¬ p ⊔ q ≤ Γ.O ⊔ Γ.U := fun h => Γ.hV_off (hV_le.trans h)
      have hx_atom : IsAtom ((p ⊔ q) ⊓ (Γ.O ⊔ Γ.U)) :=
        trace_atom hp hq hpq Γ.l_covBy_π hpq_π h_not_l
      have hx_le : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.U) ≤ p ⊔ q := inf_le_left
      have hx_l : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.U) ≤ Γ.O ⊔ Γ.U := inf_le_right
      have hx_ne_U : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.U) ≠ Γ.U := by
        intro h
        have hU_le : Γ.U ≤ p ⊔ q := h ▸ hx_le
        exact hm (line_eq_of_two_atoms_le hp hq hpq Γ.hU Γ.hV Γ.hUV hU_le hV_le).ge
      have hx_ne_V : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.U) ≠ Γ.V :=
        fun h => Γ.hV_off (h ▸ hx_l)
      exact Or.inr (Or.inl ⟨_, hx_atom, hx_l, hx_ne_U,
        (line_eq_of_two_atoms_le hp hq hpq hx_atom Γ.hV hx_ne_V hx_le hV_le).symm⟩)
    · have h_not_n : ¬ p ⊔ q ≤ Γ.O ⊔ Γ.V := by
        intro h
        apply hSV
        apply IsAtom.eq_of_le hS_atom Γ.hV
        calc (p ⊔ q) ⊓ (Γ.U ⊔ Γ.V) ≤ (Γ.O ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.V) :=
              inf_le_inf_right _ h
          _ = Γ.V := Γ.n_inf_m_eq_V
      have hn_cov : Γ.O ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V :=
        Γ.sup_V_covBy_π Γ.hO le_sup_left Γ.hOU
      have hB_atom : IsAtom ((p ⊔ q) ⊓ (Γ.O ⊔ Γ.V)) :=
        trace_atom hp hq hpq hn_cov hpq_π h_not_n
      have hB_le : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.V) ≤ p ⊔ q := inf_le_left
      have hB_n : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.V) ≤ Γ.O ⊔ Γ.V := inf_le_right
      have hB_ne_V : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.V) ≠ Γ.V := by
        intro h
        have hV_le : Γ.V ≤ p ⊔ q := h ▸ hB_le
        have h_eq : Γ.V ⊔ ((p ⊔ q) ⊓ (Γ.U ⊔ Γ.V)) = p ⊔ q :=
          line_eq_of_two_atoms_le hp hq hpq Γ.hV hS_atom (Ne.symm hSV) hV_le hS_le
        apply hm
        rw [← h_eq]
        exact sup_le le_sup_right hS_m
      have hB_ne_S : (p ⊔ q) ⊓ (Γ.O ⊔ Γ.V) ≠ (p ⊔ q) ⊓ (Γ.U ⊔ Γ.V) := by
        intro h
        apply hSV
        apply IsAtom.eq_of_le hS_atom Γ.hV
        have h1 : (p ⊔ q) ⊓ (Γ.U ⊔ Γ.V) ≤ (Γ.O ⊔ Γ.V) ⊓ (Γ.U ⊔ Γ.V) :=
          le_inf (h ▸ hB_n) hS_m
        exact h1.trans_eq Γ.n_inf_m_eq_V
      exact Or.inr (Or.inr ⟨_, _, hS_atom, hS_m, hSV, hB_atom, hB_n, hB_ne_V,
        (line_eq_of_two_atoms_le hp hq hpq hB_atom hS_atom hB_ne_S hB_le hS_le).symm⟩)

/-! ## Chart extensionality and surjectivity -/

theorem CoordSystem.affine_ext (Γ : CoordSystem L) {p p' : L}
    (hp : IsAtom p) (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.m)
    (hp' : IsAtom p') (hp'_π : p' ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp'_aff : ¬ p' ≤ Γ.m)
    (hx : Γ.xproj p = Γ.xproj p') (hy : Γ.ycoord p = Γ.ycoord p') : p = p' := by
  have hV_sup : p ⊔ Γ.V = p' ⊔ Γ.V :=
    Γ.sup_V_eq_of_xproj_eq hp hp_π hp_aff hp' hp'_π hp'_aff hx
  have hU_sup : p ⊔ Γ.U = p' ⊔ Γ.U :=
    Γ.sup_U_eq_of_ycoord_eq hp hp_π hp_aff hp' hp'_π hp'_aff hy
  have h1 : (p ⊔ Γ.V) ⊓ (p ⊔ Γ.U) = p :=
    modular_intersection hp Γ.hV Γ.hU (Γ.ne_V_of_affine hp_aff)
      (Γ.ne_U_of_affine hp_aff) Γ.hUV.symm (Γ.U_not_le_sup_V hp hp_aff)
  have h2 : (p' ⊔ Γ.V) ⊓ (p' ⊔ Γ.U) = p' :=
    modular_intersection hp' Γ.hV Γ.hU (Γ.ne_V_of_affine hp'_aff)
      (Γ.ne_U_of_affine hp'_aff) Γ.hUV.symm (Γ.U_not_le_sup_V hp' hp'_aff)
  rw [← h1, hV_sup, hU_sup, h2]

theorem CoordSystem.exists_affine_with_coords (Γ : CoordSystem L) {x y : L}
    (hx : IsAtom x) (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_ne : x ≠ Γ.U)
    (hy : IsAtom y) (hy_l : y ≤ Γ.O ⊔ Γ.U) (hy_ne : y ≠ Γ.U) :
    ∃ p : L, IsAtom p ∧ p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ∧ ¬ p ≤ Γ.U ⊔ Γ.V ∧
      Γ.xproj p = x ∧ Γ.ycoord p = y := by
  have hys_atom := Γ.yseat_is_atom hy hy_l hy_ne
  have hys_n := Γ.yseat_le_n y
  have hys_ne_V := Γ.yseat_ne_V hy hy_l hy_ne
  have hp_atom := Γ.point_is_atom hx hx_l hx_ne hys_atom hys_n hys_ne_V
  have hp_π := Γ.point_le_π (y := Γ.yseat y) hx_l
  have hp_aff := Γ.point_affine hx hx_l hx_ne hys_atom hys_n hys_ne_V
  refine ⟨Γ.point x (Γ.yseat y), hp_atom, hp_π, hp_aff,
    Γ.xproj_point hx hx_l hx_ne hys_atom hys_n hys_ne_V, ?_⟩
  have h1 : Γ.ycoord (Γ.yproj (Γ.point x (Γ.yseat y))) =
      Γ.ycoord (Γ.point x (Γ.yseat y)) :=
    Γ.ycoord_yproj hp_atom hp_π hp_aff
  rw [Γ.yproj_point hx hx_l hx_ne hys_atom hys_n hys_ne_V] at h1
  rw [← h1]
  exact Γ.ycoord_yseat hy hy_l hy_ne

/-! ## The slope is injective and surjective on directions -/

theorem CoordSystem.slope_seat (Γ : CoordSystem L) {S : L} (hS : IsAtom S)
    (hS_m : S ≤ Γ.U ⊔ Γ.V) (_hS_ne_U : S ≠ Γ.U) (hS_ne_V : S ≠ Γ.V) :
    IsAtom ((Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V)) ∧
    ((Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) ∧
    ¬ (Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V ∧
    Γ.xproj ((Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V)) = Γ.I ∧
    Γ.O ⊔ ((Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V)) = Γ.O ⊔ S := by
  have hO_ne_S : Γ.O ≠ S := fun h => Γ.hO_not_m (h ▸ hS_m)
  have hOS_π : Γ.O ⊔ S ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    sup_le (le_sup_left.trans le_sup_left) (hS_m.trans Γ.m_le_π)
  have hO_not_IV : ¬ Γ.O ≤ Γ.I ⊔ Γ.V := by
    intro h
    apply Γ.hV_off
    have h_line : Γ.I ⊔ Γ.V = Γ.I ⊔ Γ.O :=
      line_eq_of_atom_le' Γ.hI Γ.hV Γ.hO Γ.hI_ne_V (fun h' => Γ.hOI h'.symm) h
    have h_l : Γ.I ⊔ Γ.O = Γ.O ⊔ Γ.U :=
      line_eq_of_two_atoms_le Γ.hO Γ.hU Γ.hOU Γ.hI Γ.hO (fun h' => Γ.hOI h'.symm)
        Γ.hI_on le_sup_left
    exact (le_sup_right.trans h_line.le).trans h_l.le
  have h_not_IV : ¬ Γ.O ⊔ S ≤ Γ.I ⊔ Γ.V := fun h => hO_not_IV (le_sup_left.trans h)
  have hIV_cov : Γ.I ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V :=
    Γ.sup_V_covBy_π Γ.hI Γ.hI_on Γ.hUI.symm
  have hM_atom : IsAtom ((Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V)) :=
    trace_atom Γ.hO hS hO_ne_S hIV_cov hOS_π h_not_IV
  have hM_le_OS : (Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) ≤ Γ.O ⊔ S := inf_le_left
  have hM_le_IV : (Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) ≤ Γ.I ⊔ Γ.V := inf_le_right
  have hOS_inf_m : (Γ.O ⊔ S) ⊓ (Γ.U ⊔ Γ.V) = S :=
    line_direction Γ.hO Γ.hO_not_m hS_m
  have hM_ne_V : (Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) ≠ Γ.V := by
    intro h
    apply hS_ne_V
    have hV_le : Γ.V ≤ Γ.O ⊔ S := h ▸ hM_le_OS
    exact (IsAtom.eq_of_le Γ.hV hS
      ((le_inf hV_le le_sup_right).trans_eq hOS_inf_m)).symm
  have hM_aff : ¬ (Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V := by
    intro h
    apply hM_ne_V
    apply IsAtom.eq_of_le hM_atom Γ.hV
    exact (le_inf hM_le_IV h).trans_eq Γ.IV_inf_m_eq_V
  have hM_π : (Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := hM_le_OS.trans hOS_π
  have hMV_eq : (Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) ⊔ Γ.V = Γ.I ⊔ Γ.V :=
    line_eq_of_two_atoms_le Γ.hI Γ.hV Γ.hI_ne_V hM_atom Γ.hV hM_ne_V
      hM_le_IV le_sup_right
  have hM_x : Γ.xproj ((Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V)) = Γ.I := by
    show ((Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) ⊔ Γ.V) ⊓ (Γ.O ⊔ Γ.U) = Γ.I
    rw [hMV_eq, inf_comm]
    exact Γ.l_inf_IV_eq_I
  have hO_ne_M : Γ.O ≠ (Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) :=
    fun h => hO_not_IV (h ▸ hM_le_IV)
  exact ⟨hM_atom, hM_π, hM_aff, hM_x,
    (line_eq_of_atom_le' Γ.hO hS hM_atom hO_ne_S hO_ne_M hM_le_OS).symm⟩

theorem CoordSystem.slope_inj (Γ : CoordSystem L) {S S' : L}
    (hS : IsAtom S) (hS_m : S ≤ Γ.U ⊔ Γ.V) (hS_ne_V : S ≠ Γ.V)
    (hS' : IsAtom S') (hS'_m : S' ≤ Γ.U ⊔ Γ.V) (hS'_ne_V : S' ≠ Γ.V)
    (h : Γ.slope S = Γ.slope S') : S = S' := by
  by_cases hSU : S = Γ.U
  · by_cases hS'U : S' = Γ.U
    · rw [hSU, hS'U]
    · exfalso
      subst hSU
      rw [Γ.slope_U] at h
      exact (Γ.slope_facts hS' hS'_m hS'U hS'_ne_V).2.2.1 h.symm
  · by_cases hS'U : S' = Γ.U
    · exfalso
      subst hS'U
      rw [Γ.slope_U] at h
      exact (Γ.slope_facts hS hS_m hSU hS_ne_V).2.2.1 h
    · obtain ⟨hM_atom, hM_π, hM_aff, hM_x, hM_ray⟩ :=
        Γ.slope_seat hS hS_m hSU hS_ne_V
      obtain ⟨hM'_atom, hM'_π, hM'_aff, hM'_x, hM'_ray⟩ :=
        Γ.slope_seat hS' hS'_m hS'U hS'_ne_V
      have h' : Γ.ycoord ((Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V)) =
          Γ.ycoord ((Γ.O ⊔ S') ⊓ (Γ.I ⊔ Γ.V)) := h
      have hMM' : (Γ.O ⊔ S) ⊓ (Γ.I ⊔ Γ.V) = (Γ.O ⊔ S') ⊓ (Γ.I ⊔ Γ.V) :=
        Γ.affine_ext hM_atom hM_π hM_aff hM'_atom hM'_π hM'_aff
          (hM_x.trans hM'_x.symm) h'
      have hray : Γ.O ⊔ S = Γ.O ⊔ S' := by
        rw [← hM_ray, hMM', hM'_ray]
      calc S = (Γ.O ⊔ S) ⊓ (Γ.U ⊔ Γ.V) :=
            (line_direction Γ.hO Γ.hO_not_m hS_m).symm
        _ = (Γ.O ⊔ S') ⊓ (Γ.U ⊔ Γ.V) := by rw [hray]
        _ = S' := line_direction Γ.hO Γ.hO_not_m hS'_m

theorem CoordSystem.slope_surj (Γ : CoordSystem L) {d : L}
    (hd : IsAtom d) (hd_l : d ≤ Γ.O ⊔ Γ.U) (hd_ne : d ≠ Γ.U) :
    ∃ S, IsAtom S ∧ S ≤ Γ.U ⊔ Γ.V ∧ S ≠ Γ.V ∧ Γ.slope S = d := by
  by_cases hdO : d = Γ.O
  · exact ⟨Γ.U, Γ.hU, le_sup_left, Γ.hUV, by rw [Γ.slope_U, hdO]⟩
  · obtain ⟨M, hM_atom, hM_π, hM_aff, hM_x, hM_y⟩ :=
      Γ.exists_affine_with_coords Γ.hI Γ.hI_on Γ.hUI.symm hd hd_l hd_ne
    have hM_ne_O : M ≠ Γ.O := by
      intro h
      have h1 : Γ.I = Γ.O := by
        rw [← hM_x, h, Γ.xproj_of_on_l Γ.hO le_sup_left Γ.hOU]
      exact Γ.hOI h1.symm
    have hO_ne_M : Γ.O ≠ M := fun h => hM_ne_O h.symm
    have hM_ne_V : M ≠ Γ.V := Γ.ne_V_of_affine hM_aff
    have hOM_π : Γ.O ⊔ M ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
      sup_le (le_sup_left.trans le_sup_left) hM_π
    have h_not_m : ¬ Γ.O ⊔ M ≤ Γ.U ⊔ Γ.V :=
      fun h => Γ.hO_not_m (le_sup_left.trans h)
    have hS_atom : IsAtom ((Γ.O ⊔ M) ⊓ (Γ.U ⊔ Γ.V)) :=
      trace_atom Γ.hO hM_atom hO_ne_M Γ.m_covBy_π hOM_π h_not_m
    have hS_le : (Γ.O ⊔ M) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.O ⊔ M := inf_le_left
    have hS_m : (Γ.O ⊔ M) ⊓ (Γ.U ⊔ Γ.V) ≤ Γ.U ⊔ Γ.V := inf_le_right
    have hS_ne_V : (Γ.O ⊔ M) ⊓ (Γ.U ⊔ Γ.V) ≠ Γ.V := by
      intro h
      have hV_le : Γ.V ≤ Γ.O ⊔ M := h ▸ hS_le
      have h_line : Γ.O ⊔ M = Γ.O ⊔ Γ.V :=
        line_eq_of_atom_le' Γ.hO hM_atom Γ.hV hO_ne_M Γ.hOV hV_le
      have hM_n : M ≤ Γ.O ⊔ Γ.V := h_line ▸ (le_sup_right : M ≤ Γ.O ⊔ M)
      have hMV_le : M ⊔ Γ.V ≤ Γ.O ⊔ Γ.V := sup_le hM_n le_sup_right
      have hxM_le : Γ.xproj M ≤ Γ.O := by
        have h1 : Γ.xproj M ≤ (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.V) :=
          le_inf inf_le_right (inf_le_left.trans hMV_le)
        rwa [Γ.l_inf_n_eq_O] at h1
      exact Γ.hOI (IsAtom.eq_of_le Γ.hI Γ.hO (hM_x ▸ hxM_le)).symm
    have hO_ne_S : Γ.O ≠ (Γ.O ⊔ M) ⊓ (Γ.U ⊔ Γ.V) :=
      fun h => Γ.hO_not_m (h ▸ hS_m)
    have h_ray : Γ.O ⊔ M = Γ.O ⊔ ((Γ.O ⊔ M) ⊓ (Γ.U ⊔ Γ.V)) :=
      line_eq_of_atom_le' Γ.hO hM_atom hS_atom hO_ne_M hO_ne_S hS_le
    have hM_IV : M ≤ Γ.I ⊔ Γ.V := by
      have h1 := Γ.sup_V_xproj hM_atom hM_π hM_aff
      rw [hM_x] at h1
      exact le_sup_left.trans h1.le
    have hMV_eq : M ⊔ Γ.V = Γ.I ⊔ Γ.V :=
      line_eq_of_two_atoms_le Γ.hI Γ.hV Γ.hI_ne_V hM_atom Γ.hV hM_ne_V
        hM_IV le_sup_right
    have hV_not : ¬ Γ.V ≤ M ⊔ Γ.O := by
      intro hle
      apply hS_ne_V
      exact (IsAtom.eq_of_le Γ.hV hS_atom
        (le_inf (by rwa [sup_comm] at hle) le_sup_right)).symm
    have h_seat : (Γ.O ⊔ ((Γ.O ⊔ M) ⊓ (Γ.U ⊔ Γ.V))) ⊓ (Γ.I ⊔ Γ.V) = M := by
      rw [← h_ray, ← hMV_eq, sup_comm Γ.O M]
      exact modular_intersection hM_atom Γ.hO Γ.hV hM_ne_O hM_ne_V Γ.hOV hV_not
    refine ⟨(Γ.O ⊔ M) ⊓ (Γ.U ⊔ Γ.V), hS_atom, hS_m, hS_ne_V, ?_⟩
    show Γ.ycoord ((Γ.O ⊔ ((Γ.O ⊔ M) ⊓ (Γ.U ⊔ Γ.V))) ⊓ (Γ.I ⊔ Γ.V)) = d
    rw [h_seat, hM_y]

/-! ## Homogeneous coordinates: the subtype-valued projections and `hvec` -/

instance (Γ : CoordSystem L) : Nontrivial (Coordinate Γ) :=
  ⟨⟨0, 1, fun h => Γ.hOI (congrArg Subtype.val h)⟩⟩

theorem CoordSystem.slope_facts' (Γ : CoordSystem L) {S : L} (hS : IsAtom S)
    (hS_m : S ≤ Γ.U ⊔ Γ.V) (hS_ne_V : S ≠ Γ.V) :
    IsAtom (Γ.slope S) ∧ Γ.slope S ≤ Γ.O ⊔ Γ.U ∧ Γ.slope S ≠ Γ.U := by
  by_cases hSU : S = Γ.U
  · subst hSU
    rw [Γ.slope_U]
    exact ⟨Γ.hO, le_sup_left, Γ.hOU⟩
  · obtain ⟨h1, h2, _, h4⟩ := Γ.slope_facts hS hS_m hSU hS_ne_V
    exact ⟨h1, h2, h4⟩

open Classical in
noncomputable def CoordSystem.xcoordC (Γ : CoordSystem L) (p : L) : Coordinate Γ :=
  if h : IsAtom (Γ.xproj p) ∧ Γ.xproj p ≤ Γ.O ⊔ Γ.U ∧ Γ.xproj p ≠ Γ.U then
    ⟨Γ.xproj p, h⟩ else 0

open Classical in
noncomputable def CoordSystem.ycoordC (Γ : CoordSystem L) (p : L) : Coordinate Γ :=
  if h : IsAtom (Γ.ycoord p) ∧ Γ.ycoord p ≤ Γ.O ⊔ Γ.U ∧ Γ.ycoord p ≠ Γ.U then
    ⟨Γ.ycoord p, h⟩ else 0

open Classical in
noncomputable def CoordSystem.slopeC (Γ : CoordSystem L) (S : L) : Coordinate Γ :=
  if h : IsAtom (Γ.slope S) ∧ Γ.slope S ≤ Γ.O ⊔ Γ.U ∧ Γ.slope S ≠ Γ.U then
    ⟨Γ.slope S, h⟩ else 0

theorem CoordSystem.xcoordC_val (Γ : CoordSystem L) {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.U ⊔ Γ.V) :
    (Γ.xcoordC p).1 = Γ.xproj p := by
  unfold xcoordC
  rw [dif_pos ⟨Γ.xproj_is_atom hp hp_π hp_aff, Γ.xproj_le_l p, Γ.xproj_ne_U hp hp_aff⟩]

theorem CoordSystem.ycoordC_val (Γ : CoordSystem L) {p : L} (hp : IsAtom p)
    (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hp_aff : ¬ p ≤ Γ.U ⊔ Γ.V) :
    (Γ.ycoordC p).1 = Γ.ycoord p := by
  unfold ycoordC
  rw [dif_pos ⟨Γ.ycoord_is_atom hp hp_π hp_aff, Γ.ycoord_le_l p, Γ.ycoord_ne_U hp hp_π hp_aff⟩]

theorem CoordSystem.slopeC_val (Γ : CoordSystem L) {S : L} (hS : IsAtom S)
    (hS_m : S ≤ Γ.U ⊔ Γ.V) (hS_ne_V : S ≠ Γ.V) :
    (Γ.slopeC S).1 = Γ.slope S := by
  unfold slopeC
  rw [dif_pos (Γ.slope_facts' hS hS_m hS_ne_V)]

open MulOpposite in
open Classical in
noncomputable def CoordSystem.hvec (Γ : CoordSystem L) (p : L) :
    Fin 3 → (Coordinate Γ)ᵐᵒᵖ :=
  if p = Γ.V then ![0, 1, 0]
  else if p ≤ Γ.U ⊔ Γ.V then ![1, op (Γ.slopeC p), 0]
  else ![op (Γ.xcoordC p), op (Γ.ycoordC p), 1]

open MulOpposite

theorem CoordSystem.hvec_V (Γ : CoordSystem L) :
    Γ.hvec Γ.V = ![0, 1, 0] := by
  unfold hvec
  rw [if_pos rfl]

theorem CoordSystem.hvec_dir (Γ : CoordSystem L) {S : L}
    (hS_m : S ≤ Γ.U ⊔ Γ.V) (hS_ne_V : S ≠ Γ.V) :
    Γ.hvec S = ![1, op (Γ.slopeC S), 0] := by
  unfold hvec
  rw [if_neg hS_ne_V, if_pos hS_m]

theorem CoordSystem.hvec_affine (Γ : CoordSystem L) {p : L}
    (hp_aff : ¬ p ≤ Γ.U ⊔ Γ.V) :
    Γ.hvec p = ![op (Γ.xcoordC p), op (Γ.ycoordC p), 1] := by
  have hp_ne_V : p ≠ Γ.V := fun h => hp_aff (h ▸ le_sup_right)
  unfold hvec
  rw [if_neg hp_ne_V, if_neg hp_aff]

theorem CoordSystem.op_one_ne_zero (Γ : CoordSystem L) :
    (1 : (Coordinate Γ)ᵐᵒᵖ) ≠ 0 := fun h =>
  Γ.hOI ((congrArg (fun z => (unop z).1) h).symm)

theorem CoordSystem.hvec_ne_zero (Γ : CoordSystem L) (p : L) : Γ.hvec p ≠ 0 := by
  unfold hvec
  split_ifs with h1 h2
  · intro h
    have h' := congrFun h 1
    simp at h'
    exact Γ.op_one_ne_zero h'
  · intro h
    have h' := congrFun h 0
    simp at h'
    exact Γ.op_one_ne_zero h'
  · intro h
    have h' := congrFun h 2
    simp at h'
    exact Γ.op_one_ne_zero h'

/-! ## The frame level: projective injectivity, the line forms, the summit -/

theorem Coordinate.add_val {Φ : CoordFrame L} (a b : Coordinate Φ.Γ) :
    (a + b).1 = coord_add Φ.Γ a.1 b.1 := rfl

theorem Coordinate.mul_val {Φ : CoordFrame L} (a b : Coordinate Φ.Γ) :
    (a * b).1 = coord_mul Φ.Γ a.1 b.1 := rfl

theorem CoordFrame.hvec_span_inj (Φ : CoordFrame L) {p q : L}
    (hp : IsAtom p) (hp_π : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)
    (hq : IsAtom q) (hq_π : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) (hpq : p ≠ q) :
    Φ.Γ.hvec q ∉ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {Φ.Γ.hvec p} := by
  intro hmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  by_cases hqm : q ≤ Φ.Γ.U ⊔ Φ.Γ.V
  · by_cases hpm : p ≤ Φ.Γ.U ⊔ Φ.Γ.V
    · by_cases hqV : q = Φ.Γ.V
      · by_cases hpV : p = Φ.Γ.V
        · exact hpq (hpV.trans hqV.symm)
        · rw [Φ.Γ.hvec_dir hpm hpV, hqV, Φ.Γ.hvec_V] at ha
          have h0 : a * 1 = (0 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 0
          have h1 : a * op (Φ.Γ.slopeC p) = (1 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 1
          rw [mul_one] at h0
          rw [h0, zero_mul] at h1
          exact Φ.Γ.op_one_ne_zero h1.symm
      · by_cases hpV : p = Φ.Γ.V
        · rw [hpV, Φ.Γ.hvec_V, Φ.Γ.hvec_dir hqm hqV] at ha
          have h0 : a * 0 = (1 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 0
          rw [mul_zero] at h0
          exact Φ.Γ.op_one_ne_zero h0.symm
        · rw [Φ.Γ.hvec_dir hpm hpV, Φ.Γ.hvec_dir hqm hqV] at ha
          have h0 : a * 1 = (1 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 0
          have h1 : a * op (Φ.Γ.slopeC p) = op (Φ.Γ.slopeC q) := congrFun ha 1
          rw [mul_one] at h0
          rw [h0, one_mul] at h1
          have h3 : Φ.Γ.slope p = Φ.Γ.slope q := by
            rw [← Φ.Γ.slopeC_val hp hpm hpV, ← Φ.Γ.slopeC_val hq hqm hqV,
              op_injective h1]
          exact hpq (Φ.Γ.slope_inj hp hpm hpV hq hqm hqV h3)
    · rw [Φ.Γ.hvec_affine hpm] at ha
      by_cases hqV : q = Φ.Γ.V
      · rw [hqV, Φ.Γ.hvec_V] at ha
        have h2 : a * 1 = (0 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 2
        have h1 : a * op (Φ.Γ.ycoordC p) = (1 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 1
        rw [mul_one] at h2
        rw [h2, zero_mul] at h1
        exact Φ.Γ.op_one_ne_zero h1.symm
      · rw [Φ.Γ.hvec_dir hqm hqV] at ha
        have h2 : a * 1 = (0 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 2
        have h0 : a * op (Φ.Γ.xcoordC p) = (1 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 0
        rw [mul_one] at h2
        rw [h2, zero_mul] at h0
        exact Φ.Γ.op_one_ne_zero h0.symm
  · by_cases hpm : p ≤ Φ.Γ.U ⊔ Φ.Γ.V
    · rw [Φ.Γ.hvec_affine hqm] at ha
      by_cases hpV : p = Φ.Γ.V
      · rw [hpV, Φ.Γ.hvec_V] at ha
        have h2 : a * 0 = (1 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 2
        rw [mul_zero] at h2
        exact Φ.Γ.op_one_ne_zero h2.symm
      · rw [Φ.Γ.hvec_dir hpm hpV] at ha
        have h2 : a * 0 = (1 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 2
        rw [mul_zero] at h2
        exact Φ.Γ.op_one_ne_zero h2.symm
    · rw [Φ.Γ.hvec_affine hpm, Φ.Γ.hvec_affine hqm] at ha
      have h2 : a * 1 = (1 : (Coordinate Φ.Γ)ᵐᵒᵖ) := congrFun ha 2
      have h0 : a * op (Φ.Γ.xcoordC p) = op (Φ.Γ.xcoordC q) := congrFun ha 0
      have h1 : a * op (Φ.Γ.ycoordC p) = op (Φ.Γ.ycoordC q) := congrFun ha 1
      rw [mul_one] at h2
      rw [h2, one_mul] at h0 h1
      have hx : Φ.Γ.xproj p = Φ.Γ.xproj q := by
        rw [← Φ.Γ.xcoordC_val hp hp_π hpm, ← Φ.Γ.xcoordC_val hq hq_π hqm,
          op_injective h0]
      have hy : Φ.Γ.ycoord p = Φ.Γ.ycoord q := by
        rw [← Φ.Γ.ycoordC_val hp hp_π hpm, ← Φ.Γ.ycoordC_val hq hq_π hqm,
          op_injective h1]
      exact hpq (Φ.Γ.affine_ext hp hp_π hpm hq hq_π hqm hx hy)

/-! ## The three line forms -/

theorem CoordFrame.m_form (Φ : CoordFrame L) :
    ∃ c : Fin 3 → (Coordinate Φ.Γ)ᵐᵒᵖ, c ≠ 0 ∧
      ∀ t, IsAtom t → t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V →
        (t ≤ Φ.Γ.U ⊔ Φ.Γ.V ↔ planeForm c (Φ.Γ.hvec t) = 0) := by
  refine ⟨![0, 0, 1], ?_, ?_⟩
  · intro h
    exact Φ.Γ.op_one_ne_zero (congrFun h 2)
  · intro t ht ht_π
    by_cases htm : t ≤ Φ.Γ.U ⊔ Φ.Γ.V
    · refine iff_of_true htm ?_
      by_cases htV : t = Φ.Γ.V
      · rw [htV, Φ.Γ.hvec_V, planeForm_apply]
        show (0 : (Coordinate Φ.Γ)ᵐᵒᵖ) * 0 + 1 * 0 + 0 * 1 = 0
        rw [mul_zero, mul_zero, zero_mul, add_zero, add_zero]
      · rw [Φ.Γ.hvec_dir htm htV, planeForm_apply]
        show (1 : (Coordinate Φ.Γ)ᵐᵒᵖ) * 0 + op (Φ.Γ.slopeC t) * 0 + 0 * 1 = 0
        rw [mul_zero, mul_zero, zero_mul, add_zero, add_zero]
    · refine iff_of_false htm ?_
      rw [Φ.Γ.hvec_affine htm, planeForm_apply]
      show ¬ (op (Φ.Γ.xcoordC t) * 0 + op (Φ.Γ.ycoordC t) * 0 + 1 * 1 = 0)
      rw [mul_zero, mul_zero, one_mul, add_zero, zero_add]
      exact Φ.Γ.op_one_ne_zero

theorem CoordFrame.vertical_form (Φ : CoordFrame L) {x : L}
    (hx : IsAtom x) (hx_l : x ≤ Φ.Γ.O ⊔ Φ.Γ.U) (hx_ne : x ≠ Φ.Γ.U) :
    ∃ c : Fin 3 → (Coordinate Φ.Γ)ᵐᵒᵖ, c ≠ 0 ∧
      ∀ t, IsAtom t → t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V →
        (t ≤ x ⊔ Φ.Γ.V ↔ planeForm c (Φ.Γ.hvec t) = 0) := by
  have hx_aff : ¬ x ≤ Φ.Γ.U ⊔ Φ.Γ.V := Φ.Γ.affine_of_on_l hx hx_l hx_ne
  have hx_π : x ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V := hx_l.trans le_sup_left
  refine ⟨![1, 0, op (-(Φ.Γ.xcoordC x))], ?_, ?_⟩
  · intro h
    exact Φ.Γ.op_one_ne_zero (congrFun h 0)
  · intro t ht ht_π
    by_cases htm : t ≤ Φ.Γ.U ⊔ Φ.Γ.V
    · by_cases htV : t = Φ.Γ.V
      · refine iff_of_true (htV ▸ le_sup_right) ?_
        rw [htV, Φ.Γ.hvec_V, planeForm_apply]
        show (0 : (Coordinate Φ.Γ)ᵐᵒᵖ) * 1 + 1 * 0 + 0 *
          op (-(Φ.Γ.xcoordC x)) = 0
        rw [zero_mul, mul_zero, zero_mul, add_zero, add_zero]
      · refine iff_of_false ?_ ?_
        · intro hle
          exact htV (IsAtom.eq_of_le ht Φ.Γ.hV
            ((le_inf hle htm).trans_eq (Φ.Γ.vertical_inf_m hx hx_l hx_ne)))
        · rw [Φ.Γ.hvec_dir htm htV, planeForm_apply]
          show ¬ ((1 : (Coordinate Φ.Γ)ᵐᵒᵖ) * 1 + op (Φ.Γ.slopeC t) * 0 + 0 *
            op (-(Φ.Γ.xcoordC x)) = 0)
          rw [one_mul, mul_zero, zero_mul, add_zero, add_zero]
          exact Φ.Γ.op_one_ne_zero
    · rw [Φ.Γ.hvec_affine htm, planeForm_apply]
      show t ≤ x ⊔ Φ.Γ.V ↔ op (Φ.Γ.xcoordC t) * 1 + op (Φ.Γ.ycoordC t) * 0 + 1 *
        op (-(Φ.Γ.xcoordC x)) = 0
      rw [mul_one, mul_zero, add_zero, one_mul,
        ← MulOpposite.op_add, MulOpposite.op_eq_zero_iff, add_neg_eq_zero']
      have hxx : (Φ.Γ.xcoordC t = Φ.Γ.xcoordC x) ↔ (Φ.Γ.xproj t = x) := by
        constructor
        · intro h
          have h1 := congrArg Subtype.val h
          rw [Φ.Γ.xcoordC_val ht ht_π htm, Φ.Γ.xcoordC_val hx hx_π hx_aff,
            Φ.Γ.xproj_of_on_l hx hx_l hx_ne] at h1
          exact h1
        · intro h
          apply Subtype.ext
          rw [Φ.Γ.xcoordC_val ht ht_π htm, Φ.Γ.xcoordC_val hx hx_π hx_aff,
            Φ.Γ.xproj_of_on_l hx hx_l hx_ne]
          exact h
      rw [hxx]
      exact Φ.Γ.le_vertical_iff ht htm hx hx_l hx_ne

theorem CoordFrame.general_form (Φ : CoordFrame L) {S B : L}
    (hS : IsAtom S) (hS_m : S ≤ Φ.Γ.U ⊔ Φ.Γ.V) (hS_ne_V : S ≠ Φ.Γ.V)
    (hB : IsAtom B) (hB_n : B ≤ Φ.Γ.O ⊔ Φ.Γ.V) (hB_ne_V : B ≠ Φ.Γ.V) :
    ∃ c : Fin 3 → (Coordinate Φ.Γ)ᵐᵒᵖ, c ≠ 0 ∧
      ∀ t, IsAtom t → t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V →
        (t ≤ B ⊔ S ↔ planeForm c (Φ.Γ.hvec t) = 0) := by
  have hB_aff : ¬ B ≤ Φ.Γ.U ⊔ Φ.Γ.V := Φ.Γ.affine_of_on_n hB hB_n hB_ne_V
  have hB_π : B ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V :=
    hB_n.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  refine ⟨![op (-(Φ.Γ.slopeC S)), 1, op (-(Φ.Γ.ycoordC B))], ?_, ?_⟩
  · intro h
    exact Φ.Γ.op_one_ne_zero (congrFun h 1)
  · intro t ht ht_π
    have hBSm : (B ⊔ S) ⊓ (Φ.Γ.U ⊔ Φ.Γ.V) = S := line_direction hB hB_aff hS_m
    by_cases htm : t ≤ Φ.Γ.U ⊔ Φ.Γ.V
    · have hiff : t ≤ B ⊔ S ↔ t = S :=
        ⟨fun hle => IsAtom.eq_of_le ht hS ((le_inf hle htm).trans_eq hBSm),
         fun h => h ▸ le_sup_right⟩
      by_cases htV : t = Φ.Γ.V
      · refine iff_of_false ?_ ?_
        · intro hle
          apply hS_ne_V
          rw [← htV]
          exact (hiff.mp hle).symm
        · rw [htV, Φ.Γ.hvec_V, planeForm_apply]
          show ¬ ((0 : (Coordinate Φ.Γ)ᵐᵒᵖ) * op (-(Φ.Γ.slopeC S)) + 1 * 1 +
            0 * op (-(Φ.Γ.ycoordC B)) = 0)
          rw [zero_mul, zero_mul, one_mul, add_zero, zero_add]
          exact Φ.Γ.op_one_ne_zero
      · rw [Φ.Γ.hvec_dir htm htV, planeForm_apply]
        show t ≤ B ⊔ S ↔ (1 : (Coordinate Φ.Γ)ᵐᵒᵖ) * op (-(Φ.Γ.slopeC S)) +
          op (Φ.Γ.slopeC t) * 1 + 0 * op (-(Φ.Γ.ycoordC B)) = 0
        rw [one_mul, mul_one, zero_mul, add_zero, MulOpposite.op_neg,
          neg_add_eq_zero']
        rw [hiff]
        constructor
        · intro h
          rw [h]
        · intro h
          have hval : Φ.Γ.slope S = Φ.Γ.slope t := by
            rw [← Φ.Γ.slopeC_val hS hS_m hS_ne_V, ← Φ.Γ.slopeC_val ht htm htV,
              op_injective h]
          exact (Φ.Γ.slope_inj hS hS_m hS_ne_V ht htm htV hval).symm
    · rw [Φ.Γ.hvec_affine htm, planeForm_apply]
      show t ≤ B ⊔ S ↔ op (Φ.Γ.xcoordC t) * op (-(Φ.Γ.slopeC S)) +
        op (Φ.Γ.ycoordC t) * 1 + 1 * op (-(Φ.Γ.ycoordC B)) = 0
      rw [mul_one, one_mul, ← MulOpposite.op_mul, ← MulOpposite.op_add,
        ← MulOpposite.op_add, MulOpposite.op_eq_zero_iff, neg_mul, shift_eq_iff]
      have hbridge := Φ.Γ.le_line_iff hS hS_m hS_ne_V hB hB_n hB_ne_V ht ht_π htm
        Φ.P Φ.hP_atom Φ.hP_plane Φ.hP_not_l Φ.hP_not_m Φ.hP_not_OC Φ.hP_ne_I
        Φ.hP_ne_O Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred
      have hval : (Φ.Γ.ycoordC t = Φ.Γ.slopeC S * Φ.Γ.xcoordC t + Φ.Γ.ycoordC B) ↔
          (Φ.Γ.ycoord t = coord_add Φ.Γ (coord_mul Φ.Γ (Φ.Γ.slope S) (Φ.Γ.xproj t))
            (Φ.Γ.ycoord B)) := by
        constructor
        · intro h
          have h1 := congrArg Subtype.val h
          rw [Coordinate.add_val, Coordinate.mul_val, Φ.Γ.ycoordC_val ht ht_π htm,
            Φ.Γ.xcoordC_val ht ht_π htm, Φ.Γ.slopeC_val hS hS_m hS_ne_V,
            Φ.Γ.ycoordC_val hB hB_π hB_aff] at h1
          exact h1
        · intro h
          apply Subtype.ext
          rw [Coordinate.add_val, Coordinate.mul_val, Φ.Γ.ycoordC_val ht ht_π htm,
            Φ.Γ.xcoordC_val ht ht_π htm, Φ.Γ.slopeC_val hS hS_m hS_ne_V,
            Φ.Γ.ycoordC_val hB hB_π hB_aff]
          exact h
      rw [hval]
      exact hbridge

/-! ## The assembly: every line of the plane is the kernel of a form -/

theorem CoordFrame.line_form_exists (Φ : CoordFrame L) {p q : L}
    (hp : IsAtom p) (hp_π : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)
    (hq : IsAtom q) (hq_π : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) (hpq : p ≠ q) :
    ∃ c : Fin 3 → (Coordinate Φ.Γ)ᵐᵒᵖ, c ≠ 0 ∧
      ∀ t, IsAtom t → t ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V →
        (t ≤ p ⊔ q ↔ planeForm c (Φ.Γ.hvec t) = 0) := by
  rcases Φ.Γ.plane_line_cases hp hq hpq hp_π hq_π with h | ⟨x, hx, hx_l, hx_ne, h⟩ |
    ⟨S, B, hS, hS_m, hS_ne_V, hB, hB_n, hB_ne_V, h⟩
  · rw [h]
    exact Φ.m_form
  · rw [h]
    exact Φ.vertical_form hx hx_l hx_ne
  · rw [h]
    exact Φ.general_form hS hS_m hS_ne_V hB hB_n hB_ne_V

/-! ## The summit: collinearity is span membership -/

theorem CoordFrame.plane_collinear_iff (Φ : CoordFrame L) {p q r : L}
    (hp : IsAtom p) (hp_π : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)
    (hq : IsAtom q) (hq_π : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)
    (hr : IsAtom r) (hr_π : r ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) (hpq : p ≠ q) :
    r ≤ p ⊔ q ↔
      Φ.Γ.hvec r ∈ Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {Φ.Γ.hvec p, Φ.Γ.hvec q} := by
  obtain ⟨c, hc0, hchar⟩ := Φ.line_form_exists hp hp_π hq hq_π hpq
  have hspan : Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {Φ.Γ.hvec p, Φ.Γ.hvec q} =
      LinearMap.ker (planeForm c) :=
    plane_span_pair_eq_ker c hc0 (Φ.Γ.hvec_ne_zero p)
      (Φ.hvec_span_inj hp hp_π hq hq_π hpq)
      (LinearMap.mem_ker.mpr ((hchar p hp hp_π).mp le_sup_left))
      (LinearMap.mem_ker.mpr ((hchar q hq hq_π).mp le_sup_right))
  rw [hspan, LinearMap.mem_ker]
  exact hchar r hr hr_π

/-! ## Surjectivity onto the projective points -/

theorem CoordFrame.hvec_span_surj (Φ : CoordFrame L)
    (v : Fin 3 → (Coordinate Φ.Γ)ᵐᵒᵖ) (hv : v ≠ 0) :
    ∃ p : L, IsAtom p ∧ p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ∧
      Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {Φ.Γ.hvec p} =
        Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {v} := by
  by_cases h2 : v 2 = 0
  · by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
      refine ⟨Φ.Γ.V, Φ.Γ.hV, le_sup_right, ?_⟩
      have key : (v 1)⁻¹ • v = Φ.Γ.hvec Φ.Γ.V := by
        rw [Φ.Γ.hvec_V]
        funext i
        fin_cases i
        · show (v 1)⁻¹ * v 0 = 0
          rw [h0, mul_zero]
        · show (v 1)⁻¹ * v 1 = 1
          rw [inv_mul_cancel₀ h1]
        · show (v 1)⁻¹ * v 2 = 0
          rw [h2, mul_zero]
      rw [← key]
      exact span_singleton_smul (inv_ne_zero h1) v
    · obtain ⟨S, hS, hS_m, hS_ne_V, hS_slope⟩ :=
        Φ.Γ.slope_surj (unop ((v 0)⁻¹ * v 1)).2.1
          (unop ((v 0)⁻¹ * v 1)).2.2.1 (unop ((v 0)⁻¹ * v 1)).2.2.2
      refine ⟨S, hS, hS_m.trans Φ.Γ.m_le_π, ?_⟩
      have hsC : Φ.Γ.slopeC S = unop ((v 0)⁻¹ * v 1) := by
        apply Subtype.ext
        rw [Φ.Γ.slopeC_val hS hS_m hS_ne_V, hS_slope]
      have key : (v 0)⁻¹ • v = Φ.Γ.hvec S := by
        rw [Φ.Γ.hvec_dir hS_m hS_ne_V, hsC]
        funext i
        fin_cases i
        · show (v 0)⁻¹ * v 0 = 1
          rw [inv_mul_cancel₀ h0]
        · show (v 0)⁻¹ * v 1 = op (unop ((v 0)⁻¹ * v 1))
          rw [op_unop]
        · show (v 0)⁻¹ * v 2 = 0
          rw [h2, mul_zero]
      rw [← key]
      exact span_singleton_smul (inv_ne_zero h0) v
  · obtain ⟨p, hp, hp_π, hp_aff, hp_x, hp_y⟩ :=
      Φ.Γ.exists_affine_with_coords
        (unop ((v 2)⁻¹ * v 0)).2.1 (unop ((v 2)⁻¹ * v 0)).2.2.1
        (unop ((v 2)⁻¹ * v 0)).2.2.2
        (unop ((v 2)⁻¹ * v 1)).2.1 (unop ((v 2)⁻¹ * v 1)).2.2.1
        (unop ((v 2)⁻¹ * v 1)).2.2.2
    refine ⟨p, hp, hp_π, ?_⟩
    have hxC : Φ.Γ.xcoordC p = unop ((v 2)⁻¹ * v 0) := by
      apply Subtype.ext
      rw [Φ.Γ.xcoordC_val hp hp_π hp_aff, hp_x]
    have hyC : Φ.Γ.ycoordC p = unop ((v 2)⁻¹ * v 1) := by
      apply Subtype.ext
      rw [Φ.Γ.ycoordC_val hp hp_π hp_aff, hp_y]
    have key : (v 2)⁻¹ • v = Φ.Γ.hvec p := by
      rw [Φ.Γ.hvec_affine hp_aff, hxC, hyC]
      funext i
      fin_cases i
      · show (v 2)⁻¹ * v 0 = op (unop ((v 2)⁻¹ * v 0))
        rw [op_unop]
      · show (v 2)⁻¹ * v 1 = op (unop ((v 2)⁻¹ * v 1))
        rw [op_unop]
      · show (v 2)⁻¹ * v 2 = 1
        rw [inv_mul_cancel₀ h2]
    rw [← key]
    exact span_singleton_smul (inv_ne_zero h2) v

/-! ## The packaging: the plane's point map -/

noncomputable def CoordFrame.planePt (Φ : CoordFrame L) (p : L) :
    Submodule (Coordinate Φ.Γ)ᵐᵒᵖ (Fin 3 → (Coordinate Φ.Γ)ᵐᵒᵖ) :=
  Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {Φ.Γ.hvec p}

theorem CoordFrame.planePt_inj (Φ : CoordFrame L) {p q : L}
    (hp : IsAtom p) (hp_π : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)
    (hq : IsAtom q) (hq_π : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)
    (h : Φ.planePt p = Φ.planePt q) : p = q := by
  by_contra hpq
  apply Φ.hvec_span_inj hp hp_π hq hq_π hpq
  have hmem : Φ.Γ.hvec q ∈ Φ.planePt q := Submodule.mem_span_singleton_self _
  rw [← h] at hmem
  exact hmem

theorem CoordFrame.le_iff_planePt_le (Φ : CoordFrame L) {p q r : L}
    (hp : IsAtom p) (hp_π : p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)
    (hq : IsAtom q) (hq_π : q ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V)
    (hr : IsAtom r) (hr_π : r ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V) (hpq : p ≠ q) :
    r ≤ p ⊔ q ↔ Φ.planePt r ≤ Φ.planePt p ⊔ Φ.planePt q := by
  rw [Φ.plane_collinear_iff hp hp_π hq hq_π hr hr_π hpq]
  unfold CoordFrame.planePt
  rw [← Submodule.span_insert, Submodule.span_singleton_le_iff_mem]

theorem CoordFrame.planePt_surj (Φ : CoordFrame L)
    (v : Fin 3 → (Coordinate Φ.Γ)ᵐᵒᵖ) (hv : v ≠ 0) :
    ∃ p : L, IsAtom p ∧ p ≤ Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ∧
      Φ.planePt p = Submodule.span (Coordinate Φ.Γ)ᵐᵒᵖ {v} :=
  Φ.hvec_span_surj v hv

end Foam.Bridges

/-- info: 'Foam.Bridges.planeForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.planeForm

/-- info: 'Foam.Bridges.planeForm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.planeForm_apply

/-- info: 'Foam.Bridges.planeForm_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.planeForm_surjective

/-- info: 'Foam.Bridges.finrank_ker_planeForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.finrank_ker_planeForm

/-- info: 'Foam.Bridges.plane_pair_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.plane_pair_independent

/-- info: 'Foam.Bridges.plane_span_pair_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.plane_span_pair_finrank

/-- info: 'Foam.Bridges.plane_span_pair_eq_ker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.plane_span_pair_eq_ker

/-- info: 'Foam.Bridges.neg_add_eq_zero'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.neg_add_eq_zero'

/-- info: 'Foam.Bridges.add_neg_eq_zero'' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.add_neg_eq_zero'

/-- info: 'Foam.Bridges.shift_eq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.shift_eq_iff

/-- info: 'Foam.Bridges.span_singleton_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.span_singleton_smul

/-- info: 'Foam.Bridges.line_eq_of_two_atoms_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.line_eq_of_two_atoms_le

/-- info: 'Foam.Bridges.trace_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.trace_atom

/-- info: 'Foam.Bridges.CoordSystem.plane_line_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.plane_line_cases

/-- info: 'Foam.Bridges.CoordSystem.affine_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.affine_ext

/-- info: 'Foam.Bridges.CoordSystem.exists_affine_with_coords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.exists_affine_with_coords

/-- info: 'Foam.Bridges.CoordSystem.slope_seat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.slope_seat

/-- info: 'Foam.Bridges.CoordSystem.slope_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.slope_inj

/-- info: 'Foam.Bridges.CoordSystem.slope_surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.slope_surj

/-- info: 'Foam.Bridges.CoordSystem.slope_facts'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.slope_facts'

/-- info: 'Foam.Bridges.CoordSystem.xcoordC_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.xcoordC_val

/-- info: 'Foam.Bridges.CoordSystem.ycoordC_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ycoordC_val

/-- info: 'Foam.Bridges.CoordSystem.slopeC_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.slopeC_val

/-- info: 'Foam.Bridges.CoordSystem.hvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.hvec

/-- info: 'Foam.Bridges.CoordSystem.hvec_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.hvec_V

/-- info: 'Foam.Bridges.CoordSystem.hvec_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.hvec_dir

/-- info: 'Foam.Bridges.CoordSystem.hvec_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.hvec_affine

/-- info: 'Foam.Bridges.CoordSystem.op_one_ne_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.op_one_ne_zero

/-- info: 'Foam.Bridges.CoordSystem.hvec_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.hvec_ne_zero

/-- info: 'Foam.Bridges.Coordinate.add_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.Coordinate.add_val

/-- info: 'Foam.Bridges.Coordinate.mul_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.Coordinate.mul_val

/-- info: 'Foam.Bridges.CoordFrame.hvec_span_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.hvec_span_inj

/-- info: 'Foam.Bridges.CoordFrame.m_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.m_form

/-- info: 'Foam.Bridges.CoordFrame.vertical_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.vertical_form

/-- info: 'Foam.Bridges.CoordFrame.general_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.general_form

/-- info: 'Foam.Bridges.CoordFrame.line_form_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.line_form_exists

/-- info: 'Foam.Bridges.CoordFrame.plane_collinear_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.plane_collinear_iff

/-- info: 'Foam.Bridges.CoordFrame.hvec_span_surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.hvec_span_surj

/-- info: 'Foam.Bridges.CoordFrame.planePt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.planePt

/-- info: 'Foam.Bridges.CoordFrame.planePt_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.planePt_inj

/-- info: 'Foam.Bridges.CoordFrame.le_iff_planePt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.le_iff_planePt_le

/-- info: 'Foam.Bridges.CoordFrame.planePt_surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.planePt_surj
