import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.Opposite

namespace Foam.Bridges

variable {D : Type} [DivisionRing D] {V : Type} [AddCommGroup V] [Module D V]

def annih (W : Submodule D V) : Submodule Dᵐᵒᵖ (V →ₗ[D] D) where
  carrier := { f | ∀ v ∈ W, f v = 0 }
  add_mem' := fun hf hg v hv => by simp [hf v hv, hg v hv]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c _ hf v hv => by simp [hf v hv]

def annih' (U : Submodule Dᵐᵒᵖ (V →ₗ[D] D)) : Submodule D V where
  carrier := { v | ∀ f ∈ U, f v = 0 }
  add_mem' := fun hv hw f hf => by simp [hv f hf, hw f hf]
  zero_mem' := fun f _ => map_zero f
  smul_mem' := fun c _ hv f hf => by simp [hv f hf]

theorem annih_antitone {W W' : Submodule D V} (h : W ≤ W') : annih W' ≤ annih W :=
  fun _ hf v hv => hf v (h hv)

theorem annih'_antitone {U U' : Submodule Dᵐᵒᵖ (V →ₗ[D] D)} (h : U ≤ U') :
    annih' U' ≤ annih' U :=
  fun _ hv f hf => hv f (h hf)

theorem annih_galois (W : Submodule D V) (U : Submodule Dᵐᵒᵖ (V →ₗ[D] D)) :
    U ≤ annih W ↔ W ≤ annih' U :=
  ⟨fun h _ hv _ hf => h hf _ hv, fun h _ hf _ hv => h hv _ hf⟩

theorem le_annih'_annih (W : Submodule D V) : W ≤ annih' (annih W) :=
  (annih_galois W (annih W)).mp le_rfl

theorem le_annih_annih' (U : Submodule Dᵐᵒᵖ (V →ₗ[D] D)) : U ≤ annih (annih' U) :=
  (annih_galois (annih' U) U).mpr le_rfl

theorem annih'_annih_le (W : Submodule D V) : annih' (annih W) ≤ W := by
  intro v hv
  have key : ∀ φ : Module.Dual D (V ⧸ W), φ (W.mkQ v) = 0 := by
    intro φ
    have hmem : (φ ∘ₗ W.mkQ) ∈ annih W := by
      intro w hw
      show φ (W.mkQ w) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hw, map_zero]
    exact hv (φ ∘ₗ W.mkQ) hmem
  have hz : W.mkQ v = 0 := (Module.forall_dual_apply_eq_zero_iff D (W.mkQ v)).mp key
  rw [Submodule.mkQ_apply] at hz
  exact (Submodule.Quotient.mk_eq_zero W).mp hz

theorem annih'_annih_eq (W : Submodule D V) : annih' (annih W) = W :=
  le_antisymm (annih'_annih_le W) (le_annih'_annih W)

section Keystone
open Module MulOpposite
variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem coord_basis (b : Basis ι D V) (i j : ι) :
    b.coord i (b j) = if i = j then 1 else 0 := by
  rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]; simp [eq_comm]

theorem coord_linearIndependent (b : Basis ι D V) : LinearIndependent Dᵐᵒᵖ b.coord := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h : (∑ i, g i • b.coord i) (b j) = 0 := by rw [hg]; exact LinearMap.zero_apply (b j)
  rw [LinearMap.sum_apply] at h
  simp only [LinearMap.smul_apply, smul_eq_mul_unop, coord_basis, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact (unop_eq_zero_iff (g j)).mp h

theorem coord_span (b : Basis ι D V) : ⊤ ≤ Submodule.span Dᵐᵒᵖ (Set.range b.coord) := by
  intro f _
  have hf : f = ∑ i, op (f (b i)) • b.coord i := by
    apply b.ext; intro j
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul_unop, coord_basis, unop_op, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hf]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- The dual basis over the handedness `Dᵐᵒᵖ` — the construction Mathlib makes only over a
commutative field. -/
noncomputable def dualBasisOp (b : Basis ι D V) : Basis ι Dᵐᵒᵖ (Dual D V) :=
  Basis.mk (coord_linearIndependent b) (coord_span b)

theorem finrank_dual_eq (b : Basis ι D V) : finrank Dᵐᵒᵖ (Dual D V) = finrank D V := by
  rw [finrank_eq_card_basis (dualBasisOp b), finrank_eq_card_basis b]

end Keystone

section DimFormula
open Module

noncomputable def annihQuotEquiv (W : Submodule D V) : annih W ≃ₗ[Dᵐᵒᵖ] Dual D (V ⧸ W) where
  toFun f := W.liftQ f.1 (fun v hv => LinearMap.mem_ker.mpr (f.2 v hv))
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl
  invFun g := ⟨g ∘ₗ W.mkQ, fun v hv => by
    show g (W.mkQ v) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hv, map_zero]⟩
  left_inv _ := by ext v; rfl
  right_inv _ := by ext x; rfl

theorem finrank_annih [Module.Finite D V] (W : Submodule D V) :
    finrank Dᵐᵒᵖ (annih W) + finrank D W = finrank D V := by
  rw [(annihQuotEquiv W).finrank_eq, finrank_dual_eq (Module.finBasis D (V ⧸ W))]
  exact Submodule.finrank_quotient_add_finrank W

theorem le_finrank_annih' [Module.Finite D V] (U : Submodule Dᵐᵒᵖ (Dual D V)) :
    finrank D V ≤ finrank Dᵐᵒᵖ U + finrank D (annih' U) := by
  classical
  haveI : Module.Finite Dᵐᵒᵖ (Dual D V) := Module.Finite.of_basis (dualBasisOp (Module.finBasis D V))
  haveI : Module.Free Dᵐᵒᵖ U := Module.Free.of_basis (Basis.ofVectorSpace Dᵐᵒᵖ U)
  let bU := Module.finBasis Dᵐᵒᵖ U
  let g : V →ₗ[D] (Fin (finrank Dᵐᵒᵖ U) → D) := LinearMap.pi (fun i => (bU i : Dual D V))
  have hker : LinearMap.ker g ≤ annih' U := by
    intro v hv f hf
    have hvi : ∀ i, (bU i : Dual D V) v = 0 := fun i => by
      have := congrFun (LinearMap.mem_ker.mp hv) i
      simpa [g, LinearMap.pi_apply] using this
    have hsum : f = ∑ i, (bU.repr ⟨f, hf⟩ i) • (bU i : Dual D V) := by
      have h2 := congrArg (Submodule.subtype U) (bU.sum_repr ⟨f, hf⟩)
      simp only [map_sum, map_smul, Submodule.subtype_apply] at h2
      exact h2.symm
    rw [hsum, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [LinearMap.smul_apply, hvi i, MulOpposite.smul_eq_mul_unop, zero_mul]
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have hr : finrank D (LinearMap.range g) ≤ finrank Dᵐᵒᵖ U :=
    le_trans (Submodule.finrank_le _) (by rw [Module.finrank_pi, Fintype.card_fin])
  have hk : finrank D (LinearMap.ker g) ≤ finrank D (annih' U) := Submodule.finrank_mono hker
  omega

theorem annih_annih'_eq [Module.Finite D V] (U : Submodule Dᵐᵒᵖ (Dual D V)) :
    annih (annih' U) = U := by
  haveI : Module.Finite Dᵐᵒᵖ (Dual D V) := Module.Finite.of_basis (dualBasisOp (Module.finBasis D V))
  have h1 := finrank_annih (annih' U)
  have h2 := le_finrank_annih' U
  have hle : finrank Dᵐᵒᵖ (annih (annih' U)) ≤ finrank Dᵐᵒᵖ U := by omega
  exact (Submodule.eq_of_le_of_finrank_le (le_annih_annih' U) hle).symm

/-- The order anti-isomorphism `Submodule D V ≃o (Submodule Dᵐᵒᵖ V*)ᵒᵈ` — the full
projective-geometry duality, finite-dimensional, over a noncommutative division ring,
carrying the handedness in `Dᵐᵒᵖ`. The construction Mathlib makes only over a
commutative field. -/
noncomputable def annihOrderIso [Module.Finite D V] :
    Submodule D V ≃o (Submodule Dᵐᵒᵖ (Dual D V))ᵒᵈ where
  toFun W := OrderDual.toDual (annih W)
  invFun U := annih' (OrderDual.ofDual U)
  left_inv W := annih'_annih_eq W
  right_inv U := congrArg OrderDual.toDual (annih_annih'_eq (OrderDual.ofDual U))
  map_rel_iff' := by
    intro W₁ W₂
    show OrderDual.toDual (annih W₁) ≤ OrderDual.toDual (annih W₂) ↔ W₁ ≤ W₂
    rw [OrderDual.toDual_le_toDual]
    refine ⟨fun h => ?_, fun h => annih_antitone h⟩
    have := annih'_antitone h
    rwa [annih'_annih_eq, annih'_annih_eq] at this

end DimFormula



/-- info: 'Foam.Bridges.annih_galois' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms annih_galois

/-- info: 'Foam.Bridges.le_annih'_annih' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms le_annih'_annih

/-- info: 'Foam.Bridges.le_annih_annih'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms le_annih_annih'

/-- info: 'Foam.Bridges.annih'_annih_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms annih'_annih_le

/-- info: 'Foam.Bridges.annih'_annih_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms annih'_annih_eq

/-- info: 'Foam.Bridges.finrank_dual_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finrank_dual_eq

/-- info: 'Foam.Bridges.finrank_annih' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finrank_annih

/-- info: 'Foam.Bridges.annih_annih'_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms annih_annih'_eq

/-- info: 'Foam.Bridges.annihOrderIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms annihOrderIso

end Foam.Bridges
