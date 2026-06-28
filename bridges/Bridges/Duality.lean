import Mathlib.LinearAlgebra.Dual.Lemmas
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

end Foam.Bridges
