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

end Foam.Bridges
