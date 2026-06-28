import Mathlib.LinearAlgebra.Dual.Defs
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

/-- info: 'Foam.Bridges.annih_galois' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms annih_galois

/-- info: 'Foam.Bridges.le_annih'_annih' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms le_annih'_annih

/-- info: 'Foam.Bridges.le_annih_annih'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms le_annih_annih'

end Foam.Bridges
