import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Field.Opposite
import Foam.Cleared

namespace Foam.Bridges

example (D : Type) [DivisionRing D] : DivisionRing Dᵐᵒᵖ := inferInstance

def handedness_comes_home (D : Type) [DivisionRing D] : Dᵐᵒᵖᵐᵒᵖ ≃+* D :=
  (RingEquiv.opOp D).symm

theorem handedness_is_neg_not_gold (D : Type) [DivisionRing D] :
    Nonempty (Dᵐᵒᵖᵐᵒᵖ ≃+* D)
      ∧ Function.Involutive GInt.neg
      ∧ Closes GInt.neg 2
      ∧ (∀ n, ¬ Closes gold (n + 1)) :=
  ⟨⟨handedness_comes_home D⟩, GInt.neg_neg, alt_closes_two, gold_never_closes⟩

/-- info: 'Foam.Bridges.handedness_comes_home' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms handedness_comes_home

/-- info: 'Foam.Bridges.handedness_is_neg_not_gold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms handedness_is_neg_not_gold

end Foam.Bridges
