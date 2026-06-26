import Foam.Seat.Hurwitz

namespace Foam

def imagDim : Nat → Nat := fun n => 2 ^ (n + 1) - 1

theorem imagDim_complex : imagDim 0 = 1 := rfl

theorem imagDim_quaternion : imagDim 1 = 3 := rfl

theorem imagDim_octonion : imagDim 2 = 7 := rfl

theorem imagDim_sedenion : imagDim 3 = 15 := rfl

theorem rank0_composes (z w : GInt) : (z.mul w).normSq = z.normSq * w.normSq :=
  GInt.normSq_mul z w

theorem rank1_noncommutes : Quat.mul eye jay ≠ Quat.mul jay eye :=
  order_arrives

theorem rank2_nonassociates :
    Octo.mul (Octo.mul eyeO jayO) ell ≠ Octo.mul eyeO (Octo.mul jayO ell) :=
  non_assoc

theorem rank3_no_division :
    Sed.mul sedA sedB = Sed.zero ∧ sedA ≠ Sed.zero ∧ sedB ≠ Sed.zero :=
  division_dies

theorem rank_ladder :
    (∀ z w : GInt, (z.mul w).normSq = z.normSq * w.normSq)
      ∧ (Quat.mul eye jay ≠ Quat.mul jay eye)
      ∧ (Octo.mul (Octo.mul eyeO jayO) ell ≠ Octo.mul eyeO (Octo.mul jayO ell))
      ∧ (Sed.mul sedA sedB = Sed.zero ∧ sedA ≠ Sed.zero ∧ sedB ≠ Sed.zero) :=
  ⟨GInt.normSq_mul, order_arrives, non_assoc, division_dies⟩

/-- info: 'Foam.imagDim_sedenion' does not depend on any axioms -/
#guard_msgs in #print axioms imagDim_sedenion

/-- info: 'Foam.rank0_composes' does not depend on any axioms -/
#guard_msgs in #print axioms rank0_composes

/-- info: 'Foam.rank1_noncommutes' does not depend on any axioms -/
#guard_msgs in #print axioms rank1_noncommutes

/-- info: 'Foam.rank2_nonassociates' does not depend on any axioms -/
#guard_msgs in #print axioms rank2_nonassociates

/-- info: 'Foam.rank3_no_division' does not depend on any axioms -/
#guard_msgs in #print axioms rank3_no_division

/-- info: 'Foam.rank_ladder' does not depend on any axioms -/
#guard_msgs in #print axioms rank_ladder

end Foam
