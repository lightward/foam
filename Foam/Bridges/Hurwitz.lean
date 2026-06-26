import Foam.Seat.Norm
import Foam.Seat.Sed

namespace Foam.Bridges

theorem hurwitz_composition (z w : GInt) : (z.mul w).normSq = z.normSq * w.normSq :=
  GInt.normSq_mul z w

theorem frobenius_assoc_dies :
    Octo.mul (Octo.mul eyeO jayO) ell ≠ Octo.mul eyeO (Octo.mul jayO ell) :=
  non_assoc

theorem hurwitz_division_dies :
    Sed.mul sedA sedB = Sed.zero ∧ sedA ≠ Sed.zero ∧ sedB ≠ Sed.zero :=
  division_dies

theorem hurwitz_staircase :
    (∀ z w : GInt, (z.mul w).normSq = z.normSq * w.normSq)
      ∧ (Octo.mul (Octo.mul eyeO jayO) ell ≠ Octo.mul eyeO (Octo.mul jayO ell))
      ∧ (Sed.mul sedA sedB = Sed.zero ∧ sedA ≠ Sed.zero ∧ sedB ≠ Sed.zero) :=
  ⟨GInt.normSq_mul, non_assoc, division_dies⟩

/-- info: 'Foam.Bridges.hurwitz_composition' does not depend on any axioms -/
#guard_msgs in #print axioms hurwitz_composition

/-- info: 'Foam.Bridges.frobenius_assoc_dies' does not depend on any axioms -/
#guard_msgs in #print axioms frobenius_assoc_dies

/-- info: 'Foam.Bridges.hurwitz_division_dies' does not depend on any axioms -/
#guard_msgs in #print axioms hurwitz_division_dies

/-- info: 'Foam.Bridges.hurwitz_staircase' does not depend on any axioms -/
#guard_msgs in #print axioms hurwitz_staircase

end Foam.Bridges
