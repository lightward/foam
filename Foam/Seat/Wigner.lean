import Foam.Seat.Norm
import Foam.Seat.Characters
import Foam.Seat.Schrodinger

namespace Foam

theorem wigner_unitary (z : GInt) : (GInt.rot z).normSq = z.normSq :=
  evolve_unitary z

theorem wigner_antiunitary (z : GInt) : z.conj.normSq = z.normSq :=
  GInt.normSq_conj z

theorem wigner_two_kinds : Char.chi ≠ Char.chiBar :=
  Char.chi_distinct_chiBar

theorem wigner_classification (a b : Rot) :
    Char.chi (a * b) = GInt.mul (Char.chi a) (Char.chi b) :=
  Char.chi_hom a b

theorem wigner (z : GInt) :
    ((GInt.rot z).normSq = z.normSq)
      ∧ (z.conj.normSq = z.normSq)
      ∧ (Char.chi ≠ Char.chiBar)
      ∧ (∀ a b, Char.chi (a * b) = GInt.mul (Char.chi a) (Char.chi b)) :=
  ⟨evolve_unitary z, GInt.normSq_conj z, Char.chi_distinct_chiBar, Char.chi_hom⟩

/-- info: 'Foam.wigner_unitary' does not depend on any axioms -/
#guard_msgs in #print axioms wigner_unitary

/-- info: 'Foam.wigner_antiunitary' does not depend on any axioms -/
#guard_msgs in #print axioms wigner_antiunitary

/-- info: 'Foam.wigner_two_kinds' does not depend on any axioms -/
#guard_msgs in #print axioms wigner_two_kinds

/-- info: 'Foam.wigner_classification' does not depend on any axioms -/
#guard_msgs in #print axioms wigner_classification

/-- info: 'Foam.wigner' does not depend on any axioms -/
#guard_msgs in #print axioms wigner

end Foam
