import Counter.Predict
import Foam.Seat.Born

namespace Foam.Counter

def sqlAlign : Nat → Int → Int → Int
  | 0, re, _ => re
  | 1, _, im => im
  | 2, re, _ => -re
  | _, _, im => -im

def sqlBorn (tk : Nat) (re im : Int) : Int :=
  sqlAlign tk re im * sqlAlign tk re im

theorem the_rotation_clauses_are_recognition (re im : Int) :
    sqlAlign 0 re im = re
      ∧ sqlAlign 1 re im = sqlAlign 0 im (-re)
      ∧ sqlAlign 2 re im = sqlAlign 1 im (-re)
      ∧ sqlAlign 3 re im = sqlAlign 2 im (-re) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem the_four_phases_conserve (re im : Int) :
    sqlBorn 0 re im + sqlBorn 1 re im + sqlBorn 2 re im + sqlBorn 3 re im
      = 2 * (re * re + im * im) := by
  show re * re + im * im + (-re) * (-re) + (-im) * (-im)
    = 2 * (re * re + im * im)
  rw [Int.neg_mul_neg' re re, Int.neg_mul_neg' im im, Int.two_mul',
    FInt.add_assoc (re * re + im * im) (re * re) (im * im)]

theorem the_weights_never_dip (tk : Nat) (re im : Int) :
    ∃ k : Nat, sqlBorn tk re im = Int.ofNat k :=
  GInt.sq_image (sqlAlign tk re im)

theorem the_audit_never_fires (re im : Int) :
    (sqlAlign 0 re im = re
        ∧ sqlAlign 1 re im = sqlAlign 0 im (-re)
        ∧ sqlAlign 2 re im = sqlAlign 1 im (-re)
        ∧ sqlAlign 3 re im = sqlAlign 2 im (-re))
      ∧ sqlBorn 0 re im + sqlBorn 1 re im + sqlBorn 2 re im + sqlBorn 3 re im
          = 2 * (re * re + im * im)
      ∧ ∀ tk, ∃ k : Nat, sqlBorn tk re im = Int.ofNat k :=
  ⟨the_rotation_clauses_are_recognition re im,
   the_four_phases_conserve re im,
   fun tk => the_weights_never_dip tk re im⟩

/-- info: 'Foam.Counter.the_rotation_clauses_are_recognition' does not depend on any axioms -/
#guard_msgs in #print axioms the_rotation_clauses_are_recognition

/-- info: 'Foam.Counter.the_four_phases_conserve' does not depend on any axioms -/
#guard_msgs in #print axioms the_four_phases_conserve

/-- info: 'Foam.Counter.the_weights_never_dip' does not depend on any axioms -/
#guard_msgs in #print axioms the_weights_never_dip

/-- info: 'Foam.Counter.the_audit_never_fires' does not depend on any axioms -/
#guard_msgs in #print axioms the_audit_never_fires

end Foam.Counter
