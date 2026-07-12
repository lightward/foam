import Counter.Predict
import Foam.Seat.Born
import Foam.Seat.Signature
import Foam.Held
import Foam.Engine.Summary

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

theorem the_born_audit_never_fires (re im : Int) :
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

theorem the_kparseval_audit_rests_at_one (a b c d : Int) :
    (a * c - 1 * (b * d)) * (a * c - 1 * (b * d))
        - 1 * ((a * d - b * c) * (a * d - b * c))
      = (a * a - 1 * (b * b)) * (c * c - 1 * (d * d)) := by
  rw [FInt.one_mul, FInt.one_mul, FInt.one_mul, FInt.one_mul]
  exact int_hyperbolic a b c d

theorem sub_neg_flip (x y : Int) : x - -y = x + y := by
  rw [Int.sub_eq_add_neg, Int.neg_neg]

theorem the_kparseval_audit_rests_at_minus_one (a b c d : Int) :
    (a * c - (-1) * (b * d)) * (a * c - (-1) * (b * d))
        - (-1) * ((a * d - b * c) * (a * d - b * c))
      = (a * a - (-1) * (b * b)) * (c * c - (-1) * (d * d)) := by
  rw [FInt.neg_mul, FInt.neg_mul, FInt.neg_mul, FInt.neg_mul,
    FInt.one_mul, FInt.one_mul, FInt.one_mul, FInt.one_mul,
    sub_neg_flip, sub_neg_flip, sub_neg_flip, sub_neg_flip,
    Int.sub_eq_add_neg, FInt.addComm (a * d) (-(b * c))]
  exact Int.lagrange a b c d

theorem sub_eq_addneg (x y : Int) : x - y = x + -y := Int.sub_eq_add_neg

theorem mul_pull (k x y : Int) : x * (k * y) = k * (x * y) := by
  rw [← FInt.mul_assoc x k y, FInt.mulComm x k, FInt.mul_assoc k x y]

theorem kappa_prod (u v s t : Int) :
    (u - v) * (s - t) = (u * s + v * t) - (u * t + v * s) := by
  rw [sub_eq_addneg u v, sub_eq_addneg s t,
    FInt.mul_add (u + -v) s (-t),
    FInt.add_mul u (-v) s, FInt.add_mul u (-v) (-t),
    FInt.neg_mul v s, FInt.mul_neg u t, Int.neg_mul_neg' v t,
    sub_eq_addneg (u * s + v * t) (u * t + v * s),
    FInt.neg_add (u * t) (v * s),
    Int.add_cross_swap (u * s) (-(v * s)) (-(u * t)) (v * t),
    FInt.addComm (-(v * s)) (-(u * t))]

theorem kmul_sub (k p q : Int) : k * (p - q) = k * p - k * q := by
  rw [sub_eq_addneg p q, FInt.mul_add k p (-q), FInt.mul_neg k q,
    ← sub_eq_addneg (k * p) (k * q)]

theorem sub_sub_shared (P Q S : Int) : (P - S) - (Q - S) = P - Q := by
  rw [sub_eq_addneg P S, sub_eq_addneg Q S,
    sub_eq_addneg (P + -S) (Q + -S),
    FInt.neg_add Q (-S), Int.neg_neg,
    Int.add_swap_inner P (-S) (-Q) S,
    FInt.add_left_neg S, Int.add_zero, ← sub_eq_addneg P Q]

theorem the_kparseval_audit_rests_for_every_kappa (k a b c d : Int) :
    (a * c - k * (b * d)) * (a * c - k * (b * d))
        - k * ((a * d - b * c) * (a * d - b * c))
      = (a * a - k * (b * b)) * (c * c - k * (d * d)) := by
  rw [kappa_prod (a * c) (k * (b * d)) (a * c) (k * (b * d)),
    kappa_prod (a * d) (b * c) (a * d) (b * c),
    kappa_prod (a * a) (k * (b * b)) (c * c) (k * (d * d)),
    kmul_sub k ((a * d) * (a * d) + (b * c) * (b * c))
      ((a * d) * (b * c) + (b * c) * (a * d)),
    FInt.mulComm (k * (b * d)) (a * c),
    FInt.mulComm (b * c) (a * d),
    mul_pull k (a * c) (b * d),
    Int.mul_interchange a b c d,
    FInt.mul_add k ((a * d) * (b * c)) ((a * d) * (b * c)),
    Int.mul_interchange a b d c,
    FInt.mulComm d c,
    sub_sub_shared ((a * c) * (a * c) + (k * (b * d)) * (k * (b * d)))
      (k * ((a * d) * (a * d) + (b * c) * (b * c)))
      (k * ((a * b) * (c * d)) + k * ((a * b) * (c * d))),
    Int.sq_interchange a c,
    Int.mul_interchange k k (b * d) (b * d),
    Int.sq_interchange b d,
    Int.mul_interchange k k (b * b) (d * d),
    FInt.mul_add k ((a * d) * (a * d)) ((b * c) * (b * c)),
    Int.sq_interchange a d, Int.sq_interchange b c,
    mul_pull k (a * a) (d * d),
    FInt.mulComm (k * (b * b)) (c * c),
    mul_pull k (c * c) (b * b),
    FInt.mulComm (c * c) (b * b)]

theorem the_held_audit_rests {S C : Type} [DecidableEq S]
    (refresh : List S → C → C) (step : GInt → GInt)
    (new old : List S) (s : S) (ps : List S) (st : List S × C) :
    transcriptWith (LedgerStage S C) (fun st => (st.1, refresh st.1 st.2)) st ps
        = transcript (LedgerStage S C) st ps
      ∧ evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s) :=
  ⟨sweep_unobservable refresh ps st, summary_resumes step new old s⟩

/-- info: 'Foam.Counter.the_held_audit_rests' does not depend on any axioms -/
#guard_msgs in #print axioms the_held_audit_rests

/-- info: 'Foam.Counter.mul_pull' does not depend on any axioms -/
#guard_msgs in #print axioms mul_pull

/-- info: 'Foam.Counter.kappa_prod' does not depend on any axioms -/
#guard_msgs in #print axioms kappa_prod

/-- info: 'Foam.Counter.kmul_sub' does not depend on any axioms -/
#guard_msgs in #print axioms kmul_sub

/-- info: 'Foam.Counter.sub_sub_shared' does not depend on any axioms -/
#guard_msgs in #print axioms sub_sub_shared

/-- info: 'Foam.Counter.the_kparseval_audit_rests_for_every_kappa' does not depend on any axioms -/
#guard_msgs in #print axioms the_kparseval_audit_rests_for_every_kappa

/-- info: 'Foam.Counter.sub_neg_flip' does not depend on any axioms -/
#guard_msgs in #print axioms sub_neg_flip

/-- info: 'Foam.Counter.the_kparseval_audit_rests_at_minus_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_kparseval_audit_rests_at_minus_one

/-- info: 'Foam.Counter.the_kparseval_audit_rests_at_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_kparseval_audit_rests_at_one

/-- info: 'Foam.Counter.the_born_audit_never_fires' does not depend on any axioms -/
#guard_msgs in #print axioms the_born_audit_never_fires

end Foam.Counter
