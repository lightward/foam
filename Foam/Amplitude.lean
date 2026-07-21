import Foam

namespace Foam

structure GInt where
  re : Int
  im : Int

def GInt.neg (z : GInt) : GInt := ⟨-z.re, -z.im⟩

def GInt.conj (z : GInt) : GInt := ⟨z.re, -z.im⟩

def GInt.rot (z : GInt) : GInt := ⟨-z.im, z.re⟩

def GInt.normSq (z : GInt) : Int := z.re * z.re + z.im * z.im

def GInt.i : GInt := ⟨0, 1⟩

theorem int_neg_neg : ∀ a : Int, -(-a) = a
  | .ofNat 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc _ => rfl

theorem neg_mul_neg_self : ∀ a : Int, (-a) * (-a) = a * a
  | .ofNat 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc _ => rfl

theorem int_add_comm : ∀ a b : Int, a + b = b + a
  | .ofNat m, .ofNat n => congrArg Int.ofNat (Nat.add_comm m n)
  | .ofNat _, .negSucc _ => rfl
  | .negSucc _, .ofNat _ => rfl
  | .negSucc m, .negSucc n =>
      congrArg Int.negSucc (congrArg Nat.succ (Nat.add_comm m n))

theorem conj_is_an_involution (z : GInt) : z.conj.conj = z := by
  show (⟨z.re, -(-z.im)⟩ : GInt) = z
  rw [int_neg_neg]

theorem the_wheel_comes_home (z : GInt) :
    z.rot.rot.rot.rot = z := by
  show (⟨-(-z.re), -(-z.im)⟩ : GInt) = z
  rw [int_neg_neg, int_neg_neg]

theorem rot_conserves_the_norm (z : GInt) :
    z.rot.normSq = z.normSq := by
  show (-z.im) * (-z.im) + z.re * z.re = z.re * z.re + z.im * z.im
  rw [neg_mul_neg_self]
  exact int_add_comm _ _

theorem conj_conserves_the_norm (z : GInt) :
    z.conj.normSq = z.normSq := by
  show z.re * z.re + (-z.im) * (-z.im) = z.re * z.re + z.im * z.im
  rw [neg_mul_neg_self]

theorem the_two_kinds_anticommute (z : GInt) :
    z.conj.rot = (z.rot.conj).neg := by
  show (⟨-(-z.im), z.re⟩ : GInt) = ⟨-(-z.im), -(-z.re)⟩
  rw [int_neg_neg z.re]

theorem the_kinds_are_two : GInt.i.rot ≠ GInt.i.conj :=
  fun h => nomatch (GInt.mk.inj h).1

theorem wigner_two_kinds (z : GInt) :
    z.rot.normSq = z.normSq
      ∧ z.conj.normSq = z.normSq
      ∧ z.conj.rot = (z.rot.conj).neg
      ∧ GInt.i.rot ≠ GInt.i.conj :=
  ⟨rot_conserves_the_norm z, conj_conserves_the_norm z,
   the_two_kinds_anticommute z, the_kinds_are_two⟩

/-- info: 'Foam.int_neg_neg' does not depend on any axioms -/
#guard_msgs in #print axioms int_neg_neg

/-- info: 'Foam.neg_mul_neg_self' does not depend on any axioms -/
#guard_msgs in #print axioms neg_mul_neg_self

/-- info: 'Foam.int_add_comm' does not depend on any axioms -/
#guard_msgs in #print axioms int_add_comm

/-- info: 'Foam.conj_is_an_involution' does not depend on any axioms -/
#guard_msgs in #print axioms conj_is_an_involution

/-- info: 'Foam.the_wheel_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_comes_home

/-- info: 'Foam.rot_conserves_the_norm' does not depend on any axioms -/
#guard_msgs in #print axioms rot_conserves_the_norm

/-- info: 'Foam.conj_conserves_the_norm' does not depend on any axioms -/
#guard_msgs in #print axioms conj_conserves_the_norm

/-- info: 'Foam.the_two_kinds_anticommute' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_kinds_anticommute

/-- info: 'Foam.the_kinds_are_two' does not depend on any axioms -/
#guard_msgs in #print axioms the_kinds_are_two

/-- info: 'Foam.wigner_two_kinds' does not depend on any axioms -/
#guard_msgs in #print axioms wigner_two_kinds

end Foam
