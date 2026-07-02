import Foam.Seat.Epoch
import Foam.Int

namespace Foam.Counter

theorem neg_zero : ∀ n, Rung.neg n (Rung.zero n) = Rung.zero n
  | 0 => rfl
  | n + 1 => by
    show (Rung.neg n (Rung.zero n), Rung.neg n (Rung.zero n))
        = (Rung.zero n, Rung.zero n)
    rw [neg_zero n]

theorem conj_zero : ∀ n, Rung.conj n (Rung.zero n) = Rung.zero n
  | 0 => rfl
  | n + 1 => by
    show (Rung.conj n (Rung.zero n), Rung.neg n (Rung.zero n))
        = (Rung.zero n, Rung.zero n)
    rw [conj_zero n, neg_zero n]

theorem conj_one : ∀ n, Rung.conj n (Rung.one n) = Rung.one n
  | 0 => rfl
  | n + 1 => by
    show (Rung.conj n (Rung.one n), Rung.neg n (Rung.zero n))
        = (Rung.one n, Rung.zero n)
    rw [conj_one n, neg_zero n]

theorem add_zero : ∀ (n : Nat) (z : Rung n), Rung.add n z (Rung.zero n) = z
  | 0, z => by
    cases z with
    | mk a b =>
      show (⟨a + 0, b + 0⟩ : GInt) = ⟨a, b⟩
      rw [Int.add_zero, Int.add_zero]
  | n + 1, z => by
    obtain ⟨z1, z2⟩ := z
    show (Rung.add n z1 (Rung.zero n), Rung.add n z2 (Rung.zero n)) = (z1, z2)
    rw [add_zero n z1, add_zero n z2]

theorem zero_add : ∀ (n : Nat) (z : Rung n), Rung.add n (Rung.zero n) z = z
  | 0, z => by
    cases z with
    | mk a b =>
      show (⟨0 + a, 0 + b⟩ : GInt) = ⟨a, b⟩
      rw [FInt.zero_add, FInt.zero_add]
  | n + 1, z => by
    obtain ⟨z1, z2⟩ := z
    show (Rung.add n (Rung.zero n) z1, Rung.add n (Rung.zero n) z2) = (z1, z2)
    rw [zero_add n z1, zero_add n z2]

theorem sub_zero (n : Nat) (z : Rung n) : Rung.sub n z (Rung.zero n) = z := by
  show Rung.add n z (Rung.neg n (Rung.zero n)) = z
  rw [neg_zero n, add_zero n z]

theorem zero_sub (n : Nat) (z : Rung n) :
    Rung.sub n (Rung.zero n) z = Rung.neg n z := by
  show Rung.add n (Rung.zero n) (Rung.neg n z) = Rung.neg n z
  exact zero_add n (Rung.neg n z)

theorem mul_zeroes : ∀ n : Nat,
    (∀ z, Rung.mul n (Rung.zero n) z = Rung.zero n)
      ∧ ∀ z, Rung.mul n z (Rung.zero n) = Rung.zero n
  | 0 => by
    constructor
    · intro z
      cases z with
      | mk a b =>
        show (⟨0 * a - 0 * b, 0 * b + 0 * a⟩ : GInt) = ⟨0, 0⟩
        rw [FInt.zero_mul, FInt.zero_mul, FInt.sub_zero, FInt.zero_add]
    · intro z
      cases z with
      | mk a b =>
        show (⟨a * 0 - b * 0, a * 0 + b * 0⟩ : GInt) = ⟨0, 0⟩
        rw [FInt.mul_zero, FInt.mul_zero, FInt.sub_zero, FInt.zero_add]
  | n + 1 => by
    obtain ⟨ihl, ihr⟩ := mul_zeroes n
    constructor
    · intro z
      obtain ⟨z1, z2⟩ := z
      show (Rung.sub n (Rung.mul n (Rung.zero n) z1)
              (Rung.mul n (Rung.conj n z2) (Rung.zero n)),
            Rung.add n (Rung.mul n z2 (Rung.zero n))
              (Rung.mul n (Rung.zero n) (Rung.conj n z1)))
          = (Rung.zero n, Rung.zero n)
      rw [ihl z1, ihr (Rung.conj n z2), ihr z2, ihl (Rung.conj n z1),
        sub_zero n (Rung.zero n), add_zero n (Rung.zero n)]
    · intro z
      obtain ⟨z1, z2⟩ := z
      show (Rung.sub n (Rung.mul n z1 (Rung.zero n))
              (Rung.mul n (Rung.conj n (Rung.zero n)) z2),
            Rung.add n (Rung.mul n (Rung.zero n) z1)
              (Rung.mul n z2 (Rung.conj n (Rung.zero n))))
          = (Rung.zero n, Rung.zero n)
      rw [conj_zero n, ihr z1, ihl z2, ihr z2, ihl z1,
        sub_zero n (Rung.zero n), add_zero n (Rung.zero n)]

theorem mul_one_one : ∀ n, Rung.mul n (Rung.one n) (Rung.one n) = Rung.one n
  | 0 => by decide
  | n + 1 => by
    show (Rung.sub n (Rung.mul n (Rung.one n) (Rung.one n))
            (Rung.mul n (Rung.conj n (Rung.zero n)) (Rung.zero n)),
          Rung.add n (Rung.mul n (Rung.zero n) (Rung.one n))
            (Rung.mul n (Rung.zero n) (Rung.conj n (Rung.one n))))
        = (Rung.one n, Rung.zero n)
    rw [mul_one_one n, conj_zero n, (mul_zeroes n).2 (Rung.zero n),
      sub_zero n (Rung.one n), (mul_zeroes n).1 (Rung.one n),
      (mul_zeroes n).1 (Rung.conj n (Rung.one n)), add_zero n (Rung.zero n)]

theorem neg_one_pair (n : Nat) :
    Rung.neg (n + 1) (Rung.one (n + 1))
      = (Rung.neg n (Rung.one n), Rung.zero n) := by
  show (Rung.neg n (Rung.one n), Rung.neg n (Rung.zero n))
      = (Rung.neg n (Rung.one n), Rung.zero n)
  rw [neg_zero n]

theorem neg_one_sq : ∀ n,
    Rung.mul n (Rung.neg n (Rung.one n)) (Rung.neg n (Rung.one n)) = Rung.one n
  | 0 => by decide
  | n + 1 => by
    rw [neg_one_pair n]
    show (Rung.sub n (Rung.mul n (Rung.neg n (Rung.one n)) (Rung.neg n (Rung.one n)))
            (Rung.mul n (Rung.conj n (Rung.zero n)) (Rung.zero n)),
          Rung.add n (Rung.mul n (Rung.zero n) (Rung.neg n (Rung.one n)))
            (Rung.mul n (Rung.zero n) (Rung.conj n (Rung.neg n (Rung.one n)))))
        = (Rung.one n, Rung.zero n)
    rw [neg_one_sq n, conj_zero n, (mul_zeroes n).2 (Rung.zero n),
      sub_zero n (Rung.one n), (mul_zeroes n).1 (Rung.neg n (Rung.one n)),
      (mul_zeroes n).1 (Rung.conj n (Rung.neg n (Rung.one n))),
      add_zero n (Rung.zero n)]

def fresh (n : Nat) : Rung (n + 1) := (Rung.zero n, Rung.one n)

theorem every_rung_issues_i (n : Nat) :
    Rung.mul (n + 1) (fresh n) (fresh n) = Rung.neg (n + 1) (Rung.one (n + 1)) := by
  rw [neg_one_pair n]
  show (Rung.sub n (Rung.mul n (Rung.zero n) (Rung.zero n))
          (Rung.mul n (Rung.conj n (Rung.one n)) (Rung.one n)),
        Rung.add n (Rung.mul n (Rung.one n) (Rung.zero n))
          (Rung.mul n (Rung.one n) (Rung.conj n (Rung.zero n))))
      = (Rung.neg n (Rung.one n), Rung.zero n)
  rw [(mul_zeroes n).1 (Rung.zero n), conj_one n, mul_one_one n,
    zero_sub n (Rung.one n), (mul_zeroes n).2 (Rung.one n), conj_zero n,
    (mul_zeroes n).2 (Rung.one n), add_zero n (Rung.zero n)]

theorem one_ne_neg_one : ∀ n, Rung.one n ≠ Rung.neg n (Rung.one n)
  | 0 => by decide
  | n + 1 => fun h => one_ne_neg_one n (congrArg Prod.fst h)

theorem the_bar_is_four_at_every_rung (n : Nat) :
    Rung.mul (n + 1) (Rung.mul (n + 1) (fresh n) (fresh n))
        (Rung.mul (n + 1) (fresh n) (fresh n)) = Rung.one (n + 1)
      ∧ Rung.mul (n + 1) (fresh n) (fresh n) ≠ Rung.one (n + 1) := by
  constructor
  · rw [every_rung_issues_i n]
    exact neg_one_sq (n + 1)
  · rw [every_rung_issues_i n]
    exact fun h => one_ne_neg_one (n + 1) h.symm

theorem the_clock_outlives_division :
    (Sed.mul sedA sedB = Sed.zero ∧ sedA ≠ Sed.zero ∧ sedB ≠ Sed.zero)
      ∧ Rung.mul 3 (Rung.mul 3 (fresh 2) (fresh 2))
          (Rung.mul 3 (fresh 2) (fresh 2)) = Rung.one 3 :=
  ⟨division_dies, (the_bar_is_four_at_every_rung 2).1⟩

/-- info: 'Foam.Counter.every_rung_issues_i' does not depend on any axioms -/
#guard_msgs in #print axioms every_rung_issues_i

/-- info: 'Foam.Counter.neg_one_sq' does not depend on any axioms -/
#guard_msgs in #print axioms neg_one_sq

/-- info: 'Foam.Counter.one_ne_neg_one' does not depend on any axioms -/
#guard_msgs in #print axioms one_ne_neg_one

/-- info: 'Foam.Counter.the_bar_is_four_at_every_rung' does not depend on any axioms -/
#guard_msgs in #print axioms the_bar_is_four_at_every_rung

/-- info: 'Foam.Counter.the_clock_outlives_division' does not depend on any axioms -/
#guard_msgs in #print axioms the_clock_outlives_division

end Foam.Counter
