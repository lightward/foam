import Foam.Cleared
import Foam.Seat.Rotations

namespace Foam.Bridges

theorem odd_ne_even : ∀ k m : Nat, 2 * k + 1 ≠ 2 * m
  | _, 0, h => Nat.noConfusion h
  | 0, _ + 1, h => Nat.noConfusion (Nat.succ.inj h)
  | k + 1, m + 1, h => odd_ne_even k m (Nat.succ.inj (Nat.succ.inj h))

theorem odd_times_three : ∀ k : Nat, (2 * k + 1) * 3 = 2 * (3 * k + 1) + 1
  | 0 => rfl
  | k + 1 => by
    show Nat.succ (Nat.succ (2 * k + 1)) * 3 = 2 * ((3 * k + 1) + 3) + 1
    rw [Nat.succ_mul, Nat.succ_mul, odd_times_three k, Nat.left_distrib,
      Nat.left_distrib, Nat.left_distrib]

theorem three_pow_odd : ∀ a : Nat, ∃ k, 3 ^ a = 2 * k + 1
  | 0 => ⟨0, rfl⟩
  | a + 1 => by
    obtain ⟨k, hk⟩ := three_pow_odd a
    refine ⟨3 * k + 1, ?_⟩
    show 3 ^ a * 3 = 2 * (3 * k + 1) + 1
    rw [hk]
    exact odd_times_three k

theorem comma_never_clears : ∀ (a b : Nat), 1 ≤ a → 3 ^ a ≠ 2 ^ b
  | a, 0, ha, h => by
    cases a with
    | zero => exact absurd ha (by decide)
    | succ k => exact absurd ((nat_mul_eq_one (3 ^ k) 3 h).2) (by decide)
  | a, b + 1, _, h => by
    obtain ⟨k, hk⟩ := three_pow_odd a
    rw [h] at hk
    have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by
      show 2 ^ b * 2 = 2 * 2 ^ b
      exact Nat.mul_comm (2 ^ b) 2
    rw [h2] at hk
    exact odd_ne_even k (2 ^ b) hk.symm

theorem pythagoras :
    (∀ a b : Nat, 1 ≤ a → 3 ^ a ≠ 2 ^ b) ∧ ∀ n, ¬ Closes gold (n + 1) :=
  ⟨comma_never_clears, gold_never_closes⟩

/-- info: 'Foam.Bridges.odd_ne_even' does not depend on any axioms -/
#guard_msgs in #print axioms odd_ne_even

/-- info: 'Foam.Bridges.three_pow_odd' does not depend on any axioms -/
#guard_msgs in #print axioms three_pow_odd

/-- info: 'Foam.Bridges.comma_never_clears' does not depend on any axioms -/
#guard_msgs in #print axioms comma_never_clears

/-- info: 'Foam.Bridges.pythagoras' does not depend on any axioms -/
#guard_msgs in #print axioms pythagoras

end Foam.Bridges
