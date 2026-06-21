import Foam.Seat.Signature
import Foam.Seat.Clock
import Foam.Seat.Closure

namespace Foam

theorem ellipticRot_closes : Closes GInt.rot 4 := spec_closes_four

theorem ellipticRot_turns : (Rot.r1 * Rot.r1 : Rot) ≠ 1 := Rot.clock_turns

theorem parabolicBoost_add (v1 v2 : Int) (z : DInt) :
    galileanBoost v2 (galileanBoost v1 z) = galileanBoost (v2 + v1) z :=
  galilean_velocities_add v1 v2 z

theorem parabolicBoost_never_closes (v : Int) (hv : v ≠ 0) :
    galileanBoost v ⟨1, 0⟩ ≠ (⟨1, 0⟩ : DInt) := by
  intro h
  have hx : v * 1 + 0 = 0 := congrArg DInt.x h
  rw [Int.mul_one, Int.add_zero] at hx
  exact hv hx

theorem int_add_left_cancel (a x y : Int) (h : a + x = a + y) : x = y := by
  have h2 : -a + (a + x) = -a + (a + y) := congrArg (-a + ·) h
  rw [← Int.add_assoc, ← Int.add_assoc, Int.add_left_neg, Int.zero_add, Int.zero_add] at h2
  exact h2

theorem nat_mul_eq_one : ∀ (m n : Nat), m * n = 1 → m = 1 ∧ n = 1
  | 0, n, h => by rw [Nat.zero_mul] at h; exact Nat.noConfusion h
  | _ + 1, 0, h => by rw [Nat.mul_zero] at h; exact Nat.noConfusion h
  | j + 1, k + 1, h => by
    rw [Nat.mul_succ] at h
    have hle : j + 1 ≤ 1 := by
      have hx := Nat.le_add_left (j + 1) ((j + 1) * k)
      rw [h] at hx; exact hx
    have hj : j = 0 := Nat.succ.inj (Nat.le_antisymm hle (Nat.succ_le_succ (Nat.zero_le j)))
    subst hj
    rw [Nat.one_mul] at h
    exact ⟨rfl, congrArg Nat.succ (Nat.succ.inj h)⟩

theorem int_mul_eq_one : ∀ (x y : Int), x * y = 1 → (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1)
  | Int.ofNat m, Int.ofNat n, h => by
    have h2 : Int.ofNat (m * n) = Int.ofNat 1 := h
    obtain ⟨hm, hn⟩ := nat_mul_eq_one m n (Int.ofNat.inj h2)
    subst hm; subst hn; exact Or.inl ⟨rfl, rfl⟩
  | Int.ofNat m, Int.negSucc n, h => by
    exfalso
    have h' : Int.negOfNat (m * (n + 1)) = 1 := h
    cases hk : m * (n + 1) with
    | zero => rw [hk] at h'; exact absurd h' (by decide)
    | succ s => rw [hk] at h'; exact Int.noConfusion h'
  | Int.negSucc m, Int.ofNat n, h => by
    exfalso
    have h' : Int.negOfNat ((m + 1) * n) = 1 := h
    cases hk : (m + 1) * n with
    | zero => rw [hk] at h'; exact absurd h' (by decide)
    | succ s => rw [hk] at h'; exact Int.noConfusion h'
  | Int.negSucc m, Int.negSucc n, h => by
    have h2 : Int.ofNat ((m + 1) * (n + 1)) = Int.ofNat 1 := h
    obtain ⟨hm, hn⟩ := nat_mul_eq_one (m + 1) (n + 1) (Int.ofNat.inj h2)
    have hm0 : m = 0 := Nat.succ.inj hm
    have hn0 : n = 0 := Nat.succ.inj hn
    subst hm0; subst hn0; exact Or.inr ⟨rfl, rfl⟩

theorem int_pell_one (a b : Int) (h : a * a - b * b = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) := by
  rw [int_sq_diff a b] at h
  have key : (a - b) = (a + b) → b = 0 := by
    intro heq
    rw [Int.sub_eq_add_neg] at heq
    have hnb : -b = b := int_add_left_cancel a (-b) b heq
    have hbb : b + b = 0 := by
      have hh := Int.add_right_neg b
      rw [hnb] at hh
      exact hh
    have hcancel : (b + b) = 0 → b = 0 := by
      intro hbb0
      have h2 : b + b = 2 * b := by rw [Int.two_mul]
      rw [h2] at hbb0
      rcases Int.mul_eq_zero.mp hbb0 with h20 | hb
      · exact absurd h20 (by decide)
      · exact hb
    exact hcancel hbb
  cases int_mul_eq_one (a - b) (a + b) h with
  | inl hpq =>
    obtain ⟨hp, hq⟩ := hpq
    have hb0 : b = 0 := key (hp.trans hq.symm)
    rw [hb0, Int.sub_zero] at hp
    exact Or.inl ⟨hp, hb0⟩
  | inr hpq =>
    obtain ⟨hp, hq⟩ := hpq
    have hb0 : b = 0 := key (hp.trans hq.symm)
    rw [hb0, Int.sub_zero] at hp
    exact Or.inr ⟨hp, hb0⟩

theorem hyperbolicRot_trivial (a b : Int) (h : SInt.hnorm ⟨a, b⟩ = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) :=
  int_pell_one a b h

/-- info: 'Foam.ellipticRot_closes' does not depend on any axioms -/
#guard_msgs in #print axioms ellipticRot_closes

/-- info: 'Foam.ellipticRot_turns' does not depend on any axioms -/
#guard_msgs in #print axioms ellipticRot_turns

/-- info: 'Foam.parabolicBoost_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms parabolicBoost_add

/-- info: 'Foam.parabolicBoost_never_closes' depends on axioms: [propext] -/
#guard_msgs in #print axioms parabolicBoost_never_closes

/-- info: 'Foam.int_add_left_cancel' depends on axioms: [propext] -/
#guard_msgs in #print axioms int_add_left_cancel

/-- info: 'Foam.nat_mul_eq_one' does not depend on any axioms -/
#guard_msgs in #print axioms nat_mul_eq_one

/-- info: 'Foam.int_mul_eq_one' does not depend on any axioms -/
#guard_msgs in #print axioms int_mul_eq_one

/-- info: 'Foam.int_pell_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms int_pell_one

/-- info: 'Foam.hyperbolicRot_trivial' depends on axioms: [propext] -/
#guard_msgs in #print axioms hyperbolicRot_trivial

end Foam