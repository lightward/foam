/-
# Foam.Rotations — the three rotation groups (why Lorentz needs the continuum)

The signature trichotomy (`Foam/Frames.lean`) has a companion at the group level: each frame's
INTEGER rotation group, and they are strikingly different — which closes the boost story by
explaining, structurally, why finite foam is Galilean.

    frame        unit²   integer rotation group        closes?    corpus
    elliptic     −1      ℤ/4   (the dial)               yes (4)    rot_complete (Spectrum)
    parabolic     0      ℤ     (velocities add)         never      galilean_velocities_add (Galilean)
    hyperbolic   +1      trivial (±id only)             —          int_pell_one (here)

The elliptic dial CLOSES in four (`rot_complete`: rot⁴ = id) — a finite cyclic group, the
periodic stations. The parabolic boost NEVER closes — `galilean_velocities_add` makes its group
the additive line ℤ (iterate the unit-velocity boost forever, never return). And the hyperbolic
boost has NO proper integer element at all: this file proves the integer unit hyperbola is
trivial (`int_pell_one`: `a²−b²=1 → (a,b) = (±1,0)`), so the only `hnorm`-preserving integer
boost `B(a,b)·z = ⟨a·t+b·x, b·t+a·x⟩` (which preserves `hnorm` iff `a²−b²=1`, standard) is `±id`.

That is the group-level form of `Boost.finite_boost_galilean`: there is no proper boost to FIND
at integer scale, so the Lorentz group is empty between the reflections — Lorentz is a continuum
emergent, not a finite object. The continuum is exactly where `a²−b²=1` acquires nontrivial
(real, irrational-rapidity) solutions.

Axiom-free, pinned. The arithmetic floor (a hand-rolled `Int`/`Nat` unit lemma) is built here,
in the corpus's `IntFloor` discipline — core's divisibility/unit lemmas route through `omega`/
`simp` and carry `Quot.sound`/`propext`; these ask no one.
-/

import Foam.Boost
import Foam.Frame

namespace Foam

/-- Left cancellation on `Int`: `a + x = a + y → x = y`. Axiom-free (add `−a` and collapse). -/
theorem int_add_left_cancel (a x y : Int) (h : a + x = a + y) : x = y := by
  have h2 : (-a + a) + x = (-a + a) + y := by
    rw [int_add_assoc, int_add_assoc]; exact congrArg (-a + ·) h
  rw [int_neg_add_self, int_zero_add, int_zero_add] at h2
  exact h2

/-- `m · n = 1 → m = 1 ∧ n = 1` on `Nat`. By cases on both, with the `succ·succ` case pinched:
    the second summand of `(j+1)·(k+1) = (j+1)·k + (j+1)` is `≥ 1` and `≤ 1`, so `j = 0`. -/
theorem nat_mul_eq_one : ∀ (m n : Nat), m * n = 1 → m = 1 ∧ n = 1
  | 0, n, h => by rw [nat_zero_mul] at h; exact Nat.noConfusion h
  | _ + 1, 0, h => by rw [nat_mul_zero] at h; exact Nat.noConfusion h
  | j + 1, k + 1, h => by
    rw [nat_mul_succ] at h
    have hle : j + 1 ≤ 1 := by
      have hx := Nat.le_add_left (j + 1) ((j + 1) * k)
      rw [h] at hx; exact hx
    have hj : j = 0 := Nat.succ.inj (Nat.le_antisymm hle (Nat.succ_le_succ (Nat.zero_le j)))
    subst hj
    rw [nat_one_mul] at h
    exact ⟨rfl, congrArg Nat.succ (Nat.succ.inj h)⟩

/-- `x · y = 1 → (x = 1 ∧ y = 1) ∨ (x = −1 ∧ y = −1)` on `Int` — the integer units. By cases on
    the constructors: the same-sign cases reduce to `nat_mul_eq_one`; the mixed-sign products are
    `negOfNat …`, which can never be `1`. -/
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

/-- **The integer unit hyperbola is trivial** — `a² − b² = 1 → (a,b) = (±1, 0)`. Via the
    difference of squares `(a−b)(a+b) = 1` and the integer units (`int_mul_eq_one`): both factors
    equal, so `b = 0` and `a = ±1`. The hyperbolic frame has no proper integer rotation — the
    group-level reason finite foam is Galilean and Lorentz is a continuum emergent. -/
theorem int_pell_one (a b : Int) (h : a * a - b * b = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) := by
  rw [int_sq_diff a b] at h
  -- the two factors are equal (both ±1), so a + (−b) = a + b ⟹ −b = b ⟹ b = 0
  have key : (a - b) = (a + b) → b = 0 := by
    intro heq
    rw [Int.sub_eq_add_neg] at heq
    have hnb : -b = b := int_add_left_cancel a (-b) b heq
    have hbb : b + b = 0 := by
      have hh := int_add_neg_self b
      rw [hnb] at hh
      exact hh
    exact int_add_self_zero b hbb
  cases int_mul_eq_one (a - b) (a + b) h with
  | inl hpq =>
    obtain ⟨hp, hq⟩ := hpq
    have hb0 : b = 0 := key (hp.trans hq.symm)
    rw [hb0, int_sub_zero] at hp
    exact Or.inl ⟨hp, hb0⟩
  | inr hpq =>
    obtain ⟨hp, hq⟩ := hpq
    have hb0 : b = 0 := key (hp.trans hq.symm)
    rw [hb0, int_sub_zero] at hp
    exact Or.inr ⟨hp, hb0⟩

/-! ## Axiom-freeness, pinned (a drift fails the build). -/

/-- info: 'Foam.int_pell_one' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.int_pell_one

end Foam
