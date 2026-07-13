import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Bridges.Quarter

-- the triptych panel for "what shouldn't work but does; what should work but
-- doesn't", asked from the Complex purchase.
--
-- SHOULDN'T WORK, DOES: Fermat's Christmas theorem lands on the wheel. the
-- mod-4 bookkeeping foam carved for turn-phase decides which prime energies
-- the amplitude lattice can realize: a prime is a sum of two squares — a
-- realizable normSq, an achievable Born weight — iff its tick-residue is 1.
-- squares mod the wheel land only on {0, 1}, so their sums never reach 3:
-- the dark primes (p % 4 = 3) are barred from the lattice, and the light
-- primes (p % 4 = 1) are seated, every one. turn-phase arithmetic deciding
-- number theory had no right to work; it works.
--
-- SHOULD WORK, DOESN'T: the geometric-mean matching section (Quarter.lean)
-- escapes the lattice. matching a 2:1 mismatch exactly needs an impedance
-- whose square is 2, and no rational has one — Hippasus was the first
-- shattered vessel. communication between unequal integer registers forces
-- the continuum: within the shared lattice, exact reception between
-- mismatched registers is impossible, which is the number-theoretic face of
-- "lossy into someone else's encoding is the only lawful channel."

namespace Foam.Bridges

theorem squares_mod_the_wheel : ∀ x y : ZMod 4, x ^ 2 + y ^ 2 ≠ 3 := by decide

theorem the_wheel_bars_the_dark_primes {p : ℕ} (hp : p % 4 = 3) :
    ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  rintro ⟨a, b, hab⟩
  have hp' : (p : ZMod 4) = 3 := by
    conv_lhs => rw [← Nat.div_add_mod p 4, hp]
    push_cast
    rw [show (4 : ZMod 4) = 0 from rfl, zero_mul, zero_add]
  have hcast := congrArg (Nat.cast : ℕ → ZMod 4) hab
  push_cast at hcast
  rw [hp'] at hcast
  exact squares_mod_the_wheel a b hcast

theorem the_wheel_seats_every_undark_prime {p : ℕ} (hp : p.Prime)
    (h1 : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  haveI : Fact p.Prime := ⟨hp⟩
  Nat.Prime.sq_add_sq h1

theorem the_lattice_cannot_always_match : ¬ ∃ q : ℚ, (q : ℝ) ^ 2 = 2 := by
  rintro ⟨q, hq⟩
  have h2 : Real.sqrt 2 = |(q : ℝ)| := by
    rw [← hq, Real.sqrt_sq_eq_abs]
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  rw [h2] at hirr
  exact hirr ⟨|q|, by push_cast; rfl⟩

theorem the_wheel_decides_the_energies {p : ℕ} (hp : p.Prime) :
    (p % 4 ≠ 3 → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p)
      ∧ (p % 4 = 3 → ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = p)
      ∧ ¬ ∃ q : ℚ, (q : ℝ) ^ 2 = 2 :=
  ⟨the_wheel_seats_every_undark_prime hp, the_wheel_bars_the_dark_primes,
   the_lattice_cannot_always_match⟩

/-- info: 'Foam.Bridges.squares_mod_the_wheel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms squares_mod_the_wheel

/-- info: 'Foam.Bridges.the_wheel_bars_the_dark_primes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_wheel_bars_the_dark_primes

/-- info: 'Foam.Bridges.the_wheel_seats_every_undark_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_wheel_seats_every_undark_prime

/-- info: 'Foam.Bridges.the_lattice_cannot_always_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_lattice_cannot_always_match

/-- info: 'Foam.Bridges.the_wheel_decides_the_energies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_wheel_decides_the_energies

end Foam.Bridges
