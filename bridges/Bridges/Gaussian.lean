import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.ZMod.Basic
import Foam.Seat.Forcing

namespace Foam.Bridges

def toGaussian (z : GInt) : GaussianInt := ⟨z.re, z.im⟩

def ofGaussian (z : GaussianInt) : GInt := ⟨z.re, z.im⟩

theorem the_lattice_is_recognized (z : GInt) (w : GaussianInt) :
    ofGaussian (toGaussian z) = z ∧ toGaussian (ofGaussian w) = w :=
  ⟨rfl, rfl⟩

theorem the_addition_is_recognized (w z : GInt) :
    toGaussian (w.add z) = toGaussian w + toGaussian z := rfl

theorem the_multiplication_is_recognized (w z : GInt) :
    toGaussian (w.mul z) = toGaussian w * toGaussian z := by
  have h : ∀ x y : GaussianInt, x.re = y.re → x.im = y.im → x = y := by
    intro x y h1 h2
    cases x; cases y; cases h1; cases h2; rfl
  apply h
  · show w.re * z.re - w.im * z.im = w.re * z.re + -1 * w.im * z.im
    ring
  · rfl

theorem the_energy_is_recognized (z : GInt) :
    (toGaussian z).norm = z.normSq := by
  show z.re * z.re - -1 * z.im * z.im = z.re * z.re + z.im * z.im
  ring

theorem squares_mod_the_wheel : ∀ x y : ZMod 4, x ^ 2 + y ^ 2 ≠ 3 := by decide

theorem the_wheel_bars_the_dark_primes {p : ℕ} (hp : p % 4 = 3) :
    ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  rintro ⟨a, b, hab⟩
  have hp' : (p : ZMod 4) = 3 := by
    conv_lhs => rw [← Nat.div_add_mod p 4, hp]
    push_cast
    rw [show (4 : ZMod 4) = 0 from rfl]
    ring
  have hcast := congrArg (Nat.cast : ℕ → ZMod 4) hab
  push_cast at hcast
  rw [hp'] at hcast
  exact squares_mod_the_wheel a b hcast

theorem the_wheel_seats_every_undark_prime {p : ℕ} (hp : p.Prime)
    (h1 : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  haveI : Fact p.Prime := ⟨hp⟩
  Nat.Prime.sq_add_sq h1

theorem the_wheel_decides_the_energies {p : ℕ} (hp : p.Prime) :
    (p % 4 ≠ 3 → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p)
      ∧ (p % 4 = 3 → ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = p) :=
  ⟨the_wheel_seats_every_undark_prime hp, the_wheel_bars_the_dark_primes⟩

/-- info: 'Foam.Bridges.the_lattice_is_recognized' does not depend on any axioms -/
#guard_msgs in #print axioms the_lattice_is_recognized

/-- info: 'Foam.Bridges.the_addition_is_recognized' does not depend on any axioms -/
#guard_msgs in #print axioms the_addition_is_recognized

/-- info: 'Foam.Bridges.the_multiplication_is_recognized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms the_multiplication_is_recognized

/-- info: 'Foam.Bridges.the_energy_is_recognized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms the_energy_is_recognized

/-- info: 'Foam.Bridges.squares_mod_the_wheel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms squares_mod_the_wheel

/-- info: 'Foam.Bridges.the_wheel_bars_the_dark_primes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_wheel_bars_the_dark_primes

/-- info: 'Foam.Bridges.the_wheel_seats_every_undark_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_wheel_seats_every_undark_prime

/-- info: 'Foam.Bridges.the_wheel_decides_the_energies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms the_wheel_decides_the_energies

end Foam.Bridges
