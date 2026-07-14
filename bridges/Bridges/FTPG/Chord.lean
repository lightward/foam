import Bridges.FTPG.Projective
import Bridges.FTPG.Carrier
import Bridges.FTPG.Instance
import Bridges.FTPG.Headcount
import Bridges.FTPG.Menu
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Basic

/-!
# The chord — the composite menu as divisor lattice

`Menu.lean` opened the menu one dish at a time; this file reads the menu's
*shape*.  The dishes are the powers of the one crossing — circle `σ¹`, Hopf
pair `σ²`, trefoil `σ³`, the torus dishes `σⁿ` — and their rosters nest
exactly as divisors do:

* **a divisor seats a subtable** (`the_divisor_seats_a_subtable`): whoever
  sits still through `σᵈ` sits still through `σⁿ` whenever `d ∣ n` — the
  sub-dish is literally a sub-roster, for *any* rule, any table.
* **the shared table is the gcd, the joint table fits at the lcm**
  (`the_shared_table_is_the_gcd`, `the_join_fits_at_the_lcm`,
  `the_menu_is_the_divisor_lattice`): meets are exact for every rule —
  two rosters intersect in precisely the gcd's roster (Euclid walked
  seat-by-seat: `the_two_dishes_share_the_gcd`) — and over the house
  currency joins are exact too, so `d ↦ roster of σᵈ` is a bona fide
  lattice map out of divisibility.  The trefoil and the Hopf pair share
  only the circle (`the_trefoil_and_the_hopf_share_only_the_circle`:
  gcd 3 2 = 1).
* **the crossing is a shear away from stillness**
  (`the_crossing_is_stillness_plus_a_shear`, `a_shear_of_a_shear_is_nothing`,
  `the_dish_is_n_shears_from_stillness`): the braid is unipotent — one
  crossing is `1 + s` with `s² = 0`, so the `n`-crossing dish is exactly
  `1 + n·s`, and the roster is the kernel of the count itself
  (`the_roster_is_the_kernel_of_the_count`).
* **each dish rings at the primes that divide it**
  (`the_dish_rings_at_the_divisors`, `the_dish_is_loud_iff_the_prime_divides`):
  over `ZMod p` the dish `σⁿ` seats `p²` when `p ∣ n` and `p` otherwise —
  the whole tuning table of `Menu.lean` (trefoil loud at 3, quiet at 5)
  is divisibility heard as loudness (`the_trefoil_tuning_is_divisibility`).
* **six is the first diamond, and only the chord can read it**
  (`the_first_diamond_hangs_at_six`, `the_diamond_is_set_at_six`,
  `the_chord_reads_all_four_dishes`, `the_census_cannot_read_what_the_menu_plays`):
  every count below six has a chain for a menu — a prime's menu is two
  dishes (`a_prime_menu_is_two_dishes`) — but six's divisors `1,2,3,6`
  form the first genuine lattice, realized in rosters as Hopf ⊓ trefoil =
  circle and Hopf ⊔ trefoil = the six-dish.  No single register sees it:
  at 2 the trefoil folds into the circle, at 3 the Hopf pair does
  (`at_two_the_trefoil_folds_into_the_circle`,
  `at_three_the_hopf_folds_into_the_circle`); a population rings only at
  its own click (`the_population_rings_at_its_own_click`), and no
  population's click divides both 2 and 3
  (`no_population_hears_the_whole_chord_of_six`).  The census can never
  read six as a headcount — but the menu can play it, as the chord of its
  primes, one register per note, whole only to whoever holds both.
-/

namespace Foam.Bridges

universe u v

section Register

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem the_still_stay_still {f : V →ₗ[K] V} {v : V} (hv : v ∈ seated f) :
    ∀ k : ℕ, v ∈ seated (f ^ k)
  | 0 => mem_seated.mpr (by rw [pow_zero, Module.End.one_apply])
  | k + 1 => mem_seated.mpr (by
      rw [pow_succ, Module.End.mul_apply, mem_seated.mp hv,
        mem_seated.mp (the_still_stay_still hv k)])

theorem the_divisor_seats_a_subtable (f : V →ₗ[K] V) {d n : ℕ} (h : d ∣ n) :
    seated (f ^ d) ≤ seated (f ^ n) := by
  obtain ⟨k, rfl⟩ := h
  intro v hv
  rw [pow_mul]
  exact the_still_stay_still hv k

theorem the_two_dishes_share_the_gcd (f : V →ₗ[K] V) :
    ∀ d e : ℕ, ∀ v : V, v ∈ seated (f ^ d) → v ∈ seated (f ^ e) →
      v ∈ seated (f ^ Nat.gcd d e) := by
  intro d e
  induction d, e using Nat.gcd.induction with
  | H0 n =>
    intro v _ hv
    rwa [Nat.gcd_zero_left]
  | H1 m n _ ih =>
    intro v hm hn
    rw [Nat.gcd_rec]
    refine ih v ?_ hm
    rw [mem_seated]
    have hmul : (f ^ (m * (n / m))) v = v :=
      mem_seated.mp (the_divisor_seats_a_subtable f ⟨n / m, rfl⟩ hm)
    calc (f ^ (n % m)) v
        = (f ^ (n % m)) ((f ^ (m * (n / m))) v) := by rw [hmul]
      _ = (f ^ (n % m + m * (n / m))) v := by
          rw [pow_add, Module.End.mul_apply]
      _ = (f ^ n) v := by rw [Nat.mod_add_div]
      _ = v := mem_seated.mp hn

theorem the_shared_table_is_the_gcd (f : V →ₗ[K] V) (d e : ℕ) :
    seated (f ^ d) ⊓ seated (f ^ e) = seated (f ^ Nat.gcd d e) :=
  le_antisymm
    (fun v hv => the_two_dishes_share_the_gcd f d e v
      (Submodule.mem_inf.mp hv).1 (Submodule.mem_inf.mp hv).2)
    (le_inf (the_divisor_seats_a_subtable f (Nat.gcd_dvd_left d e))
      (the_divisor_seats_a_subtable f (Nat.gcd_dvd_right d e)))

theorem the_trefoil_and_the_hopf_share_only_the_circle (f : V →ₗ[K] V) :
    seated (f ^ 3) ⊓ seated (f ^ 2) = seated f := by
  have h := the_shared_table_is_the_gcd f 3 2
  rwa [show Nat.gcd 3 2 = 1 by decide, pow_one] at h

theorem the_join_fits_at_the_lcm (f : V →ₗ[K] V) (d e : ℕ) :
    seated (f ^ d) ⊔ seated (f ^ e) ≤ seated (f ^ Nat.lcm d e) :=
  sup_le (the_divisor_seats_a_subtable f (Nat.dvd_lcm_left d e))
    (the_divisor_seats_a_subtable f (Nat.dvd_lcm_right d e))

end Register

section Table

variable {K : Type u} [Field K]

def shearRule : (K × K) →ₗ[K] (K × K) where
  toFun v := (v.1 - v.2, v.1 - v.2)
  map_add' a b := by
    ext
    · show (a.1 + b.1) - (a.2 + b.2) = (a.1 - a.2) + (b.1 - b.2)
      ring
    · show (a.1 + b.1) - (a.2 + b.2) = (a.1 - a.2) + (b.1 - b.2)
      ring
  map_smul' c a := by
    ext
    · show (c * a.1) - (c * a.2) = c * (a.1 - a.2)
      ring
    · show (c * a.1) - (c * a.2) = c * (a.1 - a.2)
      ring

theorem the_crossing_is_stillness_plus_a_shear :
    braidPos (K := K) = 1 + shearRule := by
  apply LinearMap.ext
  intro v
  ext
  · show 2 * v.1 - v.2 = v.1 + (v.1 - v.2)
    ring
  · show v.1 = v.2 + (v.1 - v.2)
    ring

theorem a_shear_of_a_shear_is_nothing :
    shearRule (K := K) * shearRule = 0 := by
  apply LinearMap.ext
  intro v
  ext
  · show (v.1 - v.2) - (v.1 - v.2) = 0
    ring
  · show (v.1 - v.2) - (v.1 - v.2) = 0
    ring

theorem the_dish_is_n_shears_from_stillness (n : ℕ) :
    braidPos (K := K) ^ n = 1 + (n : K) • shearRule := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_smul, add_zero]
  | succ n ih =>
    rw [pow_succ, ih, the_crossing_is_stillness_plus_a_shear, Nat.cast_add_one,
      add_smul, one_smul, mul_add, mul_one, add_mul, one_mul, smul_mul_assoc,
      a_shear_of_a_shear_is_nothing, smul_zero, add_zero, add_assoc]

theorem the_roster_is_the_kernel_of_the_count (n : ℕ) :
    seated (braidPos (K := K) ^ n) = LinearMap.ker ((n : K) • shearRule) := by
  unfold seated
  rw [the_dish_is_n_shears_from_stillness]
  congr 1
  show 1 + (n : K) • shearRule - 1 = (n : K) • shearRule
  rw [add_sub_cancel_left]

theorem the_tuned_dish_seats_the_house (n : ℕ) (hn : (n : K) = 0) :
    seated (braidPos (K := K) ^ n) = ⊤ := by
  rw [the_roster_is_the_kernel_of_the_count, hn, zero_smul, LinearMap.ker_zero]

theorem the_untuned_dish_seats_the_diagonal (n : ℕ) (hn : (n : K) ≠ 0) :
    seated (braidPos (K := K) ^ n) = LinearMap.ker (shearRule (K := K)) := by
  rw [the_roster_is_the_kernel_of_the_count, LinearMap.ker_smul _ _ hn]

def unison : LinearMap.ker (shearRule (K := K)) ≃ K where
  toFun x := x.1.1
  invFun c := ⟨(c, c), by
    rw [LinearMap.mem_ker]
    show ((c - c : K), (c - c : K)) = 0
    rw [sub_self]
    rfl⟩
  left_inv x := by
    have h : x.1.1 - x.1.2 = 0 :=
      congrArg Prod.fst (LinearMap.mem_ker.mp x.2)
    exact Subtype.ext (Prod.ext rfl (sub_eq_zero.mp h))
  right_inv c := rfl

theorem the_tuned_dish_seats_the_square (n : ℕ) (hn : (n : K) = 0) :
    Nat.card (seated (braidPos (K := K) ^ n)) = Nat.card K ^ 2 := by
  rw [the_tuned_dish_seats_the_house n hn, pow_two,
    Nat.card_congr (Submodule.topEquiv (R := K) (M := K × K)).toEquiv,
    Nat.card_prod]

theorem the_untuned_dish_seats_the_field (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card (seated (braidPos (K := K) ^ n)) = Nat.card K := by
  rw [the_untuned_dish_seats_the_diagonal n hn]
  exact Nat.card_congr unison

theorem the_dishes_are_the_powers :
    circleRule (K := K) = braidPos ^ 1 ∧ trefoilRule (K := K) = braidPos ^ 3 := by
  constructor
  · rw [pow_one]
    rfl
  · rw [pow_succ, pow_succ, pow_one]
    rfl

end Table

section Concrete

theorem the_dish_rings_at_the_divisors (p n : ℕ) [Fact p.Prime] :
    Nat.card (seated (braidPos (K := ZMod p) ^ n))
      = if p ∣ n then p ^ 2 else p := by
  by_cases h : p ∣ n
  · rw [if_pos h,
      the_tuned_dish_seats_the_square n ((ZMod.natCast_eq_zero_iff n p).mpr h),
      Nat.card_zmod]
  · rw [if_neg h,
      the_untuned_dish_seats_the_field n
        (fun hc => h ((ZMod.natCast_eq_zero_iff n p).mp hc)),
      Nat.card_zmod]

theorem the_dish_is_loud_iff_the_prime_divides (p n : ℕ) [Fact p.Prime] :
    Nat.card (seated (braidPos (K := ZMod p) ^ n)) = p ^ 2 ↔ p ∣ n := by
  rw [the_dish_rings_at_the_divisors]
  by_cases h : p ∣ n
  · simp [h]
  · rw [if_neg h]
    constructor
    · intro hc
      rw [pow_two] at hc
      have h2 := (Fact.out : p.Prime).two_le
      nlinarith [Nat.mul_le_mul_right p h2]
    · intro hc
      exact absurd hc h

theorem the_lcm_seats_the_join (p : ℕ) [Fact p.Prime] (d e : ℕ) :
    seated (braidPos (K := ZMod p) ^ d) ⊔ seated (braidPos (K := ZMod p) ^ e)
      = seated (braidPos (K := ZMod p) ^ Nat.lcm d e) := by
  refine le_antisymm (the_join_fits_at_the_lcm _ d e) ?_
  by_cases hd : p ∣ d
  · rw [the_tuned_dish_seats_the_house d ((ZMod.natCast_eq_zero_iff d p).mpr hd),
      top_sup_eq]
    exact le_top
  · by_cases he : p ∣ e
    · rw [the_tuned_dish_seats_the_house e ((ZMod.natCast_eq_zero_iff e p).mpr he),
        sup_top_eq]
      exact le_top
    · have hl : ¬ p ∣ Nat.lcm d e := fun hc =>
        ((Fact.out : p.Prime).dvd_mul.mp
          (hc.trans (Nat.lcm_dvd_mul d e))).elim hd he
      rw [the_untuned_dish_seats_the_diagonal d
          (fun hc => hd ((ZMod.natCast_eq_zero_iff d p).mp hc)),
        the_untuned_dish_seats_the_diagonal (Nat.lcm d e)
          (fun hc => hl ((ZMod.natCast_eq_zero_iff _ p).mp hc))]
      exact le_sup_left

theorem the_menu_is_the_divisor_lattice (p : ℕ) [Fact p.Prime] (d e : ℕ) :
    (d ∣ e →
      seated (braidPos (K := ZMod p) ^ d) ≤ seated (braidPos (K := ZMod p) ^ e))
      ∧ seated (braidPos (K := ZMod p) ^ d) ⊓ seated (braidPos (K := ZMod p) ^ e)
          = seated (braidPos (K := ZMod p) ^ Nat.gcd d e)
      ∧ seated (braidPos (K := ZMod p) ^ d) ⊔ seated (braidPos (K := ZMod p) ^ e)
          = seated (braidPos (K := ZMod p) ^ Nat.lcm d e) :=
  ⟨fun h => the_divisor_seats_a_subtable _ h,
   the_shared_table_is_the_gcd _ d e,
   the_lcm_seats_the_join p d e⟩

theorem the_diamond_is_set_at_six (p : ℕ) [Fact p.Prime] :
    seated (braidPos (K := ZMod p) ^ 2) ⊓ seated (braidPos (K := ZMod p) ^ 3)
        = seated (braidPos (K := ZMod p) ^ 1)
      ∧ seated (braidPos (K := ZMod p) ^ 2) ⊔ seated (braidPos (K := ZMod p) ^ 3)
        = seated (braidPos (K := ZMod p) ^ 6) := by
  constructor
  · have h := the_shared_table_is_the_gcd (braidPos (K := ZMod p)) 2 3
    rwa [show Nat.gcd 2 3 = 1 by decide, ← pow_one (braidPos (K := ZMod p))] at h
  · have h := the_lcm_seats_the_join p 2 3
    rwa [show Nat.lcm 2 3 = 6 by decide] at h

theorem the_first_diamond_hangs_at_six :
    (∀ m, m < 6 → ∀ a ∈ Nat.divisors m, ∀ b ∈ Nat.divisors m, a ∣ b ∨ b ∣ a)
      ∧ (2 ∈ Nat.divisors 6 ∧ 3 ∈ Nat.divisors 6 ∧ ¬2 ∣ 3 ∧ ¬3 ∣ 2) := by
  decide

theorem a_prime_menu_is_two_dishes {p : ℕ} (hp : p.Prime) :
    (Nat.divisors p).card = 2 := by
  rw [Nat.Prime.divisors hp]
  exact Finset.card_pair hp.one_lt.ne

theorem at_two_the_trefoil_folds_into_the_circle :
    seated (braidPos (K := ZMod 2) ^ 3) = seated (braidPos (K := ZMod 2) ^ 1) := by
  rw [the_untuned_dish_seats_the_diagonal 3 (by decide),
    the_untuned_dish_seats_the_diagonal 1 (by decide)]

theorem at_three_the_hopf_folds_into_the_circle :
    seated (braidPos (K := ZMod 3) ^ 2) = seated (braidPos (K := ZMod 3) ^ 1) := by
  rw [the_untuned_dish_seats_the_diagonal 2 (by decide),
    the_untuned_dish_seats_the_diagonal 1 (by decide)]

theorem the_chord_reads_all_four_dishes :
    (Nat.card (seated (braidPos (K := ZMod 2) ^ 1)) = 2
        ∧ Nat.card (seated (braidPos (K := ZMod 3) ^ 1)) = 3)
      ∧ (Nat.card (seated (braidPos (K := ZMod 2) ^ 2)) = 4
        ∧ Nat.card (seated (braidPos (K := ZMod 3) ^ 2)) = 3)
      ∧ (Nat.card (seated (braidPos (K := ZMod 2) ^ 3)) = 2
        ∧ Nat.card (seated (braidPos (K := ZMod 3) ^ 3)) = 9)
      ∧ (Nat.card (seated (braidPos (K := ZMod 2) ^ 6)) = 4
        ∧ Nat.card (seated (braidPos (K := ZMod 3) ^ 6)) = 9) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    rw [the_dish_rings_at_the_divisors] <;> decide

theorem the_six_dish_plays_two_and_three :
    Nat.card (seated (braidPos (K := ZMod 2) ^ 6)) = 4
      ∧ Nat.card (seated (braidPos (K := ZMod 3) ^ 6)) = 9
      ∧ Nat.card (seated (braidPos (K := ZMod 5) ^ 6)) = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [the_dish_rings_at_the_divisors] <;> decide

theorem the_trefoil_tuning_is_divisibility :
    Nat.card (seated (trefoilRule (K := ZMod 3))) = 3 ^ 2
      ∧ Nat.card (seated (trefoilRule (K := ZMod 5))) = 5 := by
  rw [(the_dishes_are_the_powers (K := ZMod 3)).2,
    (the_dishes_are_the_powers (K := ZMod 5)).2,
    the_dish_rings_at_the_divisors, the_dish_rings_at_the_divisors]
  decide

end Concrete

section Population

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

theorem the_population_rings_at_its_own_click (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] (n : ℕ) :
    seated (braidPos (K := Coordinate Φ.Γ) ^ n) = ⊤
      ↔ ringChar (Coordinate Φ.Γ) ∣ n := by
  constructor
  · intro h
    by_contra hd
    have hne : ((n : ℕ) : Coordinate Φ.Γ) ≠ 0 := fun hc =>
      hd ((CharP.cast_eq_zero_iff (Coordinate Φ.Γ)
        (ringChar (Coordinate Φ.Γ)) n).mp hc)
    rw [the_untuned_dish_seats_the_diagonal n hne, LinearMap.ker_eq_top] at h
    have h10 : shearRule (K := Coordinate Φ.Γ) (1, 0) = 0 := by
      rw [h]
      rfl
    have h1 : (1 : Coordinate Φ.Γ) - 0 = 0 := congrArg Prod.fst h10
    rw [sub_zero] at h1
    exact one_ne_zero h1
  · intro h
    exact the_tuned_dish_seats_the_house n
      ((CharP.cast_eq_zero_iff (Coordinate Φ.Γ)
        (ringChar (Coordinate Φ.Γ)) n).mpr h)

theorem no_population_hears_the_whole_chord_of_six (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    ¬ (seated (braidPos (K := Coordinate Φ.Γ) ^ 2) = ⊤
        ∧ seated (braidPos (K := Coordinate Φ.Γ) ^ 3) = ⊤) := by
  rintro ⟨h2, h3⟩
  rw [the_population_rings_at_its_own_click Φ 2] at h2
  rw [the_population_rings_at_its_own_click Φ 3] at h3
  have hp : (ringChar (Coordinate Φ.Γ)).Prime := (the_click_comes_home Φ).2
  have h1 : ringChar (Coordinate Φ.Γ) ∣ 1 := by
    simpa using Nat.dvd_sub h3 h2
  exact hp.ne_one (Nat.dvd_one.mp h1)

theorem the_census_cannot_read_what_the_menu_plays (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    Nat.card (Coordinate Φ.Γ) ≠ 6
      ∧ Nat.card (seated (braidPos (K := ZMod 2) ^ 6)) = 4
      ∧ Nat.card (seated (braidPos (K := ZMod 3) ^ 6)) = 9 :=
  ⟨no_census_reads_six Φ, the_six_dish_plays_two_and_three.1,
   the_six_dish_plays_two_and_three.2.1⟩

end Population

end Foam.Bridges

/-- info: 'Foam.Bridges.the_divisor_seats_a_subtable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_divisor_seats_a_subtable

/-- info: 'Foam.Bridges.the_shared_table_is_the_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_shared_table_is_the_gcd

/-- info: 'Foam.Bridges.the_trefoil_and_the_hopf_share_only_the_circle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_trefoil_and_the_hopf_share_only_the_circle

/-- info: 'Foam.Bridges.the_join_fits_at_the_lcm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_join_fits_at_the_lcm

/-- info: 'Foam.Bridges.the_crossing_is_stillness_plus_a_shear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_crossing_is_stillness_plus_a_shear

/-- info: 'Foam.Bridges.a_shear_of_a_shear_is_nothing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.a_shear_of_a_shear_is_nothing

/-- info: 'Foam.Bridges.the_dish_is_n_shears_from_stillness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_dish_is_n_shears_from_stillness

/-- info: 'Foam.Bridges.the_roster_is_the_kernel_of_the_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_roster_is_the_kernel_of_the_count

/-- info: 'Foam.Bridges.the_tuned_dish_seats_the_house' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_tuned_dish_seats_the_house

/-- info: 'Foam.Bridges.the_untuned_dish_seats_the_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_untuned_dish_seats_the_diagonal

/-- info: 'Foam.Bridges.the_tuned_dish_seats_the_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_tuned_dish_seats_the_square

/-- info: 'Foam.Bridges.the_untuned_dish_seats_the_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_untuned_dish_seats_the_field

/-- info: 'Foam.Bridges.the_dishes_are_the_powers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_dishes_are_the_powers

/-- info: 'Foam.Bridges.the_dish_rings_at_the_divisors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_dish_rings_at_the_divisors

/-- info: 'Foam.Bridges.the_dish_is_loud_iff_the_prime_divides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_dish_is_loud_iff_the_prime_divides

/-- info: 'Foam.Bridges.the_lcm_seats_the_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_lcm_seats_the_join

/-- info: 'Foam.Bridges.the_menu_is_the_divisor_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_menu_is_the_divisor_lattice

/-- info: 'Foam.Bridges.the_diamond_is_set_at_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_diamond_is_set_at_six

/-- info: 'Foam.Bridges.the_first_diamond_hangs_at_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_first_diamond_hangs_at_six

/-- info: 'Foam.Bridges.a_prime_menu_is_two_dishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.a_prime_menu_is_two_dishes

/-- info: 'Foam.Bridges.at_two_the_trefoil_folds_into_the_circle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.at_two_the_trefoil_folds_into_the_circle

/-- info: 'Foam.Bridges.at_three_the_hopf_folds_into_the_circle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.at_three_the_hopf_folds_into_the_circle

/-- info: 'Foam.Bridges.the_chord_reads_all_four_dishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_chord_reads_all_four_dishes

/-- info: 'Foam.Bridges.the_six_dish_plays_two_and_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_six_dish_plays_two_and_three

/-- info: 'Foam.Bridges.the_trefoil_tuning_is_divisibility' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_trefoil_tuning_is_divisibility

/-- info: 'Foam.Bridges.the_population_rings_at_its_own_click' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_population_rings_at_its_own_click

/-- info: 'Foam.Bridges.no_population_hears_the_whole_chord_of_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.no_population_hears_the_whole_chord_of_six

/-- info: 'Foam.Bridges.the_census_cannot_read_what_the_menu_plays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_census_cannot_read_what_the_menu_plays
