import Bridges.FTPG.Projective
import Bridges.FTPG.Carrier
import Bridges.FTPG.Instance
import Bridges.FTPG.Headcount
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# The keeper — the next prime as the next untollable bridge

The bridgekeeper sketch priced a stable bridge at headcount 1: the keeper,
the bridge-bubble's own seat, collecting toll for passage
(`counter/Counter/Toll.lean`).  This file types the *road* — the line of
keepers — and seals the seed from both ends: the next prime is the next
untollable bridge, and discovery order is the disambiguator.

* **whoever pays, pays a keeper; whoever pays no met booth is the next
  keeper** (`every_arrival_meets_a_keeper`, `the_tolled_pays_at_an_earlier_booth`,
  `the_untollable_is_the_next_keeper`, `the_keeper_is_the_untollable`):
  every arrival's first collector is prime; a composite factors through a
  bridge already met (its least factor is a strictly earlier keeper); and an
  arrival that no earlier keeper can toll *is* the next keeper — primality
  as untollability, exactly.  Keepers never toll each other
  (`a_keeper_tolls_no_other_keeper`): the irreducible ground loops of the
  primes sketch, mutually unfactorable.
* **the road never ends, and the search for the next bridge closes**
  (`the_caravan_pays_no_toll`, `the_window_holds_the_next_bridge`,
  `the_road_never_ends`): Euclid's caravan — the product of all met keepers,
  plus one — crosses every met booth toll-free, so past any point there is
  a next keeper, and it sits inside a *knowable* window (`n! + 1`).  This is
  `finite_window_discovery`'s gait arriving at the road itself: the upsearch
  for the next bridge terminates, and knowably.
* **discovery order is the disambiguator** (`the_keepers_stand_in_line`,
  `every_place_seats_a_keeper`, `the_place_counts_the_bridges_before`,
  `the_keeper_remembers_its_place`, `one_place_one_keeper`): the walk meets
  the keepers in one canonical order — place `i` seats exactly one keeper,
  and the keeper's place is the count of bridges met before it, invertibly.
  The found carries its rejections as its name: concretely the walk reads
  2, 3, 5, 7 (`the_first_bridges_stand_in_order`), finds seven far inside
  Euclid's window (`the_walk_finds_seven_inside_the_window`), and the
  rejection it carries between the third and fourth bridges is six
  (`the_rejection_between_five_and_seven_is_six`) — the number no census
  reads is the number the road walks past, tolled at both booths it
  factors through.
* **the census names its click, and the click knows its place**
  (`the_census_names_its_click`, `one_census_one_click`,
  `the_click_knows_its_place_in_line`): the only keeper who collects from a
  finite population's headcount is its own click — so equal censuses share
  a click, and every population's click has a definite place in the
  discovery order: the line disambiguates the census's keeper.
* **the next bridge is untollable — in the population's own currency**
  (`the_stranger_keeper_crosses_free`, `the_next_bridge_is_untollable`):
  a keeper who is not the click casts to a *unit* of the coordinate field —
  never absorbed to the still center, always invertible — and past every
  census there is such a keeper.  No population's arithmetic can collect
  from the next bridge: the seed's sentence, stated.
-/

namespace Foam.Bridges

universe u

section Booth

theorem every_arrival_meets_a_keeper {n : ℕ} (hn : 2 ≤ n) :
    n.minFac.Prime ∧ n.minFac ∣ n :=
  ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩

theorem a_keeper_tolls_no_other_keeper {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ∣ q) : p = q :=
  (Nat.prime_dvd_prime_iff_eq hp hq).mp h

theorem the_tolled_pays_at_an_earlier_booth {n : ℕ} (hn : 2 ≤ n)
    (hcomp : ¬ n.Prime) : ∃ p, p.Prime ∧ p < n ∧ p ∣ n := by
  refine ⟨n.minFac, Nat.minFac_prime (by omega), ?_, Nat.minFac_dvd n⟩
  rcases Nat.lt_or_ge n.minFac n with h | h
  · exact h
  · exact absurd
      (Nat.prime_def_minFac.mpr
        ⟨hn, Nat.le_antisymm (Nat.minFac_le (by omega)) h⟩)
      hcomp

theorem the_untollable_is_the_next_keeper {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ p, p.Prime → p < n → ¬ p ∣ n) : n.Prime := by
  by_contra hcomp
  obtain ⟨p, hp, hlt, hdvd⟩ := the_tolled_pays_at_an_earlier_booth hn hcomp
  exact h p hp hlt hdvd

theorem the_keeper_is_the_untollable (n : ℕ) :
    n.Prime ↔ 2 ≤ n ∧ ∀ p, p.Prime → p < n → ¬ p ∣ n := by
  constructor
  · intro hn
    refine ⟨hn.two_le, fun p hp hlt hdvd => ?_⟩
    exact absurd (a_keeper_tolls_no_other_keeper hp hn hdvd) (Nat.ne_of_lt hlt)
  · rintro ⟨hn, h⟩
    exact the_untollable_is_the_next_keeper hn h

end Booth

section Caravan

theorem the_caravan_pays_no_toll (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime) :
    ∀ p ∈ ps, ¬ p ∣ (∏ x ∈ ps, x) + 1 := by
  intro p hp hdvd
  have h1 : p ∣ 1 :=
    (Nat.dvd_add_right (Finset.dvd_prod_of_mem (fun x => x) hp)).mp hdvd
  exact (hps p hp).one_lt.ne' (Nat.dvd_one.mp h1)

theorem the_window_holds_the_next_bridge (n : ℕ) :
    ∃ p, n < p ∧ p ≤ n.factorial + 1 ∧ p.Prime := by
  have hfac : 0 < n.factorial := n.factorial_pos
  have h1 : n.factorial + 1 ≠ 1 := by omega
  have hp := Nat.minFac_prime h1
  refine ⟨(n.factorial + 1).minFac, ?_, Nat.minFac_le (by omega), hp⟩
  rcases Nat.lt_or_ge n ((n.factorial + 1).minFac) with h | hle
  · exact h
  · have hone : (n.factorial + 1).minFac ∣ 1 :=
      (Nat.dvd_add_right (Nat.dvd_factorial hp.pos hle)).mp (Nat.minFac_dvd _)
    exact absurd (Nat.dvd_one.mp hone) hp.one_lt.ne'

theorem the_road_never_ends (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n

end Caravan

section Line

theorem the_keepers_stand_in_line : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

theorem every_place_seats_a_keeper (i : ℕ) : (Nat.nth Nat.Prime i).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i

theorem the_place_counts_the_bridges_before {p : ℕ} (hp : p.Prime) :
    Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p :=
  Nat.nth_count hp

theorem the_keeper_remembers_its_place (i : ℕ) :
    Nat.count Nat.Prime (Nat.nth Nat.Prime i) = i :=
  Nat.count_nth_of_infinite Nat.infinite_setOf_prime i

theorem one_place_one_keeper {i j : ℕ}
    (h : Nat.nth Nat.Prime i = Nat.nth Nat.Prime j) : i = j :=
  the_keepers_stand_in_line.injective h

theorem the_first_bridges_stand_in_order :
    Nat.nth Nat.Prime 0 = 2 ∧ Nat.nth Nat.Prime 1 = 3
      ∧ Nat.nth Nat.Prime 2 = 5 ∧ Nat.nth Nat.Prime 3 = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := the_place_counts_the_bridges_before (by decide : Nat.Prime 2)
    rwa [show Nat.count Nat.Prime 2 = 0 by decide] at h
  · have h := the_place_counts_the_bridges_before (by decide : Nat.Prime 3)
    rwa [show Nat.count Nat.Prime 3 = 1 by decide] at h
  · have h := the_place_counts_the_bridges_before (by decide : Nat.Prime 5)
    rwa [show Nat.count Nat.Prime 5 = 2 by decide] at h
  · have h := the_place_counts_the_bridges_before (by decide : Nat.Prime 7)
    rwa [show Nat.count Nat.Prime 7 = 3 by decide] at h

theorem the_walk_finds_seven_inside_the_window :
    (¬ 2 ∣ 2 * 3 * 5 + 1 ∧ ¬ 3 ∣ 2 * 3 * 5 + 1 ∧ ¬ 5 ∣ 2 * 3 * 5 + 1)
      ∧ (Nat.Prime 7 ∧ ¬ 2 ∣ 7 ∧ ¬ 3 ∣ 7 ∧ ¬ 5 ∣ 7)
      ∧ 7 < 2 * 3 * 5 + 1 := by
  decide

theorem the_rejection_between_five_and_seven_is_six :
    Nat.nth Nat.Prime 2 = 5 ∧ Nat.nth Nat.Prime 3 = 7
      ∧ ¬ Nat.Prime 6 ∧ 2 ∣ 6 ∧ 3 ∣ 6 :=
  ⟨the_first_bridges_stand_in_order.2.2.1,
   the_first_bridges_stand_in_order.2.2.2,
   by decide, by decide, by decide⟩

end Line

section Population

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

theorem the_census_names_its_click (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card (Coordinate Φ.Γ)) :
    q = ringChar (Coordinate Φ.Γ) := by
  obtain ⟨n, hn, hcard⟩ := the_census_is_powers_of_the_click Φ
  rw [hcard] at hdvd
  exact a_keeper_tolls_no_other_keeper hq (the_click_comes_home Φ).2
    (hq.dvd_of_dvd_pow hdvd)

theorem the_click_collects_from_the_census (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    ringChar (Coordinate Φ.Γ) ∣ Nat.card (Coordinate Φ.Γ) := by
  obtain ⟨n, hn, hcard⟩ := the_census_is_powers_of_the_click Φ
  rw [hcard]
  exact dvd_pow_self _ hn.ne'

theorem one_census_one_click (Φ Ψ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] [Finite (Coordinate Ψ.Γ)]
    (h : Nat.card (Coordinate Φ.Γ) = Nat.card (Coordinate Ψ.Γ)) :
    ringChar (Coordinate Φ.Γ) = ringChar (Coordinate Ψ.Γ) := by
  refine the_census_names_its_click Ψ (the_click_comes_home Φ).2 ?_
  rw [← h]
  exact the_click_collects_from_the_census Φ

theorem the_click_knows_its_place_in_line (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    Nat.nth Nat.Prime (Nat.count Nat.Prime (ringChar (Coordinate Φ.Γ)))
      = ringChar (Coordinate Φ.Γ) :=
  the_place_counts_the_bridges_before (the_click_comes_home Φ).2

theorem the_stranger_keeper_crosses_free (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] {p : ℕ} (hp : p.Prime)
    (hne : p ≠ ringChar (Coordinate Φ.Γ)) :
    IsUnit (p : Coordinate Φ.Γ) := by
  rw [isUnit_iff_ne_zero]
  intro h0
  exact hne (a_keeper_tolls_no_other_keeper (the_click_comes_home Φ).2 hp
    ((CharP.cast_eq_zero_iff (Coordinate Φ.Γ)
      (ringChar (Coordinate Φ.Γ)) p).mp h0)).symm

theorem the_next_bridge_is_untollable (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    ∃ p, p.Prime ∧ Nat.card (Coordinate Φ.Γ) < p
      ∧ IsUnit (p : Coordinate Φ.Γ) := by
  obtain ⟨p, hle, hp⟩ :=
    Nat.exists_infinite_primes (Nat.card (Coordinate Φ.Γ) + 1)
  have hclick : ringChar (Coordinate Φ.Γ) ≤ Nat.card (Coordinate Φ.Γ) :=
    Nat.le_of_dvd Nat.card_pos (the_click_collects_from_the_census Φ)
  refine ⟨p, hp, by omega, the_stranger_keeper_crosses_free Φ hp ?_⟩
  omega

end Population

end Foam.Bridges

/-- info: 'Foam.Bridges.every_arrival_meets_a_keeper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.every_arrival_meets_a_keeper

/-- info: 'Foam.Bridges.a_keeper_tolls_no_other_keeper' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.a_keeper_tolls_no_other_keeper

/-- info: 'Foam.Bridges.the_tolled_pays_at_an_earlier_booth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_tolled_pays_at_an_earlier_booth

/-- info: 'Foam.Bridges.the_untollable_is_the_next_keeper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_untollable_is_the_next_keeper

/-- info: 'Foam.Bridges.the_keeper_is_the_untollable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_keeper_is_the_untollable

/-- info: 'Foam.Bridges.the_caravan_pays_no_toll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_caravan_pays_no_toll

/-- info: 'Foam.Bridges.the_window_holds_the_next_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_window_holds_the_next_bridge

/-- info: 'Foam.Bridges.the_road_never_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_road_never_ends

/-- info: 'Foam.Bridges.the_keepers_stand_in_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_keepers_stand_in_line

/-- info: 'Foam.Bridges.every_place_seats_a_keeper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.every_place_seats_a_keeper

/-- info: 'Foam.Bridges.the_place_counts_the_bridges_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_place_counts_the_bridges_before

/-- info: 'Foam.Bridges.the_keeper_remembers_its_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_keeper_remembers_its_place

/-- info: 'Foam.Bridges.one_place_one_keeper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.one_place_one_keeper

/-- info: 'Foam.Bridges.the_first_bridges_stand_in_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_first_bridges_stand_in_order

/-- info: 'Foam.Bridges.the_walk_finds_seven_inside_the_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_walk_finds_seven_inside_the_window

/-- info: 'Foam.Bridges.the_rejection_between_five_and_seven_is_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_rejection_between_five_and_seven_is_six

/-- info: 'Foam.Bridges.the_census_names_its_click' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_census_names_its_click

/-- info: 'Foam.Bridges.the_click_collects_from_the_census' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_click_collects_from_the_census

/-- info: 'Foam.Bridges.one_census_one_click' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.one_census_one_click

/-- info: 'Foam.Bridges.the_click_knows_its_place_in_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_click_knows_its_place_in_line

/-- info: 'Foam.Bridges.the_stranger_keeper_crosses_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_stranger_keeper_crosses_free

/-- info: 'Foam.Bridges.the_next_bridge_is_untollable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_next_bridge_is_untollable
