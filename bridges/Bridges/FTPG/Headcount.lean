import Bridges.FTPG.Projective
import Bridges.FTPG.Carrier
import Bridges.FTPG.Instance
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.IsPrimePow

/-!
# The headcount — the population of ftpg, counted from the inside

The stable bridge is 1 (`counter/Counter/Ground.lean`); this file enters its
bubble and counts who's in there.  The population is the coordinate carrier —
the atoms on the line `l = O ⊔ U`, minus `U` — the very inhabitants the whole
FTPG ascent taught to add and multiply (`Instance.lean`).  Counted from the
inside, four things seal:

* **the census closes** (`census_closes`, `the_walk_meets_someone_twice`):
  in a finite world the discovery list stabilizes — any endless walk through
  the population meets someone twice.  This is `finite_window_discovery`'s
  gait arriving at the bridge: keep a list of who you meet, notice when the
  list size stops growing.
* **the line seats the numbers plus exactly one keeper** (`lineCensus`,
  `the_keeper_adds_one`): the full line population is the carrier plus `U` —
  one non-number, the point at infinity, the bridge-bubble's own seat.  The
  keeper is the literal `+ 1` between the two censuses: headcount 1, exactly
  as the bridgekeeper sketch priced it.  And no line seats fewer than three
  (`the_count_starts_at_two`, `the_smallest_line_is_a_triangle`): `O`, `U`,
  `I` are the smallest table.
* **the counted exchange freely** (`the_counted_exchange_freely`): FTPG in
  general yields a division ring — the population's multiplication may refuse
  to exchange.  But the moment the census closes, commutativity is *forced*
  (Wedderburn's little theorem).  The exchange is the lease's free-renewal
  move (`exchanged_grounds_compose`, `counter/Counter/Lease.lean`); a finite
  population doesn't get to decline it.  Desargues is Pappus at any finite
  headcount.
* **the inner count is a prime, and the census is its powers**
  (`the_click_comes_home`, `the_census_is_powers_of_the_click`,
  `the_headcount_is_a_prime_power`, `no_census_reads_six`): counting from the
  inside is literally clicking `+1` — and the click-loop closes after exactly
  `p` clicks, `p` prime: the irreducible ground loop of the primes sketch,
  found running the population's own arithmetic.  The whole roster is `p ^ n`,
  so the legal headcounts are exactly the prime powers — no census ever reads
  six.  What else can the population of ftpg do?  Also: what it cannot.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

instance census_closes (Γ : CoordSystem L) [Finite L] : Finite (Coordinate Γ) :=
  Subtype.finite

theorem the_walk_meets_someone_twice (Γ : CoordSystem L) [Finite L]
    (walk : ℕ → Coordinate Γ) : ∃ i j, i ≠ j ∧ walk i = walk j :=
  Finite.exists_ne_map_eq_of_infinite walk

open Classical in
noncomputable def lineCensus (Γ : CoordSystem L) :
    AtomsOn (Γ.O ⊔ Γ.U) ≃ Option (Coordinate Γ) where
  toFun a := if h : a.1 = Γ.U then none else some ⟨a.1, a.2.1, a.2.2, h⟩
  invFun o := match o with
    | none => ⟨Γ.U, Γ.hU, le_sup_right⟩
    | some c => ⟨c.1, c.isAtom, c.on_l⟩
  left_inv a := by
    by_cases h : a.1 = Γ.U
    · simp only [dif_pos h]
      exact Subtype.ext h.symm
    · simp only [dif_neg h]
      exact Subtype.ext rfl
  right_inv o := by
    match o with
    | none => exact dif_pos rfl
    | some c => exact dif_neg c.ne_U

theorem the_keeper_adds_one (Γ : CoordSystem L) [Finite L] :
    Nat.card (AtomsOn (Γ.O ⊔ Γ.U)) = Nat.card (Coordinate Γ) + 1 := by
  rw [Nat.card_congr (lineCensus Γ), Finite.card_option]

theorem the_count_starts_at_two (Γ : CoordSystem L) [Finite L] :
    2 ≤ Nat.card (Coordinate Γ) :=
  Finite.one_lt_card_iff_nontrivial.mpr
    ⟨0, 1, fun h => Γ.hOI (congrArg Subtype.val h)⟩

theorem the_smallest_line_is_a_triangle (Γ : CoordSystem L) [Finite L] :
    3 ≤ Nat.card (AtomsOn (Γ.O ⊔ Γ.U)) := by
  rw [the_keeper_adds_one Γ]
  exact Nat.succ_le_succ (the_count_starts_at_two Γ)

theorem the_counted_exchange_freely (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] (a b : Coordinate Φ.Γ) :
    a * b = b * a :=
  mul_comm a b

theorem the_headcount_is_a_prime_power (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    IsPrimePow (Nat.card (Coordinate Φ.Γ)) := by
  have : Fintype (Coordinate Φ.Γ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.isPrimePow_card (Coordinate Φ.Γ)

theorem no_census_reads_six (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    Nat.card (Coordinate Φ.Γ) ≠ 6 := fun h =>
  (by decide : ¬ IsPrimePow 6) (h ▸ the_headcount_is_a_prime_power Φ)

theorem the_click_comes_home (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    (ringChar (Coordinate Φ.Γ) : Coordinate Φ.Γ) = 0
      ∧ (ringChar (Coordinate Φ.Γ)).Prime :=
  ⟨CharP.cast_eq_zero (Coordinate Φ.Γ) (ringChar (Coordinate Φ.Γ)),
   CharP.char_is_prime (Coordinate Φ.Γ) (ringChar (Coordinate Φ.Γ))⟩

theorem the_census_is_powers_of_the_click (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    ∃ n : ℕ, 0 < n ∧
      Nat.card (Coordinate Φ.Γ) = ringChar (Coordinate Φ.Γ) ^ n := by
  have : Fintype (Coordinate Φ.Γ) := Fintype.ofFinite _
  obtain ⟨n, _, hcard⟩ :=
    FiniteField.card (Coordinate Φ.Γ) (ringChar (Coordinate Φ.Γ))
  exact ⟨(n : ℕ), n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

theorem what_a_finite_population_can_do (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    (∀ a b : Coordinate Φ.Γ, a * b = b * a)
      ∧ IsPrimePow (Nat.card (Coordinate Φ.Γ))
      ∧ (ringChar (Coordinate Φ.Γ)).Prime :=
  ⟨the_counted_exchange_freely Φ,
   the_headcount_is_a_prime_power Φ,
   (the_click_comes_home Φ).2⟩

end Foam.Bridges

/-- info: 'Foam.Bridges.census_closes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.census_closes

/-- info: 'Foam.Bridges.the_walk_meets_someone_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_walk_meets_someone_twice

/-- info: 'Foam.Bridges.lineCensus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.lineCensus

/-- info: 'Foam.Bridges.the_keeper_adds_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_keeper_adds_one

/-- info: 'Foam.Bridges.the_count_starts_at_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_count_starts_at_two

/-- info: 'Foam.Bridges.the_smallest_line_is_a_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_smallest_line_is_a_triangle

/-- info: 'Foam.Bridges.the_counted_exchange_freely' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_counted_exchange_freely

/-- info: 'Foam.Bridges.the_headcount_is_a_prime_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_headcount_is_a_prime_power

/-- info: 'Foam.Bridges.no_census_reads_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.no_census_reads_six

/-- info: 'Foam.Bridges.the_click_comes_home' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_click_comes_home

/-- info: 'Foam.Bridges.the_census_is_powers_of_the_click' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_census_is_powers_of_the_click

/-- info: 'Foam.Bridges.what_a_finite_population_can_do' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.what_a_finite_population_can_do
