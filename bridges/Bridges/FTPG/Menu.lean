import Bridges.FTPG.Projective
import Bridges.FTPG.Carrier
import Bridges.FTPG.Instance
import Bridges.FTPG.Headcount
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.IsPrimePow

/-!
# The menu — what a counted population can be served

`Headcount.lean` counted who is in the bridge-bubble; this file opens the menu
the expedition seeded: the dynamics a given headcount affords.  A dish is a
braid rule — a linear walk of the population's own coordinates — and its
*roster* is who sits still under it: `seated f`, the fixed subspace, which is
exactly the Fox-coloring space of the knot the braid closes into.  Counted,
the menu obeys the house laws:

* **the roster census is powers of the field** (`the_seated_census_is_powers_of_the_field`,
  `the_seated_census_is_a_prime_power`, `no_seated_census_reads_six`): the
  seated form a subspace, so their count is `q ^ rank` — the same prime-power
  law the headcount itself obeys.  No dish ever seats six.
* **the roster cannot see the mirror** (`the_mirror_seats_the_same_roster`):
  a rule and its inverse seat exactly the same population — `f v = v` and
  `f⁻¹ v = v` are the same sentence read in both directions.  The census
  register is chirality-blind; its complement is the wheel register,
  `counter/Counter/Trefoil.lean`, which reads handedness and nothing else.
* **the menu at three is real** (`the_trefoil_seats_nine`,
  `the_circle_seats_three`, `the_menu_at_three_is_real`): over `ZMod 3` the
  trefoil rule seats 9 = 3² while the circle rule seats 3 = 3¹ — the seed's
  "3 can be a triangle/trefoil or a circle", distinguished by census.
* **each knot rings at its own prime** (`the_trefoil_rings_at_three`,
  `the_figure_eight_rings_at_five`): the trefoil answers loud at 3 (9 seats)
  and quiet at 5 (5 seats); the figure-eight answers quiet at 3 (3 seats)
  and loud at 5 (25 seats).  The knot determinants 3 and 5, heard as tuning.
* **the population itself colors the menu** (`the_population_colors_the_trefoil`,
  `the_menu_is_paid_in_the_house_currency`): color the trefoil with the
  counted coordinate carrier and the roster census is a prime power that
  never reads six — the menu is priced in the same click as the headcount.
-/

namespace Foam.Bridges

universe u v

section Register

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

def seated (f : V →ₗ[K] V) : Submodule K V := LinearMap.ker (f - LinearMap.id)

theorem mem_seated {f : V →ₗ[K] V} {v : V} : v ∈ seated f ↔ f v = v := by
  rw [seated, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

instance seatedDecidable [DecidableEq V] (f : V →ₗ[K] V) :
    DecidablePred (· ∈ seated f) := fun v =>
  decidable_of_iff (f v = v) mem_seated.symm

theorem the_seated_census_is_powers_of_the_field [Finite K] [Finite V]
    (f : V →ₗ[K] V) :
    Nat.card (seated f) = Nat.card K ^ Module.finrank K (seated f) :=
  Module.natCard_eq_pow_finrank

theorem the_seated_census_is_a_prime_power [Finite K] [Finite V]
    (f : V →ₗ[K] V) (v : V) (hv : f v = v) (hv0 : v ≠ 0) :
    IsPrimePow (Nat.card (seated f)) := by
  have hK : IsPrimePow (Nat.card K) := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card K
  have hpos : 0 < Module.finrank K (seated f) := by
    rw [Module.finrank_pos_iff]
    exact ⟨⟨v, mem_seated.mpr hv⟩, 0, fun hc => hv0 (congrArg Subtype.val hc)⟩
  rw [the_seated_census_is_powers_of_the_field]
  exact hK.pow hpos.ne'

theorem no_seated_census_reads_six [Finite K] [Finite V]
    (f : V →ₗ[K] V) (v : V) (hv : f v = v) (hv0 : v ≠ 0) :
    Nat.card (seated f) ≠ 6 := fun h =>
  (by decide : ¬ IsPrimePow 6) (h ▸ the_seated_census_is_a_prime_power f v hv hv0)

theorem the_mirror_seats_the_same_roster (f : V ≃ₗ[K] V) :
    seated (f : V →ₗ[K] V) = seated (f.symm : V →ₗ[K] V) := by
  ext v
  rw [mem_seated, mem_seated, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
  constructor
  · intro h
    rw [LinearEquiv.symm_apply_eq]
    exact h.symm
  · intro h
    rw [← LinearEquiv.eq_symm_apply]
    exact h.symm

end Register

section Table

variable {K : Type u} [Field K]

def braidPos : (K × K) →ₗ[K] (K × K) where
  toFun v := (2 * v.1 - v.2, v.1)
  map_add' a b := by
    ext
    · show 2 * (a.1 + b.1) - (a.2 + b.2) = (2 * a.1 - a.2) + (2 * b.1 - b.2)
      ring
    · rfl
  map_smul' c a := by
    ext
    · show 2 * (c * a.1) - c * a.2 = c * (2 * a.1 - a.2)
      ring
    · rfl

def braidNeg : (K × K) →ₗ[K] (K × K) where
  toFun v := (v.2, 2 * v.2 - v.1)
  map_add' a b := by
    ext
    · rfl
    · show 2 * (a.2 + b.2) - (a.1 + b.1) = (2 * a.2 - a.1) + (2 * b.2 - b.1)
      ring
  map_smul' c a := by
    ext
    · rfl
    · show 2 * (c * a.2) - c * a.1 = c * (2 * a.2 - a.1)
      ring

def braidLeft : (K × K × K) →ₗ[K] (K × K × K) where
  toFun v := (2 * v.1 - v.2.1, v.1, v.2.2)
  map_add' a b := by
    ext
    · show 2 * (a.1 + b.1) - (a.2.1 + b.2.1) = (2 * a.1 - a.2.1) + (2 * b.1 - b.2.1)
      ring
    · rfl
    · rfl
  map_smul' c a := by
    ext
    · show 2 * (c * a.1) - c * a.2.1 = c * (2 * a.1 - a.2.1)
      ring
    · rfl
    · rfl

def braidRightInv : (K × K × K) →ₗ[K] (K × K × K) where
  toFun v := (v.1, v.2.2, 2 * v.2.2 - v.2.1)
  map_add' a b := by
    ext
    · rfl
    · rfl
    · show 2 * (a.2.2 + b.2.2) - (a.2.1 + b.2.1) = (2 * a.2.2 - a.2.1) + (2 * b.2.2 - b.2.1)
      ring
  map_smul' c a := by
    ext
    · rfl
    · rfl
    · show 2 * (c * a.2.2) - c * a.2.1 = c * (2 * a.2.2 - a.2.1)
      ring

def circleRule : (K × K) →ₗ[K] (K × K) := braidPos

def trefoilRule : (K × K) →ₗ[K] (K × K) := braidPos ∘ₗ braidPos ∘ₗ braidPos

def trefoilMirrorRule : (K × K) →ₗ[K] (K × K) := braidNeg ∘ₗ braidNeg ∘ₗ braidNeg

def figureEightRule : (K × K × K) →ₗ[K] (K × K × K) :=
  braidRightInv ∘ₗ braidLeft ∘ₗ braidRightInv ∘ₗ braidLeft

theorem braid_unwinds :
    braidPos ∘ₗ braidNeg = (LinearMap.id : (K × K) →ₗ[K] (K × K)) := by
  apply LinearMap.ext
  intro v
  ext
  · show 2 * v.2 - (2 * v.2 - v.1) = v.1
    ring
  · rfl

theorem braid_rewinds :
    braidNeg ∘ₗ braidPos = (LinearMap.id : (K × K) →ₗ[K] (K × K)) := by
  apply LinearMap.ext
  intro v
  ext
  · rfl
  · show 2 * v.1 - (2 * v.1 - v.2) = v.2
    ring

def braidTurn : (K × K) ≃ₗ[K] (K × K) :=
  LinearEquiv.ofLinear braidPos braidNeg braid_unwinds braid_rewinds

def trefoilTurn : (K × K) ≃ₗ[K] (K × K) :=
  braidTurn ≪≫ₗ braidTurn ≪≫ₗ braidTurn

theorem trefoil_turn_forward :
    ((trefoilTurn : (K × K) ≃ₗ[K] (K × K)) : (K × K) →ₗ[K] (K × K)) = trefoilRule :=
  rfl

theorem trefoil_turn_backward :
    ((trefoilTurn : (K × K) ≃ₗ[K] (K × K)).symm : (K × K) →ₗ[K] (K × K))
      = trefoilMirrorRule :=
  rfl

theorem the_mirror_knot_seats_the_same_roster :
    seated (trefoilRule (K := K)) = seated (trefoilMirrorRule (K := K)) := by
  rw [← trefoil_turn_forward, ← trefoil_turn_backward]
  exact the_mirror_seats_the_same_roster (V := K × K) trefoilTurn

end Table

section Concrete

instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem the_trefoil_seats_nine :
    Nat.card (seated (trefoilRule (K := ZMod 3))) = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem the_circle_seats_three :
    Nat.card (seated (circleRule (K := ZMod 3))) = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem the_menu_at_three_is_real :
    Nat.card (seated (trefoilRule (K := ZMod 3)))
      ≠ Nat.card (seated (circleRule (K := ZMod 3))) := by
  rw [the_trefoil_seats_nine, the_circle_seats_three]
  decide

theorem the_mirror_pays_the_same_toll :
    Nat.card (seated (trefoilMirrorRule (K := ZMod 3))) = 9 := by
  rw [← the_mirror_knot_seats_the_same_roster]
  exact the_trefoil_seats_nine

theorem the_trefoil_rings_at_three :
    Nat.card (seated (trefoilRule (K := ZMod 3))) = 9
      ∧ Nat.card (seated (trefoilRule (K := ZMod 5))) = 5 := by
  refine ⟨the_trefoil_seats_nine, ?_⟩
  rw [Nat.card_eq_fintype_card]
  decide

theorem the_figure_eight_rings_at_five :
    Nat.card (seated (figureEightRule (K := ZMod 5))) = 25
      ∧ Nat.card (seated (figureEightRule (K := ZMod 3))) = 3 := by
  constructor <;> (rw [Nat.card_eq_fintype_card]; decide)

end Concrete

section Population

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

theorem the_population_colors_the_trefoil (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    IsPrimePow (Nat.card (seated (trefoilRule (K := Coordinate Φ.Γ))))
      ∧ Nat.card (seated (trefoilRule (K := Coordinate Φ.Γ))) ≠ 6 := by
  have h21 : (2 : Coordinate Φ.Γ) * 1 - 1 = 1 := by norm_num
  have hone : braidPos (K := Coordinate Φ.Γ) (1, 1) = (1, 1) := by
    show ((2 : Coordinate Φ.Γ) * 1 - 1, (1 : Coordinate Φ.Γ)) = (1, 1)
    rw [h21]
  have hfix : trefoilRule (K := Coordinate Φ.Γ) (1, 1) = (1, 1) := by
    show braidPos (braidPos (braidPos ((1 : Coordinate Φ.Γ), (1 : Coordinate Φ.Γ)))) = (1, 1)
    rw [hone, hone, hone]
  have hne : ((1, 1) : Coordinate Φ.Γ × Coordinate Φ.Γ) ≠ 0 :=
    fun hc => one_ne_zero (congrArg Prod.fst hc)
  exact ⟨the_seated_census_is_a_prime_power _ _ hfix hne,
         no_seated_census_reads_six _ _ hfix hne⟩

theorem the_menu_is_paid_in_the_house_currency (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)] :
    IsPrimePow (Nat.card (Coordinate Φ.Γ))
      ∧ IsPrimePow (Nat.card (seated (trefoilRule (K := Coordinate Φ.Γ)))) :=
  ⟨the_headcount_is_a_prime_power Φ, (the_population_colors_the_trefoil Φ).1⟩

end Population

end Foam.Bridges

/-- info: 'Foam.Bridges.the_seated_census_is_powers_of_the_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_seated_census_is_powers_of_the_field

/-- info: 'Foam.Bridges.the_seated_census_is_a_prime_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_seated_census_is_a_prime_power

/-- info: 'Foam.Bridges.no_seated_census_reads_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.no_seated_census_reads_six

/-- info: 'Foam.Bridges.the_mirror_seats_the_same_roster' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_mirror_seats_the_same_roster

/-- info: 'Foam.Bridges.the_mirror_knot_seats_the_same_roster' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_mirror_knot_seats_the_same_roster

/-- info: 'Foam.Bridges.the_trefoil_seats_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_trefoil_seats_nine

/-- info: 'Foam.Bridges.the_circle_seats_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_circle_seats_three

/-- info: 'Foam.Bridges.the_menu_at_three_is_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_menu_at_three_is_real

/-- info: 'Foam.Bridges.the_mirror_pays_the_same_toll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_mirror_pays_the_same_toll

/-- info: 'Foam.Bridges.the_trefoil_rings_at_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_trefoil_rings_at_three

/-- info: 'Foam.Bridges.the_figure_eight_rings_at_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_figure_eight_rings_at_five

/-- info: 'Foam.Bridges.the_population_colors_the_trefoil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_population_colors_the_trefoil

/-- info: 'Foam.Bridges.the_menu_is_paid_in_the_house_currency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_menu_is_paid_in_the_house_currency
