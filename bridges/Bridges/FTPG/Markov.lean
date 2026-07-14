import Bridges.FTPG.Menu
import Bridges.FTPG.Carrier
import Bridges.FTPG.CoordinateAlgebra
import Mathlib.Tactic.LinearCombination

/-!
# Markov — the census register cannot hear the recipe

`Menu.lean` priced each dish by its roster: `seated f`, who sits still under
the braid rule.  But a knot arrives as a *recipe* — a braid word — and the
same dish has many recipes.  Markov's theorem says two braid words close into
the same knot exactly when they are related by the two Markov moves:
conjugation (reseat the table, same dish) and stabilization (set one more
place and cross it once, either hand).  This file proves the census register
blind to both:

* **the reseating carries the roster** (`the_reseating_carries_the_roster`,
  `a_reseating_moves_no_headcount`): conjugating the rule maps the seated
  onto the seated — the roster travels bodily with the reseating, headcount
  intact.
* **the new strand seats no one new** (`stabilized_fixes_iff`,
  `the_new_strand_seats_no_one_new`): a stabilized recipe's stillness answers
  entirely to the old table — the new seat merely copies its neighbor — so
  the census is unchanged, whichever hand the new crossing uses.
* **the census hears the dish, not the recipe**
  (`the_census_hears_the_dish_not_the_recipe`, `two_recipes_one_roster`):
  any conjugation of any stabilization seats exactly the old roster, and any
  two Markov rewritings of one dish agree with each other.  Concretely
  (`the_stabilized_trefoil_seats_nine`,
  `the_reseated_recipe_seats_the_same_nine`): σ₂σ₁³ and its conjugates over
  `ZMod 3` seat the same nine the two-strand trefoil recipe seats.
* **the house cannot hear it either** (`the_population_cannot_hear_the_recipe`):
  in the counted population's own currency, every Markov rewriting of the
  trefoil recipe still seats a prime power, and never six.

The complementary register keeps its complement: the toll booth
(`counter/Counter/Toll.lean`) *charges* for the very move this register
cannot hear — stabilization is the kink, R1, `the_kink_pays_and_shows` —
while this register hears the knot itself.  One reads the writhe, the other
the closure; between them the recipe and the dish stay distinguishable.
-/

namespace Foam.Bridges

universe u v

section Reseat

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

def rearranged (g : V ≃ₗ[K] V) (f : V →ₗ[K] V) : V →ₗ[K] V :=
  (g : V →ₗ[K] V) ∘ₗ f ∘ₗ (g.symm : V →ₗ[K] V)

theorem mem_seated_rearranged {g : V ≃ₗ[K] V} {f : V →ₗ[K] V} {v : V} :
    v ∈ seated (rearranged g f) ↔ g.symm v ∈ seated f := by
  rw [mem_seated, mem_seated]
  simp only [rearranged, LinearMap.comp_apply, LinearEquiv.coe_coe]
  constructor
  · intro h
    apply g.injective
    rw [g.apply_symm_apply]
    exact h
  · intro h
    rw [h, g.apply_symm_apply]

theorem the_reseating_carries_the_roster (g : V ≃ₗ[K] V) (f : V →ₗ[K] V) :
    seated (rearranged g f) = (seated f).map (g : V →ₗ[K] V) := by
  ext v
  rw [mem_seated_rearranged, Submodule.mem_map]
  constructor
  · intro h
    exact ⟨g.symm v, h, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    simpa using hw

theorem a_reseating_moves_no_headcount (g : V ≃ₗ[K] V) (f : V →ₗ[K] V) :
    Nat.card (seated (rearranged g f)) = Nat.card (seated f) := by
  rw [the_reseating_carries_the_roster]
  exact (Nat.card_congr (g.submoduleMap (seated f)).toEquiv).symm

end Reseat

section Stabilize

variable {K : Type u} [Field K]

def braidRight : (K × K × K) →ₗ[K] (K × K × K) where
  toFun v := (v.1, 2 * v.2.1 - v.2.2, v.2.1)
  map_add' a b := by
    ext
    · rfl
    · show 2 * (a.2.1 + b.2.1) - (a.2.2 + b.2.2) = (2 * a.2.1 - a.2.2) + (2 * b.2.1 - b.2.2)
      ring
    · rfl
  map_smul' c a := by
    ext
    · rfl
    · show 2 * (c * a.2.1) - c * a.2.2 = c * (2 * a.2.1 - a.2.2)
      ring
    · rfl

theorem braid_right_unwinds :
    braidRight ∘ₗ braidRightInv = (LinearMap.id : (K × K × K) →ₗ[K] (K × K × K)) := by
  apply LinearMap.ext
  intro v
  ext
  · rfl
  · show 2 * v.2.2 - (2 * v.2.2 - v.2.1) = v.2.1
    ring
  · rfl

theorem braid_right_rewinds :
    braidRightInv ∘ₗ braidRight = (LinearMap.id : (K × K × K) →ₗ[K] (K × K × K)) := by
  apply LinearMap.ext
  intro v
  ext
  · rfl
  · rfl
  · show 2 * v.2.1 - (2 * v.2.1 - v.2.2) = v.2.2
    ring

def braidRightTurn : (K × K × K) ≃ₗ[K] (K × K × K) :=
  LinearEquiv.ofLinear braidRight braidRightInv braid_right_unwinds braid_right_rewinds

def widened (f : (K × K) →ₗ[K] (K × K)) : (K × K × K) →ₗ[K] (K × K × K) where
  toFun v := ((f (v.1, v.2.1)).1, (f (v.1, v.2.1)).2, v.2.2)
  map_add' a b := by
    have h : f ((a + b).1, (a + b).2.1) = f (a.1, a.2.1) + f (b.1, b.2.1) :=
      f.map_add (a.1, a.2.1) (b.1, b.2.1)
    ext
    · show (f ((a + b).1, (a + b).2.1)).1 = (f (a.1, a.2.1) + f (b.1, b.2.1)).1
      exact congrArg Prod.fst h
    · show (f ((a + b).1, (a + b).2.1)).2 = (f (a.1, a.2.1) + f (b.1, b.2.1)).2
      exact congrArg Prod.snd h
    · rfl
  map_smul' c a := by
    have h : f ((c • a).1, (c • a).2.1) = c • f (a.1, a.2.1) :=
      f.map_smul c (a.1, a.2.1)
    ext
    · show (f ((c • a).1, (c • a).2.1)).1 = (c • f (a.1, a.2.1)).1
      exact congrArg Prod.fst h
    · show (f ((c • a).1, (c • a).2.1)).2 = (c • f (a.1, a.2.1)).2
      exact congrArg Prod.snd h
    · rfl

def stabilized (f : (K × K) →ₗ[K] (K × K)) : (K × K × K) →ₗ[K] (K × K × K) :=
  braidRight ∘ₗ widened f

def stabilizedMirror (f : (K × K) →ₗ[K] (K × K)) : (K × K × K) →ₗ[K] (K × K × K) :=
  braidRightInv ∘ₗ widened f

theorem stabilized_fixes_iff (f : (K × K) →ₗ[K] (K × K)) (v : K × K × K) :
    stabilized f v = v ↔ f (v.1, v.2.1) = (v.1, v.2.1) ∧ v.2.2 = v.2.1 := by
  constructor
  · intro h
    have h' : ((f (v.1, v.2.1)).1, 2 * (f (v.1, v.2.1)).2 - v.2.2, (f (v.1, v.2.1)).2)
        = (v.1, v.2.1, v.2.2) := h
    injection h' with h1 hrest
    injection hrest with h2 h3
    have hz : v.2.2 = v.2.1 := by linear_combination h2 - 2 * h3
    refine ⟨?_, hz⟩
    ext
    · exact h1
    · exact h3.trans hz
  · rintro ⟨hf, hz⟩
    have hf1 : (f (v.1, v.2.1)).1 = v.1 := by rw [hf]
    have hf2 : (f (v.1, v.2.1)).2 = v.2.1 := by rw [hf]
    ext
    · show (f (v.1, v.2.1)).1 = v.1
      exact hf1
    · show 2 * (f (v.1, v.2.1)).2 - v.2.2 = v.2.1
      rw [hf2, hz]
      ring
    · show (f (v.1, v.2.1)).2 = v.2.2
      rw [hf2]
      exact hz.symm

theorem stabilizedMirror_fixes_iff (f : (K × K) →ₗ[K] (K × K)) (v : K × K × K) :
    stabilizedMirror f v = v ↔ f (v.1, v.2.1) = (v.1, v.2.1) ∧ v.2.2 = v.2.1 := by
  constructor
  · intro h
    have h' : ((f (v.1, v.2.1)).1, v.2.2, 2 * v.2.2 - (f (v.1, v.2.1)).2)
        = (v.1, v.2.1, v.2.2) := h
    injection h' with h1 hrest
    injection hrest with h2 h3
    have hF : (f (v.1, v.2.1)).2 = v.2.1 := by linear_combination h2 - h3
    refine ⟨?_, h2⟩
    ext
    · exact h1
    · exact hF
  · rintro ⟨hf, hz⟩
    have hf1 : (f (v.1, v.2.1)).1 = v.1 := by rw [hf]
    have hf2 : (f (v.1, v.2.1)).2 = v.2.1 := by rw [hf]
    ext
    · show (f (v.1, v.2.1)).1 = v.1
      exact hf1
    · show v.2.2 = v.2.1
      exact hz
    · show 2 * v.2.2 - (f (v.1, v.2.1)).2 = v.2.2
      rw [hf2, hz]
      ring

theorem seated_census_of_answering (f : (K × K) →ₗ[K] (K × K))
    {g : (K × K × K) →ₗ[K] (K × K × K)}
    (hg : ∀ v : K × K × K, g v = v ↔ f (v.1, v.2.1) = (v.1, v.2.1) ∧ v.2.2 = v.2.1) :
    Nat.card (seated g) = Nat.card (seated f) :=
  Nat.card_congr
    { toFun := fun v => ⟨(v.1.1, v.1.2.1),
        mem_seated.mpr ((hg v.1).mp (mem_seated.mp v.2)).1⟩
      invFun := fun w => ⟨(w.1.1, w.1.2, w.1.2),
        mem_seated.mpr ((hg (w.1.1, w.1.2, w.1.2)).mpr ⟨mem_seated.mp w.2, rfl⟩)⟩
      left_inv := fun v => Subtype.ext (by
        have hz := ((hg v.1).mp (mem_seated.mp v.2)).2
        ext
        · rfl
        · rfl
        · exact hz.symm)
      right_inv := fun w => Subtype.ext rfl }

theorem the_new_strand_seats_no_one_new (f : (K × K) →ₗ[K] (K × K)) :
    Nat.card (seated (stabilized f)) = Nat.card (seated f)
      ∧ Nat.card (seated (stabilizedMirror f)) = Nat.card (seated f) :=
  ⟨seated_census_of_answering f (stabilized_fixes_iff f),
   seated_census_of_answering f (stabilizedMirror_fixes_iff f)⟩

theorem the_census_hears_the_dish_not_the_recipe
    (f : (K × K) →ₗ[K] (K × K)) (g : (K × K × K) ≃ₗ[K] (K × K × K)) :
    Nat.card (seated (rearranged g (stabilized f))) = Nat.card (seated f) := by
  rw [a_reseating_moves_no_headcount]
  exact (the_new_strand_seats_no_one_new f).1

theorem two_recipes_one_roster (f : (K × K) →ₗ[K] (K × K))
    (g g' : (K × K × K) ≃ₗ[K] (K × K × K)) :
    Nat.card (seated (rearranged g (stabilized f)))
      = Nat.card (seated (rearranged g' (stabilizedMirror f))) := by
  rw [a_reseating_moves_no_headcount, a_reseating_moves_no_headcount,
      (the_new_strand_seats_no_one_new f).1, (the_new_strand_seats_no_one_new f).2]

end Stabilize

section Concrete

theorem the_stabilized_trefoil_seats_nine :
    Nat.card (seated (stabilized (trefoilRule (K := ZMod 3)))) = 9 := by
  rw [(the_new_strand_seats_no_one_new (trefoilRule (K := ZMod 3))).1]
  exact the_trefoil_seats_nine

theorem the_reseated_recipe_seats_the_same_nine :
    Nat.card (seated (rearranged braidRightTurn
      (stabilized (trefoilRule (K := ZMod 3))))) = 9 := by
  rw [the_census_hears_the_dish_not_the_recipe]
  exact the_trefoil_seats_nine

end Concrete

section Population

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

theorem the_population_cannot_hear_the_recipe (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)]
    (g : (Coordinate Φ.Γ × Coordinate Φ.Γ × Coordinate Φ.Γ)
        ≃ₗ[Coordinate Φ.Γ]
        (Coordinate Φ.Γ × Coordinate Φ.Γ × Coordinate Φ.Γ)) :
    IsPrimePow (Nat.card (seated (rearranged g
        (stabilized (trefoilRule (K := Coordinate Φ.Γ))))))
      ∧ Nat.card (seated (rearranged g
        (stabilized (trefoilRule (K := Coordinate Φ.Γ))))) ≠ 6 := by
  rw [the_census_hears_the_dish_not_the_recipe]
  exact the_population_colors_the_trefoil Φ

end Population

end Foam.Bridges

/-- info: 'Foam.Bridges.the_reseating_carries_the_roster' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_reseating_carries_the_roster

/-- info: 'Foam.Bridges.a_reseating_moves_no_headcount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.a_reseating_moves_no_headcount

/-- info: 'Foam.Bridges.the_new_strand_seats_no_one_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_new_strand_seats_no_one_new

/-- info: 'Foam.Bridges.the_census_hears_the_dish_not_the_recipe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_census_hears_the_dish_not_the_recipe

/-- info: 'Foam.Bridges.two_recipes_one_roster' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.two_recipes_one_roster

/-- info: 'Foam.Bridges.the_stabilized_trefoil_seats_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_stabilized_trefoil_seats_nine

/-- info: 'Foam.Bridges.the_reseated_recipe_seats_the_same_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_reseated_recipe_seats_the_same_nine

/-- info: 'Foam.Bridges.the_population_cannot_hear_the_recipe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_population_cannot_hear_the_recipe
