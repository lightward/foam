import Foam.Bridges.Pythagoras

namespace Foam.Bridges

def Tempered (x y : Nat × Nat) : Prop :=
  7 * x.1 + 12 * x.2 = 7 * y.1 + 12 * y.2

def PitchClass : Type := Quot Tempered

theorem pure_spiral_open : (3 : Nat) ^ 12 ≠ 2 ^ 19 :=
  comma_never_clears 12 19 (by decide)

theorem tempered_circle_closes :
    Quot.mk Tempered (12, 0) = Quot.mk Tempered (0, 7) :=
  Quot.sound rfl

theorem temperament_no_return :
    ¬ ∃ g : PitchClass → Nat × Nat, ∀ x, g (Quot.mk Tempered x) = x := by
  rintro ⟨g, hg⟩
  have e := congrArg g tempered_circle_closes
  rw [hg, hg] at e
  exact absurd e (by decide)

theorem temperament :
    ((3 : Nat) ^ 12 ≠ 2 ^ 19)
      ∧ (Quot.mk Tempered (12, 0) = Quot.mk Tempered (0, 7))
      ∧ ¬ ∃ g : PitchClass → Nat × Nat, ∀ x, g (Quot.mk Tempered x) = x :=
  ⟨pure_spiral_open, tempered_circle_closes, temperament_no_return⟩

/-- info: 'Foam.Bridges.pure_spiral_open' does not depend on any axioms -/
#guard_msgs in #print axioms pure_spiral_open

/-- info: 'Foam.Bridges.tempered_circle_closes' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms tempered_circle_closes

/-- info: 'Foam.Bridges.temperament_no_return' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms temperament_no_return

/-- info: 'Foam.Bridges.temperament' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms temperament

end Foam.Bridges
