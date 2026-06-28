import Mathlib.RepresentationTheory.Maschke
import Foam.Seat.Clock

namespace Foam.Bridges

open Foam

noncomputable instance : Fintype Rot :=
  Fintype.ofList [Rot.r0, Rot.r1, Rot.r2, Rot.r3] (fun x => by cases x <;> decide)

instance : Group Rot where
  mul := (· * ·)
  one := 1
  inv := Rot.inv
  mul_assoc := Grp.mul_assoc
  one_mul := Grp.one_mul
  mul_one := Grp.mul_one
  inv_mul_cancel := Grp.inv_mul

theorem clock_coordinatizes_in_time (k : Type) [Field k] [CharZero k]
    (V : Type) [AddCommGroup V] [Module (MonoidAlgebra k Rot) V] :
    (∀ (g x : Rot), clock.act g x = g * x)
      ∧ ComplementedLattice (Submodule (MonoidAlgebra k Rot) V)
      ∧ IsModularLattice (Submodule (MonoidAlgebra k Rot) V) := by
  haveI : NeZero (Nat.card Rot : k) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨by norm_num [show Fintype.card Rot = 4 from by decide]⟩
  exact ⟨fun _ _ => rfl, inferInstance, inferInstance⟩

theorem clock_regular_rep_coordinatizes (k : Type) [Field k] [CharZero k] :
    ComplementedLattice (Submodule (MonoidAlgebra k Rot) (MonoidAlgebra k Rot)) :=
  (clock_coordinatizes_in_time k (MonoidAlgebra k Rot)).2.1

/-- info: 'Foam.Bridges.clock_coordinatizes_in_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clock_coordinatizes_in_time

/-- info: 'Foam.Bridges.clock_regular_rep_coordinatizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clock_regular_rep_coordinatizes

end Foam.Bridges
