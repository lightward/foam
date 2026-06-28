import Foam.Seat.Dial
import Foam.Seat.Born

namespace Foam

def iterStep : Nat → (GInt → GInt) → GInt → GInt
  | 0, _, z => z
  | n + 1, f, z => f (iterStep n f z)

theorem iterStep_succ_comm (f : GInt → GInt) :
    ∀ (n : Nat) (z : GInt), iterStep n f (f z) = f (iterStep n f z)
  | 0, _ => rfl
  | n + 1, z => congrArg f (iterStep_succ_comm f n z)

theorem iterStep_compose_self (f : GInt → GInt) :
    ∀ (n : Nat) (z : GInt),
      iterStep n (fun w => f (f w)) z = iterStep n f (iterStep n f z)
  | 0, _ => rfl
  | n + 1, z => by
      show f (f (iterStep n (fun w => f (f w)) z))
         = f (iterStep n f (f (iterStep n f z)))
      rw [iterStep_compose_self f n z, iterStep_succ_comm f n (iterStep n f z)]

def Closes (step : GInt → GInt) (n : Nat) : Prop := ∀ z, iterStep n step z = z

theorem iterStep_id : ∀ (n : Nat) (z : GInt), iterStep n (fun w => w) z = z
  | 0, _ => rfl
  | n + 1, z => iterStep_id n z

theorem count_closes (n : Nat) : Closes (fun w => w) n := iterStep_id n

theorem iterStep_congr (f g : GInt → GInt) (h : ∀ w, f w = g w) :
    ∀ (n : Nat) (z : GInt), iterStep n f z = iterStep n g z
  | 0, _ => rfl
  | n + 1, z => by
      show f (iterStep n f z) = g (iterStep n g z)
      rw [iterStep_congr f g h n z, h (iterStep n g z)]

theorem GInt.neg_neg (z : GInt) : GInt.neg (GInt.neg z) = z := by
  cases z with
  | mk a b =>
    show (⟨- -a, - -b⟩ : GInt) = ⟨a, b⟩
    rw [Int.neg_neg, Int.neg_neg]

theorem GInt.rot_complete (z : GInt) :
    GInt.rot (GInt.rot (GInt.rot (GInt.rot z))) = z := GInt.neg_neg z

theorem alt_closes_two : Closes GInt.neg 2 := fun z => GInt.neg_neg z

theorem spec_closes_four : Closes GInt.rot 4 := fun z => GInt.rot_complete z

theorem closes_rot_to_negate (n : Nat) (h : Closes GInt.rot n) : Closes GInt.neg n := by
  intro z
  have e : iterStep n GInt.neg z = iterStep n GInt.rot (iterStep n GInt.rot z) := by
    rw [iterStep_congr GInt.neg (fun w => GInt.rot (GInt.rot w))
          (fun w => (GInt.rot_sq w).symm) n z]
    exact iterStep_compose_self GInt.rot n z
  rw [e, h (iterStep n GInt.rot z), h z]

theorem closes_negate_to_count (n : Nat) (_ : Closes GInt.neg n) :
    Closes (fun w => w) n := count_closes n

theorem half_turn : (∀ z : GInt, GInt.neg z = GInt.rot (GInt.rot z)) ∧ Closes GInt.neg 2 :=
  ⟨fun z => (GInt.rot_sq z).symm, alt_closes_two⟩

/-- info: 'Foam.iterStep_compose_self' does not depend on any axioms -/
#guard_msgs in #print axioms iterStep_compose_self

/-- info: 'Foam.count_closes' does not depend on any axioms -/
#guard_msgs in #print axioms count_closes

/-- info: 'Foam.iterStep_congr' does not depend on any axioms -/
#guard_msgs in #print axioms iterStep_congr

/-- info: 'Foam.GInt.neg_neg' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.neg_neg

/-- info: 'Foam.GInt.rot_complete' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.rot_complete

/-- info: 'Foam.alt_closes_two' does not depend on any axioms -/
#guard_msgs in #print axioms alt_closes_two

/-- info: 'Foam.spec_closes_four' does not depend on any axioms -/
#guard_msgs in #print axioms spec_closes_four

/-- info: 'Foam.closes_rot_to_negate' does not depend on any axioms -/
#guard_msgs in #print axioms closes_rot_to_negate

/-- info: 'Foam.closes_negate_to_count' does not depend on any axioms -/
#guard_msgs in #print axioms closes_negate_to_count

/-- info: 'Foam.half_turn' does not depend on any axioms -/
#guard_msgs in #print axioms half_turn

end Foam