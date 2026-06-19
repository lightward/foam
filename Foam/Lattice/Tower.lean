import Foam.Lattice.Dial
import Foam.Lattice.Refinement

namespace Foam.Lattice

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

theorem alt_closes_two : Closes GInt.negate 2 := fun z => GInt.negate_negate z

theorem spec_closes_four : Closes GInt.rot 4 := fun z => GInt.rot_complete z

theorem closes_rot_to_negate (n : Nat) (h : Closes GInt.rot n) : Closes GInt.negate n := by
  intro z
  have e : iterStep n GInt.negate z = iterStep n GInt.rot (iterStep n GInt.rot z) :=
    iterStep_compose_self GInt.rot n z
  rw [e, h (iterStep n GInt.rot z), h z]

theorem closes_negate_to_count (n : Nat) (_ : Closes GInt.negate n) :
    Closes (fun w => w) n := count_closes n

/-- info: 'Foam.Lattice.iterStep_compose_self' does not depend on any axioms -/
#guard_msgs in #print axioms iterStep_compose_self

/-- info: 'Foam.Lattice.spec_closes_four' does not depend on any axioms -/
#guard_msgs in #print axioms spec_closes_four

/-- info: 'Foam.Lattice.closes_rot_to_negate' does not depend on any axioms -/
#guard_msgs in #print axioms closes_rot_to_negate

end Foam.Lattice
