import Foam.Engine.Spectrum
import Foam.Seat.Closure
import Foam.Seat.Doubling
import Foam.Int

namespace Foam

variable {S : Type}

def rotPow : Nat → GInt → GInt
  | 0,     z => z
  | n + 1, z => GInt.rot (rotPow n z)

def specR [DecidableEq S] : List S → S → GInt
  | [],     _ => GInt.zero
  | x :: l, s => (rotPow l.length (if x = s then GInt.one else GInt.zero)).add (specR l s)

theorem rot_add (a b : GInt) : (a.add b).rot = a.rot.add b.rot := by
  cases a with
  | mk a1 a2 =>
    cases b with
    | mk b1 b2 =>
      show (⟨-(a2 + b2), a1 + b1⟩ : GInt) = ⟨-a2 + -b2, a1 + b1⟩
      rw [FInt.neg_add]

theorem conj_add (a b : GInt) : (a.add b).conj = a.conj.add b.conj := by
  cases a with
  | mk a1 a2 =>
    cases b with
    | mk b1 b2 =>
      show (⟨a1 + b1, -(a2 + b2)⟩ : GInt) = ⟨a1 + b1, -a2 + -b2⟩
      rw [FInt.neg_add]

theorem conj_rot (z : GInt) : (z.rot).conj = rotPow 3 z.conj := by
  cases z with
  | mk a b =>
    show (⟨-b, -a⟩ : GInt) = ⟨- - -b, -a⟩
    rw [Int.neg_neg]

theorem rotPow_add (n : Nat) (a b : GInt) :
    rotPow n (a.add b) = (rotPow n a).add (rotPow n b) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show GInt.rot (rotPow m (a.add b)) = (GInt.rot (rotPow m a)).add (GInt.rot (rotPow m b))
    rw [ih, rot_add]

theorem rotPow_compose (m n : Nat) (z : GInt) :
    rotPow m (rotPow n z) = rotPow (m + n) z := by
  induction m with
  | zero =>
    show rotPow n z = rotPow (0 + n) z
    rw [Nat.zero_add]
  | succ k ih =>
    show GInt.rot (rotPow k (rotPow n z)) = rotPow (Nat.succ k + n) z
    rw [ih, Nat.succ_add]
    rfl

theorem rotPow_four (z : GInt) : rotPow 4 z = z := by
  show z.rot.rot.rot.rot = z
  exact GInt.rot_complete z

theorem rotPow_add_four (k : Nat) (z : GInt) : rotPow (k + 4) z = rotPow k z := by
  rw [← rotPow_compose k 4 z, rotPow_four]

theorem conj_mark (c : Prop) [inst : Decidable c] :
    (if c then GInt.one else GInt.zero).conj = (if c then GInt.one else GInt.zero) := by
  cases inst with
  | isTrue _ => rfl
  | isFalse _ => rfl

theorem specR_bridge [DecidableEq S] : ∀ (l : List S) (s : S),
    GInt.rot (specR l s) = rotPow l.length (GInt.conj (spec l s)) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x l ih =>
    intro s
    have key : ∀ (W : GInt), rotPow (l.length + 1) (rotPow 3 W) = rotPow l.length W := by
      intro W
      rw [rotPow_compose]
      exact rotPow_add_four l.length W
    show GInt.rot ((rotPow l.length (if x = s then GInt.one else GInt.zero)).add (specR l s))
       = rotPow (l.length + 1) (GInt.conj (spec (x :: l) s))
    rw [rot_add, ih, spec_shift, conj_add, conj_mark, conj_rot, rotPow_add, key]
    rfl

/-- info: 'Foam.conj_rot' does not depend on any axioms -/
#guard_msgs in #print axioms conj_rot

/-- info: 'Foam.rotPow_four' does not depend on any axioms -/
#guard_msgs in #print axioms rotPow_four

/-- info: 'Foam.specR_bridge' does not depend on any axioms -/
#guard_msgs in #print axioms specR_bridge

end Foam
