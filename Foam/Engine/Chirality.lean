import Foam.Engine.Spectrum
import Foam.Seat.Closure
import Foam.Seat.Doubling
import Foam.Int

namespace Foam

variable {S : Type}

def d098 : Nat → Ty05 → Ty05
  | 0,     z => z
  | n + 1, z => Foam.Ty05.d115 (d098 n z)

def d100 [DecidableEq S] : List S → S → Ty05
  | [],     _ => Foam.Ty05.d044
  | x :: l, s => (d098 l.length (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044)).d108 (d100 l s)

theorem t318 (a b : Ty05) : (a.d108 b).d115 = a.d115.d108 b.d115 := by
  cases a with
  | mk a1 a2 =>
    cases b with
    | mk b1 b2 =>
      show (⟨-(a2 + b2), a1 + b1⟩ : Ty05) = ⟨-a2 + -b2, a1 + b1⟩
      rw [Foam.t025]

theorem t268 (a b : Ty05) : (a.d108 b).d110 = a.d110.d108 b.d110 := by
  cases a with
  | mk a1 a2 =>
    cases b with
    | mk b1 b2 =>
      show (⟨a1 + b1, -(a2 + b2)⟩ : Ty05) = ⟨a1 + b1, -a2 + -b2⟩
      rw [Foam.t025]

theorem t270 (z : Ty05) : (z.d115).d110 = d098 3 z.d110 := by
  cases z with
  | mk a b =>
    show (⟨-b, -a⟩ : Ty05) = ⟨- - -b, -a⟩
    rw [Int.neg_neg]

theorem t316 (n : Nat) (a b : Ty05) :
    d098 n (a.d108 b) = (d098 n a).d108 (d098 n b) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show Foam.Ty05.d115 (d098 m (a.d108 b)) = (Foam.Ty05.d115 (d098 m a)).d108 (Foam.Ty05.d115 (d098 m b))
    rw [ih, t318]

theorem t186 (m n : Nat) (z : Ty05) :
    d098 m (d098 n z) = d098 (m + n) z := by
  induction m with
  | zero =>
    show d098 n z = d098 (0 + n) z
    rw [Nat.zero_add]
  | succ k ih =>
    show Foam.Ty05.d115 (d098 k (d098 n z)) = d098 (Nat.succ k + n) z
    rw [ih, Nat.succ_add]
    rfl

theorem t187 (z : Ty05) : d098 4 z = z := by
  show z.d115.d115.d115.d115 = z
  exact Foam.Ty05.t214 z

theorem t185 (k : Nat) (z : Ty05) : d098 (k + 4) z = d098 k z := by
  rw [← t186 k 4 z, t187]

theorem t269 (c : Prop) [inst : Decidable c] :
    (if c then Foam.Ty05.d042 else Foam.Ty05.d044).d110 = (if c then Foam.Ty05.d042 else Foam.Ty05.d044) := by
  cases inst with
  | isTrue _ => rfl
  | isFalse _ => rfl

theorem t401 [DecidableEq S] : ∀ (l : List S) (s : S),
    Foam.Ty05.d115 (d100 l s) = d098 l.length (Foam.Ty05.d110 (d197 l s)) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x l ih =>
    intro s
    have key : ∀ (W : Ty05), d098 (l.length + 1) (d098 3 W) = d098 l.length W := by
      intro W
      rw [t186]
      exact t185 l.length W
    show Foam.Ty05.d115 ((d098 l.length (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044)).d108 (d100 l s))
       = d098 (l.length + 1) (Foam.Ty05.d110 (d197 (x :: l) s))
    rw [t318, ih, t403, t268, t269, t270, t316, key]
    rfl

/-- info: 'Foam.t270' does not depend on any axioms -/
#guard_msgs in #print axioms t270

/-- info: 'Foam.t187' does not depend on any axioms -/
#guard_msgs in #print axioms t187

/-- info: 'Foam.t401' does not depend on any axioms -/
#guard_msgs in #print axioms t401

end Foam
