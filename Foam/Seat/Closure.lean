import Foam.Seat.Dial
import Foam.Seat.Born

namespace Foam

def d096 : Nat → (Ty05 → Ty05) → Ty05 → Ty05
  | 0, _, z => z
  | n + 1, f, z => f (d096 n f z)

theorem t177 (f : Ty05 → Ty05) :
    ∀ (n : Nat) (z : Ty05), d096 n f (f z) = f (d096 n f z)
  | 0, _ => rfl
  | n + 1, z => congrArg f (t177 f n z)

theorem t174 (f : Ty05 → Ty05) :
    ∀ (n : Nat) (z : Ty05),
      d096 n (fun w => f (f w)) z = d096 n f (d096 n f z)
  | 0, _ => rfl
  | n + 1, z => by
      show f (f (d096 n (fun w => f (f w)) z))
         = f (d096 n f (f (d096 n f z)))
      rw [t174 f n z, t177 f n (d096 n f z)]

def t137 (step : Ty05 → Ty05) (n : Nat) : Prop := ∀ z, d096 n step z = z

theorem t176 : ∀ (n : Nat) (z : Ty05), d096 n (fun w => w) z = z
  | 0, _ => rfl
  | n + 1, z => t176 n z

theorem t273 (n : Nat) : t137 (fun w => w) n := t176 n

theorem t175 (f g : Ty05 → Ty05) (h : ∀ w, f w = g w) :
    ∀ (n : Nat) (z : Ty05), d096 n f z = d096 n g z
  | 0, _ => rfl
  | n + 1, z => by
      show f (d096 n f z) = g (d096 n g z)
      rw [t175 f g h n z, h (d096 n g z)]

theorem Ty05.t210 (z : Ty05) : Foam.Ty05.d113 (Foam.Ty05.d113 z) = z := by
  cases z with
  | mk a b =>
    show (⟨- -a, - -b⟩ : Ty05) = ⟨a, b⟩
    rw [Int.neg_neg, Int.neg_neg]

theorem Ty05.t214 (z : Ty05) :
    Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 z))) = z := Foam.Ty05.t210 z

theorem t260 : t137 Foam.Ty05.d113 2 := fun z => Foam.Ty05.t210 z

theorem t322 : t137 Foam.Ty05.d115 4 := fun z => Foam.Ty05.t214 z

theorem t266 (n : Nat) (h : t137 Foam.Ty05.d115 n) : t137 Foam.Ty05.d113 n := by
  intro z
  have e : d096 n Foam.Ty05.d113 z = d096 n Foam.Ty05.d115 (d096 n Foam.Ty05.d115 z) := by
    rw [t175 Foam.Ty05.d113 (fun w => Foam.Ty05.d115 (Foam.Ty05.d115 w))
          (fun w => (Foam.Ty05.t216 w).symm) n z]
    exact t174 Foam.Ty05.d115 n z
  rw [e, h (d096 n Foam.Ty05.d115 z), h z]

theorem t265 (n : Nat) (_ : t137 Foam.Ty05.d113 n) :
    t137 (fun w => w) n := t273 n

/-- info: 'Foam.t174' does not depend on any axioms -/
#guard_msgs in #print axioms t174

/-- info: 'Foam.t273' does not depend on any axioms -/
#guard_msgs in #print axioms t273

/-- info: 'Foam.t175' does not depend on any axioms -/
#guard_msgs in #print axioms t175

/-- info: 'Foam.Ty05.t210' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t210

/-- info: 'Foam.Ty05.t214' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t214

/-- info: 'Foam.t260' does not depend on any axioms -/
#guard_msgs in #print axioms t260

/-- info: 'Foam.t322' does not depend on any axioms -/
#guard_msgs in #print axioms t322

/-- info: 'Foam.t266' does not depend on any axioms -/
#guard_msgs in #print axioms t266

/-- info: 'Foam.t265' does not depend on any axioms -/
#guard_msgs in #print axioms t265

end Foam