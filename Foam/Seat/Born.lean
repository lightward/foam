import Foam.Int
import Foam.Seat.Dial

namespace Foam


theorem t058 (p q r s : Int) : (p + q) + (r + s) = (p + r) + (q + s) := by
  rw [t005 p q (r + s), ← t005 q r s, t004 q r,
      t005 r q s, ← t005 p r (q + s)]

theorem t057 (p q r s : Int) : (p + q) + (r + s) = (p + s) + (q + r) := by
  rw [t005 p q (r + s), t004 r s, ← t005 q s r,
      t004 q s, t005 s q r, ← t005 p s (q + r)]

theorem t065 (x : Int) : 2 * x = x + x := by
  rw [show (2 : Int) = 1 + 1 from rfl, t007, t037]

theorem t060 (a b c d : Int) : (a * c) * (b * d) = (a * b) * (c * d) := by
  rw [t016 a c (b * d), ← t016 c b d, t014 c b,
      t016 b c d, ← t016 a b (c * d)]

theorem t064 (a c : Int) : (a * c) * (a * c) = (a * a) * (c * c) :=
  Foam.t060 a a c c

theorem t061 (a b : Int) : (-a) * (-b) = a * b := by
  rw [t027, t018, Int.neg_neg]

theorem t063 (W K Z M N : Int) :
    ((W + K) + (K + Z)) + ((M + (-K)) + ((-K) + N)) = (W + M) + (N + Z) := by
  rw [Foam.t057 W K K Z, Foam.t057 M (-K) (-K) N,
      Foam.t058 (W + Z) (K + K) (M + N) ((-K) + (-K)),
      Foam.t057 K K (-K) (-K), t008 K, Int.add_zero, Int.add_zero,
      Foam.t058 W Z M N, t004 Z N]

theorem t059 (a b c d : Int) :
    (a * c + b * d) * (a * c + b * d)
      + (-(b * c) + a * d) * (-(b * c) + a * d)
    = (a * a + b * b) * (c * c + d * d) := by
  rw [t015 (a * c + b * d) (a * c) (b * d),
      t007 (a * c) (b * d) (a * c), t007 (a * c) (b * d) (b * d)]
  rw [t015 (-(b * c) + a * d) (-(b * c)) (a * d),
      t007 (-(b * c)) (a * d) (-(b * c)), t007 (-(b * c)) (a * d) (a * d)]
  rw [t015 (a * a + b * b) (c * c) (d * d),
      t007 (a * a) (b * b) (c * c), t007 (a * a) (b * b) (d * d)]
  rw [Foam.t064 a c, Foam.t064 b d]
  rw [Foam.t061 (b * c) (b * c), Foam.t064 b c, Foam.t064 a d]
  rw [t018 (a * d) (b * c), t027 (b * c) (a * d)]
  rw [t014 (b * d) (a * c), Foam.t060 a b c d]
  rw [Foam.t060 a b d c, t014 d c]
  rw [t014 (b * c) (a * d), Foam.t060 a b d c, t014 d c]
  exact Foam.t063 (a * a * (c * c)) (a * b * (c * d)) (b * b * (d * d))
        (b * b * (c * c)) (a * a * (d * d))

def Ty05.d113 (z : Ty05) : Ty05 := ⟨-z.d043, -z.d041⟩
def Ty05.d115 (z : Ty05) : Ty05 := ⟨-z.d041, z.d043⟩
def Ty05.d109 (w z : Ty05) : Int := w.d043 * z.d043 + w.d041 * z.d041
def Ty05.d165 (w z : Ty05) : Int := Foam.Ty05.d109 w z * Foam.Ty05.d109 w z

theorem Ty05.t351 (w z : Ty05) : ∃ k : Nat, Foam.Ty05.d165 w z = Int.ofNat k :=
  Foam.Ty05.t056 (Foam.Ty05.d109 w z)

theorem Ty05.t216 (z : Ty05) : Foam.Ty05.d115 (Foam.Ty05.d115 z) = Foam.Ty05.d113 z := rfl

theorem Ty05.t207 (w z : Ty05) : Foam.Ty05.d109 w (Foam.Ty05.d113 z) = -(Foam.Ty05.d109 w z) := by
  show w.d043 * (-z.d043) + w.d041 * (-z.d041) = -(w.d043 * z.d043 + w.d041 * z.d041)
  rw [t018, t018, ← t025]

theorem Ty05.t206 (θ a b : Ty05) :
    Foam.Ty05.d109 θ (Foam.Ty05.d108 a b) = Foam.Ty05.d109 θ a + Foam.Ty05.d109 θ b := by
  show θ.d043 * (a.d043 + b.d043) + θ.d041 * (a.d041 + b.d041)
     = (θ.d043 * a.d043 + θ.d041 * a.d041) + (θ.d043 * b.d043 + θ.d041 * b.d041)
  rw [t015, t015]
  exact Foam.t058 (θ.d043 * a.d043) (θ.d043 * b.d043) (θ.d041 * a.d041) (θ.d041 * b.d041)

theorem Ty05.t208 (θ z : Ty05) :
    Foam.Ty05.d109 θ z + Foam.Ty05.d109 θ (Foam.Ty05.d115 z)
      + Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 z))
      + Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 z))) = 0 := by
  have e3 : Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 z)) = -(Foam.Ty05.d109 θ z) := by
    rw [Foam.Ty05.t216, Foam.Ty05.t207]
  have e4 : Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 z))) = -(Foam.Ty05.d109 θ (Foam.Ty05.d115 z)) := by
    rw [Foam.Ty05.t216 (Foam.Ty05.d115 z), Foam.Ty05.t207]
  rw [e3, e4,
      t005 (Foam.Ty05.d109 θ z + Foam.Ty05.d109 θ (Foam.Ty05.d115 z))
        (-(Foam.Ty05.d109 θ z)) (-(Foam.Ty05.d109 θ (Foam.Ty05.d115 z))),
      Foam.t058 (Foam.Ty05.d109 θ z) (Foam.Ty05.d109 θ (Foam.Ty05.d115 z))
        (-(Foam.Ty05.d109 θ z)) (-(Foam.Ty05.d109 θ (Foam.Ty05.d115 z))),
      t008, t008, Int.add_zero]

theorem Ty05.t353 (θ a b : Ty05) :
    Foam.Ty05.d165 θ (Foam.Ty05.d108 a b)
      = Foam.Ty05.d165 θ a + Foam.Ty05.d165 θ b + 2 * (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ b) := by
  show Foam.Ty05.d109 θ (Foam.Ty05.d108 a b) * Foam.Ty05.d109 θ (Foam.Ty05.d108 a b)
     = Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ a + Foam.Ty05.d109 θ b * Foam.Ty05.d109 θ b
       + 2 * (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ b)
  rw [Foam.Ty05.t206 θ a b, Foam.t065 (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ b),
      t007 (Foam.Ty05.d109 θ a) (Foam.Ty05.d109 θ b) (Foam.Ty05.d109 θ a + Foam.Ty05.d109 θ b),
      t015 (Foam.Ty05.d109 θ a) (Foam.Ty05.d109 θ a) (Foam.Ty05.d109 θ b),
      t015 (Foam.Ty05.d109 θ b) (Foam.Ty05.d109 θ a) (Foam.Ty05.d109 θ b),
      t014 (Foam.Ty05.d109 θ b) (Foam.Ty05.d109 θ a)]
  exact Foam.t057 (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ a) (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ b)
        (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ b) (Foam.Ty05.d109 θ b * Foam.Ty05.d109 θ b)

theorem Ty05.t352 (θ z : Ty05) :
    Foam.Ty05.d165 θ z + Foam.Ty05.d165 (Foam.Ty05.d115 θ) z = Foam.Ty05.d114 θ * Foam.Ty05.d114 z := by
  show (θ.d043 * z.d043 + θ.d041 * z.d041) * (θ.d043 * z.d043 + θ.d041 * z.d041)
     + ((-θ.d041) * z.d043 + θ.d043 * z.d041) * ((-θ.d041) * z.d043 + θ.d043 * z.d041)
     = (θ.d043 * θ.d043 + θ.d041 * θ.d041) * (z.d043 * z.d043 + z.d041 * z.d041)
  rw [t027 θ.d041 z.d043]
  exact Foam.t059 θ.d043 θ.d041 z.d043 z.d041

/-- info: 'Foam.Ty05.t351' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t351

/-- info: 'Foam.Ty05.t216' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t216

/-- info: 'Foam.Ty05.t208' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t208

/-- info: 'Foam.Ty05.t353' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t353

/-- info: 'Foam.Ty05.t352' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t352

end Foam
