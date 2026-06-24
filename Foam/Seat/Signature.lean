import Foam.Seat.Born

namespace Foam


structure Ty14 where
  d076 : Int
  d077 : Int

def Ty14.d130 (z : Ty14) : Int := z.d076 * z.d076 - z.d077 * z.d077

def d147 (w z : Ty14) : Int := w.d076 * z.d076 - w.d077 * z.d077

def d148 (w z : Ty14) : Int := w.d076 * z.d077 - w.d077 * z.d076

structure Ty03 where
  d036 : Int
  d037 : Int

def Ty03.d104 (z : Ty03) : Int := z.d036 * z.d036

def d146 (v : Int) (z : Ty03) : Ty03 := ⟨z.d036, v * z.d036 + z.d037⟩

def d149 (κ : Int) (z : Ty05) : Int := z.d043 * z.d043 - κ * (z.d041 * z.d041)

def d140 (κ : Int) (w z : Ty05) : Int := w.d043 * z.d043 - κ * (w.d041 * z.d041)

def d142 (w z : Ty05) : Int := w.d043 * z.d041 - w.d041 * z.d043

theorem t289 (v : Int) (z : Ty03) :
    (d146 v z).d104 = z.d104 := rfl

theorem t290 (v1 v2 : Int) (z : Ty03) :
    d146 v2 (d146 v1 z) = d146 (v2 + v1) z := by
  show (⟨z.d036, v2 * z.d036 + (v1 * z.d036 + z.d037)⟩ : Ty03) = ⟨z.d036, (v2 + v1) * z.d036 + z.d037⟩
  rw [t007 v2 v1 z.d036, t005 (v2 * z.d036) (v1 * z.d036) z.d037]

theorem t082 (a b : Int) : a * a - b * b = (a - b) * (a + b) := by
  rw [Int.sub_eq_add_neg (a := a * a) (b := b * b), Int.sub_eq_add_neg (a := a) (b := b),
      t007 a (-b) (a + b), t015 a a b, t015 (-b) a b,
      t027 b a, t027 b b, t014 b a,
      t005 (a * a) (a * b) (-(a * b) + -(b * b)),
      ← t005 (a * b) (-(a * b)) (-(b * b)),
      t008 (a * b), t054 (-(b * b))]

theorem t074 (t x u v : Int) :
    (t * u - x * v) - (t * v - x * u) = (t + x) * (u - v) := by
  rw [Int.sub_eq_add_neg (a := t * u) (b := x * v),
      Int.sub_eq_add_neg (a := t * v) (b := x * u),
      Int.sub_eq_add_neg (a := t * u + -(x * v)) (b := t * v + -(x * u)),
      t025 (a := t * v) (b := -(x * u)), Int.neg_neg (x * u),
      Int.sub_eq_add_neg (a := u) (b := v), t015 (t + x) u (-v),
      t007 t x u, t007 t x (-v), t018 t v, t018 x v,
      Foam.t057 (t * u) (-(x * v)) (-(t * v)) (x * u),
      t004 (-(x * v)) (-(t * v))]

theorem t075 (t x u v : Int) :
    (t * u - x * v) + (t * v - x * u) = (t - x) * (u + v) := by
  rw [Int.sub_eq_add_neg (a := t * u) (b := x * v),
      Int.sub_eq_add_neg (a := t * v) (b := x * u),
      Int.sub_eq_add_neg (a := t) (b := x), t007 t (-x) (u + v),
      t015 t u v, t015 (-x) u v, t027 x u, t027 x v,
      Foam.t058 (t * u) (-(x * v)) (t * v) (-(x * u)),
      t004 (-(x * v)) (-(x * u))]

theorem t079 (t x u v : Int) :
    (t * u - x * v) * (t * u - x * v) - (t * v - x * u) * (t * v - x * u)
      = (t * t - x * x) * (u * u - v * v) := by
  rw [t082 (t * u - x * v) (t * v - x * u), t074 t x u v, t075 t x u v,
      Foam.t060 (t + x) (t - x) (u - v) (u + v),
      t014 (t + x) (t - x), ← t082 t x, ← t082 u v]

theorem t299 (w z : Ty14) :
    d147 w z * d147 w z - d148 w z * d148 w z = Foam.Ty14.d130 w * Foam.Ty14.d130 z := by
  show (w.d076 * z.d076 - w.d077 * z.d077) * (w.d076 * z.d076 - w.d077 * z.d077)
        - (w.d076 * z.d077 - w.d077 * z.d076) * (w.d076 * z.d077 - w.d077 * z.d076)
      = (w.d076 * w.d076 - w.d077 * w.d077) * (z.d076 * z.d076 - z.d077 * z.d077)
  exact t079 w.d076 w.d077 z.d076 z.d077

theorem t300 :
    d147 ⟨2, 1⟩ ⟨3, 1⟩ * d147 ⟨2, 1⟩ ⟨3, 1⟩
        - d148 ⟨2, 1⟩ ⟨3, 1⟩ * d148 ⟨2, 1⟩ ⟨3, 1⟩
      = Foam.Ty14.d130 ⟨2, 1⟩ * Foam.Ty14.d130 ⟨3, 1⟩ := by decide

theorem t256 (κ a : Int) : d140 κ ⟨a, 0⟩ ⟨1, 0⟩ = a := by
  show a * 1 - κ * (0 * 0) = a
  rw [t020, t022, t022, t052]

theorem t274 (a : Int) : d142 ⟨a, 0⟩ ⟨1, 0⟩ = 0 := by
  show a * 0 - 0 * 1 = 0
  rw [t022, t055, t052]

theorem t303 (κ a : Int) : d149 κ ⟨a, 0⟩ = a * a := by
  show a * a - κ * (0 * 0) = a * a
  rw [t022, t022, t052]

theorem t304 (κ : Int) : d149 κ ⟨1, 0⟩ = 1 := by
  show 1 * 1 - κ * (0 * 0) = 1
  rw [t037, t022, t022, t052]

theorem t284 (κ : Int) (f : Int → Int)
    (h : ∀ w z : Ty05, f (d140 κ w z) - κ * f (d142 w z) = d149 κ w * d149 κ z) :
    ∀ a : Int, f a = a * a + κ * f 0 := by
  intro a
  have ha := h ⟨a, 0⟩ ⟨1, 0⟩
  rw [t256 κ a, t274 a, t303 κ a, t304 κ,
      t014 (a * a) 1, t037] at ha
  rw [← t048 (a := f a) (b := κ * f 0), ha]

theorem t331 (κ : Int) (f : Int → Int)
    (h : ∀ w z : Ty05, f (d140 κ w z) - κ * f (d142 w z) = d149 κ w * d149 κ z) :
    (1 - κ) * f 0 = 0 := by
  have hf0 := t284 κ f h 0
  rw [t055, t054] at hf0
  show (1 - κ) * f 0 = 0
  rw [Int.sub_eq_add_neg (a := 1) (b := κ), t007 1 (-κ) (f 0), t037,
      t027 κ (f 0), ← hf0, t008]

theorem t305 : ∃ z : Ty05, d149 (-1) z ≠ d149 1 z := ⟨⟨1, 1⟩, by decide⟩

/-- info: 'Foam.t289' does not depend on any axioms -/
#guard_msgs in #print axioms t289

/-- info: 'Foam.t290' does not depend on any axioms -/
#guard_msgs in #print axioms t290

/-- info: 'Foam.t079' does not depend on any axioms -/
#guard_msgs in #print axioms t079

/-- info: 'Foam.t299' does not depend on any axioms -/
#guard_msgs in #print axioms t299

/-- info: 'Foam.t300' does not depend on any axioms -/
#guard_msgs in #print axioms t300

/-- info: 'Foam.t284' does not depend on any axioms -/
#guard_msgs in #print axioms t284

/-- info: 'Foam.t331' does not depend on any axioms -/
#guard_msgs in #print axioms t331

/-- info: 'Foam.t305' does not depend on any axioms -/
#guard_msgs in #print axioms t305

end Foam
