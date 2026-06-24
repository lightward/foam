import Foam.Seat.Dial
import Foam.Seat.Doubling
import Foam.Seat.Born

namespace Foam


def d032 : Ty12 → Ty05
  | _ => ⟨1, 0⟩

def d031 : Ty12 → Ty05
  | Foam.Ty12.c1 => ⟨1, 0⟩
  | Foam.Ty12.c2 => ⟨-1, 0⟩
  | Foam.Ty12.c3 => ⟨1, 0⟩
  | Foam.Ty12.c4 => ⟨-1, 0⟩

def d103 : Ty12 → Ty05 := Foam.Ty12.d063

def d162 : Ty12 → Ty05 := fun a => Foam.Ty05.d110 (Foam.Ty12.d063 a)

theorem t203 (a b : Ty12) :
    Foam.d032 (a * b) = Foam.Ty05.d112 (Foam.d032 a) (Foam.d032 b) := by
  cases a <;> cases b <;> decide

theorem t199 (a b : Ty12) :
    Foam.d031 (a * b) = Foam.Ty05.d112 (Foam.d031 a) (Foam.d031 b) := by
  cases a <;> cases b <;> decide

theorem t201 (a b : Ty12) :
    Foam.d103 (a * b) = Foam.Ty05.d112 (Foam.d103 a) (Foam.d103 b) := by
  cases a <;> cases b <;> decide

theorem t338 (a b : Ty12) :
    Foam.d162 (a * b) = Foam.Ty05.d112 (Foam.d162 a) (Foam.d162 b) := by
  cases a <;> cases b <;> decide

theorem t204 (a : Ty12) : (Foam.d032 a).d114 = 1 := by
  cases a <;> decide

theorem t200 (a : Ty12) : (Foam.d031 a).d114 = 1 := by
  cases a <;> decide

theorem t202 (a : Ty12) : (Foam.d103 a).d114 = 1 := by
  cases a <;> decide

theorem t340 (a : Ty12) : (Foam.d162 a).d114 = 1 := by
  cases a <;> decide

def d164 (f g : Ty12 → Ty05) : Ty05 :=
  Foam.Ty05.d108
    (Foam.Ty05.d108 (Foam.Ty05.d112 (f Foam.Ty12.c1) (Foam.Ty05.d110 (g Foam.Ty12.c1))) (Foam.Ty05.d112 (f Foam.Ty12.c2) (Foam.Ty05.d110 (g Foam.Ty12.c2))))
    (Foam.Ty05.d108 (Foam.Ty05.d112 (f Foam.Ty12.c3) (Foam.Ty05.d110 (g Foam.Ty12.c3))) (Foam.Ty05.d112 (f Foam.Ty12.c4) (Foam.Ty05.d110 (g Foam.Ty12.c4))))

theorem t347 : Foam.d164 Foam.d032 Foam.d032 = ⟨4, 0⟩ := by decide
theorem t337 : Foam.d164 Foam.d031 Foam.d031 = ⟨4, 0⟩ := by decide
theorem t343 : Foam.d164 Foam.d103 Foam.d103 = ⟨4, 0⟩ := by decide
theorem t339 : Foam.d164 Foam.d162 Foam.d162 = ⟨4, 0⟩ := by decide

theorem t344 : Foam.d164 Foam.d032 Foam.d031 = Foam.Ty05.d044 := by decide
theorem t346 : Foam.d164 Foam.d032 Foam.d103 = Foam.Ty05.d044 := by decide
theorem t345 : Foam.d164 Foam.d032 Foam.d162 = Foam.Ty05.d044 := by decide
theorem t336 : Foam.d164 Foam.d031 Foam.d103 = Foam.Ty05.d044 := by decide
theorem t335 : Foam.d164 Foam.d031 Foam.d162 = Foam.Ty05.d044 := by decide
theorem t341 : Foam.d164 Foam.d103 Foam.d162 = Foam.Ty05.d044 := by decide

theorem t342 : Foam.d103 ≠ Foam.d162 := by
  intro h
  have : Foam.d103 Foam.Ty12.c2 = Foam.d162 Foam.Ty12.c2 := by rw [h]
  exact absurd this (by decide)

theorem t136 : Foam.d031 ≠ Foam.d032 := by
  intro h
  have : Foam.d031 Foam.Ty12.c2 = Foam.d032 Foam.Ty12.c2 := by rw [h]
  exact absurd this (by decide)

def d163 (n0 n1 n2 n3 : Int) (f : Ty12 → Ty05) : Ty05 :=
  Foam.Ty05.d108
    (Foam.Ty05.d108 (Foam.Ty05.d112 ⟨n0, 0⟩ (f Foam.Ty12.c1)) (Foam.Ty05.d112 ⟨n1, 0⟩ (f Foam.Ty12.c2)))
    (Foam.Ty05.d108 (Foam.Ty05.d112 ⟨n2, 0⟩ (f Foam.Ty12.c3)) (Foam.Ty05.d112 ⟨n3, 0⟩ (f Foam.Ty12.c4)))

def d202 (n0 n1 n2 n3 : Int) : Int := (Foam.d163 n0 n1 n2 n3 Foam.d032).d043
def d201 (n0 n1 n2 n3 : Int) : Int := (Foam.d163 n0 n1 n2 n3 Foam.d031).d043
def d204 (n0 n1 n2 n3 : Int) : Int := (Foam.d163 n0 n1 n2 n3 Foam.d103).d043
def d203 (n0 n1 n2 n3 : Int) : Int := (Foam.d163 n0 n1 n2 n3 Foam.d103).d041

theorem Ty05.t209 (n : Int) (w : Ty05) :
    Foam.Ty05.d112 ⟨n, 0⟩ w = ⟨n * w.d043, n * w.d041⟩ := by
  show (Foam.Ty05.mk (n * w.d043 - 0 * w.d041) (n * w.d041 + 0 * w.d043)) = ⟨n * w.d043, n * w.d041⟩
  rw [t055, t052, t055, Int.add_zero]

theorem t349 (n0 n1 n2 n3 : Int) (f : Ty12 → Ty05) :
    (Foam.d163 n0 n1 n2 n3 f).d043
      = (n0 * (f Foam.Ty12.c1).d043 + n1 * (f Foam.Ty12.c2).d043) + (n2 * (f Foam.Ty12.c3).d043 + n3 * (f Foam.Ty12.c4).d043) := by
  show ((Foam.Ty05.d112 ⟨n0,0⟩ (f Foam.Ty12.c1)).d043 + (Foam.Ty05.d112 ⟨n1,0⟩ (f Foam.Ty12.c2)).d043
       + ((Foam.Ty05.d112 ⟨n2,0⟩ (f Foam.Ty12.c3)).d043 + (Foam.Ty05.d112 ⟨n3,0⟩ (f Foam.Ty12.c4)).d043))
     = (n0 * (f Foam.Ty12.c1).d043 + n1 * (f Foam.Ty12.c2).d043) + (n2 * (f Foam.Ty12.c3).d043 + n3 * (f Foam.Ty12.c4).d043)
  rw [Foam.Ty05.t209, Foam.Ty05.t209, Foam.Ty05.t209, Foam.Ty05.t209]

theorem t348 (n0 n1 n2 n3 : Int) (f : Ty12 → Ty05) :
    (Foam.d163 n0 n1 n2 n3 f).d041
      = (n0 * (f Foam.Ty12.c1).d041 + n1 * (f Foam.Ty12.c2).d041) + (n2 * (f Foam.Ty12.c3).d041 + n3 * (f Foam.Ty12.c4).d041) := by
  show ((Foam.Ty05.d112 ⟨n0,0⟩ (f Foam.Ty12.c1)).d041 + (Foam.Ty05.d112 ⟨n1,0⟩ (f Foam.Ty12.c2)).d041
       + ((Foam.Ty05.d112 ⟨n2,0⟩ (f Foam.Ty12.c3)).d041 + (Foam.Ty05.d112 ⟨n3,0⟩ (f Foam.Ty12.c4)).d041))
     = (n0 * (f Foam.Ty12.c1).d041 + n1 * (f Foam.Ty12.c2).d041) + (n2 * (f Foam.Ty12.c3).d041 + n3 * (f Foam.Ty12.c4).d041)
  rw [Foam.Ty05.t209, Foam.Ty05.t209, Foam.Ty05.t209, Foam.Ty05.t209]

theorem t419 (n0 n1 n2 n3 : Int) :
    Foam.d202 n0 n1 n2 n3 = n0 + n1 + n2 + n3 := by
  show (Foam.d163 n0 n1 n2 n3 Foam.d032).d043 = n0 + n1 + n2 + n3
  rw [Foam.t349 n0 n1 n2 n3 Foam.d032]
  show (n0 * 1 + n1 * 1) + (n2 * 1 + n3 * 1) = n0 + n1 + n2 + n3
  rw [t020, t020, t020, t020, ← t005 (n0 + n1) n2 n3]

theorem t418 (n0 n1 n2 n3 : Int) :
    Foam.d201 n0 n1 n2 n3 = n0 + -n1 + n2 + -n3 := by
  show (Foam.d163 n0 n1 n2 n3 Foam.d031).d043 = n0 + -n1 + n2 + -n3
  rw [Foam.t349 n0 n1 n2 n3 Foam.d031]
  show (n0 * 1 + n1 * (-1)) + (n2 * 1 + n3 * (-1)) = n0 + -n1 + n2 + -n3
  rw [t020, t020, t019, t019, ← t005 (n0 + -n1) n2 (-n3)]

theorem t421 (n0 n1 n2 n3 : Int) :
    Foam.d204 n0 n1 n2 n3 = n0 + -n2 := by
  show (Foam.d163 n0 n1 n2 n3 Foam.d103).d043 = n0 + -n2
  rw [Foam.t349 n0 n1 n2 n3 Foam.d103]
  show (n0 * 1 + n1 * 0) + (n2 * (-1) + n3 * 0) = n0 + -n2
  rw [t020, t022, t019, t022, Int.add_zero, Int.add_zero]

theorem t420 (n0 n1 n2 n3 : Int) :
    Foam.d203 n0 n1 n2 n3 = n1 + -n3 := by
  show (Foam.d163 n0 n1 n2 n3 Foam.d103).d041 = n1 + -n3
  rw [Foam.t348 n0 n1 n2 n3 Foam.d103]
  show (n0 * 0 + n1 * 1) + (n2 * 0 + n3 * (-1)) = n1 + -n3
  rw [t020, t022, t019, t022, t054, t054]

def d001 (a : Int) : Int := a + a

theorem t002 (a b c d : Int) : a + b + c + d = (a + c) + (b + d) := by
  rw [t005 (a + b) c d, t005 a b (c + d),
    ← t005 b c d, t004 b c, t005 c b d,
    ← t005 a c (b + d)]

theorem t003 (a b c d : Int) : a + -b + c + -d = (a + c) + -(b + d) := by
  rw [Foam.t002 a (-b) c (-d), ← t025]

theorem t090 (x y : Int) : (x + y) + (x + -y) = Foam.d001 x := by
  rw [← t005 (x + y) x (-y), Foam.t002 x y x (-y),
    t008 y, Int.add_zero]
  rfl

theorem t089 (x y : Int) : (x + y) + -(x + -y) = Foam.d001 y := by
  rw [t025, Int.neg_neg y, ← t005 (x + y) (-x) y,
    Foam.t002 x y (-x) y, t008 x, t054]
  rfl

theorem t091 (a b : Int) : Foam.d001 (a + b) = Foam.d001 a + Foam.d001 b := by
  show (a + b) + (a + b) = (a + a) + (b + b)
  rw [← t005 (a + b) a b, Foam.t002 a b a b]

theorem t092 (a b : Int) : Foam.d001 (a + -b) = Foam.d001 a + -Foam.d001 b := by
  show (a + -b) + (a + -b) = (a + a) + -(b + b)
  rw [← t005 (a + -b) a (-b), Foam.t002 a (-b) a (-b), t025]

theorem t412 (n0 n1 n2 n3 : Int) :
    Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3 = Foam.d001 (n0 + n2) := by
  rw [Foam.t419, Foam.t418, Foam.t002 n0 n1 n2 n3,
    Foam.t003 n0 n1 n2 n3, Foam.t090 (n0 + n2) (n1 + n3)]

theorem t414 (n0 n1 n2 n3 : Int) :
    Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3 = Foam.d001 (n1 + n3) := by
  rw [Foam.t419, Foam.t418, Foam.t002 n0 n1 n2 n3,
    Foam.t003 n0 n1 n2 n3, Foam.t089 (n0 + n2) (n1 + n3)]

theorem t422 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3)
      + Foam.d001 (Foam.d204 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n0) := by
  rw [Foam.t412, Foam.t421, ← Foam.t091 (n0 + n2) (n0 + -n2),
    Foam.t090 n0 n2]

theorem t424 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3)
      + -Foam.d001 (Foam.d204 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n2) := by
  rw [Foam.t412, Foam.t421, ← Foam.t092 (n0 + n2) (n0 + -n2),
    Foam.t089 n0 n2]

theorem t423 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3)
      + Foam.d001 (Foam.d203 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n1) := by
  rw [Foam.t414, Foam.t420, ← Foam.t091 (n1 + n3) (n1 + -n3),
    Foam.t090 n1 n3]

theorem t425 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3)
      + -Foam.d001 (Foam.d203 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n3) := by
  rw [Foam.t414, Foam.t420, ← Foam.t092 (n1 + n3) (n1 + -n3),
    Foam.t089 n1 n3]

theorem t416 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3)
        + Foam.d001 (Foam.d204 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n0) ∧
    (Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3)
        + Foam.d001 (Foam.d203 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n1) ∧
    (Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3)
        + -Foam.d001 (Foam.d204 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n2) ∧
    (Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3)
        + -Foam.d001 (Foam.d203 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n3) :=
  ⟨Foam.t422 n0 n1 n2 n3, Foam.t423 n0 n1 n2 n3,
    Foam.t424 n0 n1 n2 n3, Foam.t425 n0 n1 n2 n3⟩

theorem t413 :
    Foam.d204 1 1 1 1 = Foam.d204 0 0 0 0 ∧
    Foam.d203 1 1 1 1 = Foam.d203 0 0 0 0 ∧
    Foam.d201 1 1 1 1 = Foam.d201 0 0 0 0 ∧
    Foam.d202 1 1 1 1 ≠ Foam.d202 0 0 0 0 := by decide

theorem t417 :
    Foam.d202 1 0 0 0 = Foam.d202 0 0 1 0 ∧
    Foam.d203 1 0 0 0 = Foam.d203 0 0 1 0 ∧
    Foam.d201 1 0 0 0 = Foam.d201 0 0 1 0 ∧
    Foam.d204 1 0 0 0 ≠ Foam.d204 0 0 1 0 := by decide

theorem t415 :
    Foam.d202 0 1 0 0 = Foam.d202 0 0 0 1 ∧
    Foam.d204 0 1 0 0 = Foam.d204 0 0 0 1 ∧
    Foam.d201 0 1 0 0 = Foam.d201 0 0 0 1 ∧
    Foam.d203 0 1 0 0 ≠ Foam.d203 0 0 0 1 := by decide

theorem t411 :
    Foam.d202 1 0 1 0 = Foam.d202 0 1 0 1 ∧
    Foam.d204 1 0 1 0 = Foam.d204 0 1 0 1 ∧
    Foam.d203 1 0 1 0 = Foam.d203 0 1 0 1 ∧
    Foam.d201 1 0 1 0 ≠ Foam.d201 0 1 0 1 := by decide

/-- info: 'Foam.t203' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t203

/-- info: 'Foam.t199' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t199

/-- info: 'Foam.t201' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t201

/-- info: 'Foam.t338' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t338

/-- info: 'Foam.t204' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t204

/-- info: 'Foam.t200' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t200

/-- info: 'Foam.t202' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t202

/-- info: 'Foam.t340' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t340

/-- info: 'Foam.t347' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t347

/-- info: 'Foam.t337' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t337

/-- info: 'Foam.t343' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t343

/-- info: 'Foam.t339' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t339

/-- info: 'Foam.t344' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t344

/-- info: 'Foam.t346' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t346

/-- info: 'Foam.t345' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t345

/-- info: 'Foam.t336' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t336

/-- info: 'Foam.t335' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t335

/-- info: 'Foam.t341' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t341

/-- info: 'Foam.t342' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t342

/-- info: 'Foam.t136' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t136

/-- info: 'Foam.Ty05.t209' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t209

/-- info: 'Foam.t349' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t349

/-- info: 'Foam.t348' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t348

/-- info: 'Foam.t419' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t419

/-- info: 'Foam.t418' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t418

/-- info: 'Foam.t421' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t421

/-- info: 'Foam.t420' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t420

/-- info: 'Foam.t002' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t002

/-- info: 'Foam.t003' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t003

/-- info: 'Foam.t090' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t090

/-- info: 'Foam.t089' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t089

/-- info: 'Foam.t091' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t091

/-- info: 'Foam.t092' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t092

/-- info: 'Foam.t412' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t412

/-- info: 'Foam.t414' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t414

/-- info: 'Foam.t422' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t422

/-- info: 'Foam.t423' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t423

/-- info: 'Foam.t424' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t424

/-- info: 'Foam.t425' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t425

/-- info: 'Foam.t416' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t416

/-- info: 'Foam.t413' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t413

/-- info: 'Foam.t417' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t417

/-- info: 'Foam.t415' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t415

/-- info: 'Foam.t411' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t411

end Foam