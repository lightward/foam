import Foam.Platonism.Tower

namespace Foam

abbrev Ty21 := Ty08 3

structure Ty04 where
  d105 : Ty21
  d106 : Ty21

def d194 : Ty01 Ty04 where
  Ty20 := Bool
  Ty19   := Ty21
  d102   := fun f p => bif p then f.d106 else f.d105

def d198 (x : Ty21) (f : Ty04) : Ty04 := { f with d105 := x }
def d199 (y : Ty21) (f : Ty04) : Ty04 := { f with d106 := y }

def d023 : Bool := false
def d024 : Bool := true

def t205 (op : Ty04 → Ty04) (b : Ty01 Ty04) : Prop :=
  ∃ f p, b.d102 (op f) p ≠ b.d102 f p

def t359 (write : Ty21 → Ty04 → Ty04) (p : Bool) : Prop :=
  ∃ dec : Ty21 → Ty21, ∀ x f, dec (d194.d102 (write x f) p) = x

def d144 : Ty21 := (Foam.Ty08.d052 2, (0 : Int))
def d145 : Ty21 := (Foam.Ty08.d052 2, (1 : Int))

theorem t282 : d145 ≠ d144 := fun h => absurd (congrArg Prod.snd h) (by decide)

theorem t381 :
    t205 (d198 d145) d194 ∧ t205 (d199 d145) d194 :=
  ⟨⟨⟨d144, d144⟩, d023, fun h => t282 h⟩,
   ⟨⟨d144, d144⟩, d024, fun h => t282 h⟩⟩

theorem t474 : t359 d198 d023 ∧ t359 d199 d024 :=
  ⟨⟨id, fun _ _ => rfl⟩, ⟨id, fun _ _ => rfl⟩⟩

theorem t408 (x : Ty21) (f : Ty04) : (d198 x f).d106 = f.d106 := rfl
theorem t409 (y : Ty21) (f : Ty04) : (d199 y f).d105 = f.d105 := rfl

theorem t389 (x y : Ty21) (f : Ty04) :
    d198 x (d199 y f) = d199 y (d198 x f) := rfl

theorem t399 :
    d194.d155.d157.t198 d194 ∧ d194.t198 d194.d155.d157 :=
  t374 d194

theorem t475 (n : Nat) :
    (d194.d200 n).t198 d194 ∧ d194.t198 (d194.d200 n) :=
  t453 d194 n

theorem t445 :
    (t205 (d198 d145) d194 ∧ t205 (d199 d145) d194)
      ∧ (t359 d198 d023 ∧ t359 d199 d024)
      ∧ (∀ x y f, d198 x (d199 y f) = d199 y (d198 x f))
      ∧ (∀ n, (d194.d200 n).t198 d194 ∧ d194.t198 (d194.d200 n)) :=
  ⟨t381, t474, t389, t475⟩

/-- info: 'Foam.t282' does not depend on any axioms -/
#guard_msgs in #print axioms t282

/-- info: 'Foam.t381' does not depend on any axioms -/
#guard_msgs in #print axioms t381

/-- info: 'Foam.t474' does not depend on any axioms -/
#guard_msgs in #print axioms t474

/-- info: 'Foam.t389' does not depend on any axioms -/
#guard_msgs in #print axioms t389

/-- info: 'Foam.t399' does not depend on any axioms -/
#guard_msgs in #print axioms t399

/-- info: 'Foam.t475' does not depend on any axioms -/
#guard_msgs in #print axioms t475

/-- info: 'Foam.t445' does not depend on any axioms -/
#guard_msgs in #print axioms t445

end Foam
