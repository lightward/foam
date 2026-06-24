import Foam.Platonism

namespace Foam

variable {State : Type}

def Ty08 : Nat → Type
  | 0 => PUnit
  | n + 1 => Ty08 n × Int

def Ty08.d052 : (n : Nat) → Ty08 n
  | 0 => PUnit.unit
  | n + 1 => (Foam.Ty08.d052 n, 0)

def Ty01.d156 (b : Ty01 State) (n : Nat) : Ty01 (State × Ty08 n) where
  Ty20 := b.Ty20
  Ty19 := b.Ty19
  d102 := fun s p => b.d102 s.1 p

def Ty01.d200 (b : Ty01 State) (n : Nat) : Ty01 State where
  Ty20 := (b.d156 n).Ty20
  Ty19 := (b.d156 n).Ty19
  d102 := fun s p => (b.d156 n).d102 (s, Foam.Ty08.d052 n) p

theorem t371 (b : Ty01 State) (n : Nat)
    (s : State × Ty08 n) (p : b.Ty20) :
    (b.d156 n).d102 s p = b.d102 s.1 p := rfl

theorem t370 (b : Ty01 State) (n : Nat)
    (s : State) (l m : Ty08 n) (p : b.Ty20) :
    (b.d156 n).d102 (s, l) p = (b.d156 n).d102 (s, m) p := rfl

theorem t458 (b : Ty01 State) (n : Nat) (s : State) (p : b.Ty20) :
    (b.d200 n).d102 s p = b.d102 s p := rfl

theorem t453 (b : Ty01 State) (n : Nat) :
    (b.d200 n).t198 b ∧ b.t198 (b.d200 n) :=
  ⟨⟨id, id, fun _ _ => rfl⟩, ⟨id, id, fun _ _ => rfl⟩⟩

theorem t452 (b : Ty01 State) (n : Nat) :
    (b.d200 n).t198 (b.d200 n) ∧
      (b.d200 n).t198 b ∧ b.t198 (b.d200 n) :=
  ⟨Foam.Ty01.t332 _, t453 b n⟩

theorem t451 (b : Ty01 State) (m n : Nat) :
    (b.d200 (n + m)).t198 (b.d200 m) ∧
      (b.d200 m).t198 (b.d200 (n + m)) :=
  ⟨⟨id, id, fun _ _ => rfl⟩, ⟨id, id, fun _ _ => rfl⟩⟩

def Ty08.d002 : Nat → Nat := fun n => n

theorem t117 (m n : Nat) :
    Foam.Ty08.d002 (n + m) = Foam.Ty08.d002 n + Foam.Ty08.d002 m := rfl

theorem t135 (n : Nat) :
    ∃ l m : Ty08 n × Int, l ≠ m :=
  ⟨(Foam.Ty08.d052 n, 0), (Foam.Ty08.d052 n, 1),
   fun h => absurd (congrArg Prod.snd h) (by decide : (0 : Int) ≠ 1)⟩

abbrev t067 : Nat → Prop := fun n => n ≤ 3

theorem t104 : t067 3 := by decide

theorem t105 :
    t067 3 ∧ ¬ t067 4 := by
  exact ⟨by decide, by decide⟩

theorem t191 :
    ∃ x : Ty13 3, x ≠ Foam.Ty13.d074 3 :=
  ⟨Foam.Ty13.d072 3, Foam.Ty13.t156 3⟩

/-- info: 'Foam.t371' does not depend on any axioms -/
#guard_msgs in #print axioms t371

/-- info: 'Foam.t370' does not depend on any axioms -/
#guard_msgs in #print axioms t370

/-- info: 'Foam.t458' does not depend on any axioms -/
#guard_msgs in #print axioms t458

/-- info: 'Foam.t453' does not depend on any axioms -/
#guard_msgs in #print axioms t453

/-- info: 'Foam.t452' does not depend on any axioms -/
#guard_msgs in #print axioms t452

/-- info: 'Foam.t451' does not depend on any axioms -/
#guard_msgs in #print axioms t451

/-- info: 'Foam.t117' does not depend on any axioms -/
#guard_msgs in #print axioms t117

/-- info: 'Foam.t135' does not depend on any axioms -/
#guard_msgs in #print axioms t135

/-- info: 'Foam.t104' does not depend on any axioms -/
#guard_msgs in #print axioms t104

/-- info: 'Foam.t105' does not depend on any axioms -/
#guard_msgs in #print axioms t105

/-- info: 'Foam.t191' does not depend on any axioms -/
#guard_msgs in #print axioms t191

end Foam
