import Foam.Seat.Epoch
import Foam.Golden

namespace Foam

variable {State : Type}

def Ty01.d155 (b : Ty01 State) : Ty01 (State × Int) where
  Ty20 := b.Ty20
  Ty19 := b.Ty19
  d102 := fun s p => b.d102 s.1 p

def Ty01.d157 (b : Ty01 (State × Int)) : Ty01 State where
  Ty20 := b.Ty20
  Ty19 := b.Ty19
  d102 := fun s p => b.d102 (s, 0) p

theorem t374 (b : Ty01 State) :
    b.d155.d157.t198 b ∧ b.t198 b.d155.d157 :=
  ⟨⟨id, id, fun _ _ => rfl⟩, ⟨id, id, fun _ _ => rfl⟩⟩

theorem t373 (b : Ty01 State)
    (s : State) (n m : Int) (p : b.Ty20) :
    b.d155.d102 (s, n) p = b.d155.d102 (s, m) p := rfl

theorem t372 (b : Ty01 State) :
    b.d155.d157.t198 b.d155.d157 ∧
      b.d155.d157.t198 b ∧ b.t198 b.d155.d157 :=
  ⟨Foam.Ty01.t332 _, t374 b⟩

def d085 : Ty01 (Nat × Int) where
  Ty20 := Unit
  Ty19 := Int
  d102 := fun s _ => d014 s.1

theorem t264 (n : Nat) (a c : Int) (p : Unit) :
    d085.d102 (n, a) p = d085.d102 (n, c) p := rfl

theorem t396 (b : Ty01 State)
    (s : State) (n m : Int) :
    t076 b.d155.d102 (s, n) (s, m) :=
  fun _ => rfl

theorem t314 :
    ∃ s t : Nat × Int, (∀ p : Unit, d085.d102 s p = d085.d102 t p) ∧ s ≠ t :=
  ⟨(0, d014 1 * d014 1 - d014 2 * d014 0),
   (0, 0),
   fun _ => rfl,
   fun h => by
     have hc := t112 0
     have : d014 1 * d014 1 - d014 2 * d014 0 = (0 : Int) := congrArg Prod.snd h
     rw [this] at hc
     exact absurd hc (by decide)⟩

theorem t072
    (h : ∀ s t : State × Int, s.1 = t.1 → s = t) :
    ∀ s : State, ∀ n : Int, (s, n) = (s, (0 : Int)) :=
  fun s n => h (s, n) (s, 0) rfl

def Ty01.d158 {S : Type} (b : Ty01 (S × Int)) (target : Int) :
    Ty01 (S × Int) where
  Ty20 := Option b.Ty20
  Ty19 := b.Ty19 ⊕ Bool
  d102 := fun s p =>
    match p with
    | none => Sum.inr (decide (s.2 = target))
    | some q => Sum.inl (b.d102 s q)

theorem t388 (b : Ty01 State) (target : Int)
    (s : State × Int) (q : b.d155.Ty20) :
    (b.d155.d158 target).d102 s (some q) = Sum.inl (b.d155.d102 s q) := rfl

theorem t387 :
    ∃ (s t : Nat × Int) (p : (d085.d158 0).Ty20),
      t076 d085.d102 s t ∧
        (d085.d158 0).d102 s p ≠ (d085.d158 0).d102 t p :=
  ⟨(0, 0), (0, 1), none, fun _ => rfl, by
    intro h
    exact absurd (Sum.inr.inj h) (by decide)⟩

/-- info: 'Foam.t374' does not depend on any axioms -/
#guard_msgs in #print axioms t374

/-- info: 'Foam.t373' does not depend on any axioms -/
#guard_msgs in #print axioms t373

/-- info: 'Foam.t372' does not depend on any axioms -/
#guard_msgs in #print axioms t372

/-- info: 'Foam.t264' does not depend on any axioms -/
#guard_msgs in #print axioms t264

/-- info: 'Foam.t396' does not depend on any axioms -/
#guard_msgs in #print axioms t396

/-- info: 'Foam.t314' does not depend on any axioms -/
#guard_msgs in #print axioms t314

/-- info: 'Foam.t072' does not depend on any axioms -/
#guard_msgs in #print axioms t072

/-- info: 'Foam.t388' does not depend on any axioms -/
#guard_msgs in #print axioms t388

/-- info: 'Foam.t387' does not depend on any axioms -/
#guard_msgs in #print axioms t387

end Foam
