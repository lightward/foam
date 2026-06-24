import Foam.Int

namespace Foam

theorem t085 (n : Nat) : Int.ofNat (n + 1) - 1 = Int.ofNat n := by
  show (Int.ofNat n + 1) - 1 = Int.ofNat n
  exact Foam.t013 (Int.ofNat n) 1

def d016 : Int → Bool
  | Int.ofNat 0 => false
  | Int.ofNat (_ + 1) => true
  | Int.negSucc _ => false

def d086 (obs bal : Int) : Int :=
  match d016 obs with
  | true => bal - 1
  | false => bal

theorem t193 : d086 1 (d086 1 1) = -1 := rfl

theorem t194 : d086 2 (d086 2 2) = 0 := rfl

def t073 (b : Int) : Prop := ∃ m : Nat, b = Int.ofNat m

theorem t195 (m : Nat) :
    t073 (d086 (Int.ofNat (m + 2))
      (d086 (Int.ofNat (m + 2)) (Int.ofNat (m + 2)))) := by
  refine ⟨m, ?_⟩
  have h1 : d086 (Int.ofNat (m + 2)) (Int.ofNat (m + 2)) = Int.ofNat (m + 1) :=
    t085 (m + 1)
  rw [h1]
  exact t085 m

theorem t169 (bal : Int) (h : t073 bal) :
    t073 (d086 bal bal) := by
  obtain ⟨m, rfl⟩ := h
  cases m with
  | zero => exact ⟨0, rfl⟩
  | succ k => exact ⟨k, t085 k⟩

def d010 : Nat → Int → Int
  | 0, bal => bal
  | k + 1, bal => d010 k (d086 bal bal)

theorem t108 (k : Nat) (bal : Int) (h : t073 bal) :
    t073 (d010 k bal) := by
  induction k generalizing bal with
  | zero => exact h
  | succ n ih => exact ih (d086 bal bal) (t169 bal h)

theorem t086 : ∀ m : Nat, (Int.ofNat m) ≠ (-1 : Int) := by
  intro m h
  exact Int.noConfusion h

theorem t087 : (-1 : Int) + 1 = 0 := rfl

def d007 : Int → Nat
  | Int.ofNat _ => 0
  | Int.negSucc k => k + 1

theorem t106 (b : Int) : d007 b = 0 ↔ t073 b := by
  cases b with
  | ofNat m => exact ⟨fun _ => ⟨m, rfl⟩, fun _ => rfl⟩
  | negSucc k =>
    constructor
    · intro h; exact Nat.noConfusion h
    · intro h; obtain ⟨m, hm⟩ := h; exact Int.noConfusion hm

theorem t192 (k : Nat) :
    d086 (Int.negSucc k) (Int.negSucc k) = Int.negSucc k := rfl

theorem t127 (k : Nat) :
    Int.negSucc k + Int.ofNat (d007 (Int.negSucc k)) = 0 := by
  show Int.subNatNat (k + 1) (k + 1) = 0
  unfold Int.subNatNat
  rw [Nat.sub_self]
  rfl

def d095 : Int → Bool
  | Int.ofNat _ => false
  | Int.negSucc _ => true

def d141 (obs bal : Int) : Int :=
  match d095 obs with
  | true => bal + 1
  | false => bal

theorem t321 (m : Nat) :
    d141 (Int.ofNat m) (Int.ofNat m) = Int.ofNat m := rfl

theorem t288 (k : Nat) :
    d141 (Int.negSucc (k + 1)) (Int.negSucc (k + 1)) = Int.negSucc k := rfl

theorem t287 :
    d141 (Int.negSucc 0) (Int.negSucc 0) = 0 := rfl

theorem t324 :
    d141 (-1) (d141 (-1) (-1)) = 1 := rfl

theorem t310 :
    t073 (d141 (-1) (d141 (-1) (-1))) := ⟨1, rfl⟩

/-- info: 'Foam.t193' does not depend on any axioms -/
#guard_msgs in #print axioms t193

/-- info: 'Foam.t195' does not depend on any axioms -/
#guard_msgs in #print axioms t195

/-- info: 'Foam.t169' does not depend on any axioms -/
#guard_msgs in #print axioms t169

/-- info: 'Foam.t108' does not depend on any axioms -/
#guard_msgs in #print axioms t108

/-- info: 'Foam.t086' does not depend on any axioms -/
#guard_msgs in #print axioms t086

/-- info: 'Foam.t087' does not depend on any axioms -/
#guard_msgs in #print axioms t087

/-- info: 'Foam.t106' does not depend on any axioms -/
#guard_msgs in #print axioms t106

/-- info: 'Foam.t127' does not depend on any axioms -/
#guard_msgs in #print axioms t127

/-- info: 'Foam.t310' does not depend on any axioms -/
#guard_msgs in #print axioms t310

end Foam
