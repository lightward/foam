import Foam.Int

namespace Foam

theorem ofNat_succ_sub_one (n : Nat) : Int.ofNat (n + 1) - 1 = Int.ofNat n := by
  show (Int.ofNat n + 1) - 1 = Int.ofNat n
  exact FInt.add_sub_cancel_right (Int.ofNat n) 1

def isPos : Int → Bool
  | Int.ofNat 0 => false
  | Int.ofNat (_ + 1) => true
  | Int.negSucc _ => false

def checkedDrain (obs bal : Int) : Int :=
  match isPos obs with
  | true => bal - 1
  | false => bal

theorem stale_escapes_floor : checkedDrain 1 (checkedDrain 1 1) = -1 := rfl

theorem stale_lands_at_ground : checkedDrain 2 (checkedDrain 2 2) = 0 := rfl

def grounded (b : Int) : Prop := ∃ m : Nat, b = Int.ofNat m

theorem stale_safe_off_margin (m : Nat) :
    grounded (checkedDrain (Int.ofNat (m + 2))
      (checkedDrain (Int.ofNat (m + 2)) (Int.ofNat (m + 2)))) := by
  refine ⟨m, ?_⟩
  have h1 : checkedDrain (Int.ofNat (m + 2)) (Int.ofNat (m + 2)) = Int.ofNat (m + 1) :=
    ofNat_succ_sub_one (m + 1)
  rw [h1]
  exact ofNat_succ_sub_one m

theorem fresh_holds_floor (bal : Int) (h : grounded bal) :
    grounded (checkedDrain bal bal) := by
  obtain ⟨m, rfl⟩ := h
  cases m with
  | zero => exact ⟨0, rfl⟩
  | succ k => exact ⟨k, ofNat_succ_sub_one k⟩

def drainSeq : Nat → Int → Int
  | 0, bal => bal
  | k + 1, bal => drainSeq k (checkedDrain bal bal)

theorem drainSeq_holds_floor (k : Nat) (bal : Int) (h : grounded bal) :
    grounded (drainSeq k bal) := by
  induction k generalizing bal with
  | zero => exact h
  | succ n ih => exact ih (checkedDrain bal bal) (fresh_holds_floor bal h)

theorem scar_outside_carrier : ∀ m : Nat, (Int.ofNat m) ≠ (-1 : Int) := by
  intro m h
  exact Int.noConfusion h

theorem scar_repair : (-1 : Int) + 1 = 0 := rfl

def debt : Int → Nat
  | Int.ofNat _ => 0
  | Int.negSucc k => k + 1

theorem debt_zero_iff_grounded (b : Int) : debt b = 0 ↔ grounded b := by
  cases b with
  | ofNat m => exact ⟨fun _ => ⟨m, rfl⟩, fun _ => rfl⟩
  | negSucc k =>
    constructor
    · intro h; exact Nat.noConfusion h
    · intro h; obtain ⟨m, hm⟩ := h; exact Int.noConfusion hm

theorem scar_stable (k : Nat) :
    checkedDrain (Int.negSucc k) (Int.negSucc k) = Int.negSucc k := rfl

theorem promise_kept (k : Nat) :
    Int.negSucc k + Int.ofNat (debt (Int.negSucc k)) = 0 := by
  show Int.subNatNat (k + 1) (k + 1) = 0
  unfold Int.subNatNat
  rw [Nat.sub_self]
  rfl

def isNeg : Int → Bool
  | Int.ofNat _ => false
  | Int.negSucc _ => true

def checkedSettle (obs bal : Int) : Int :=
  match isNeg obs with
  | true => bal + 1
  | false => bal

theorem settle_stops_at_ground (m : Nat) :
    checkedSettle (Int.ofNat m) (Int.ofNat m) = Int.ofNat m := rfl

theorem fresh_settle_steps (k : Nat) :
    checkedSettle (Int.negSucc (k + 1)) (Int.negSucc (k + 1)) = Int.negSucc k := rfl

theorem fresh_settle_grounds :
    checkedSettle (Int.negSucc 0) (Int.negSucc 0) = 0 := rfl

theorem stale_settle_passes_ground :
    checkedSettle (-1) (checkedSettle (-1) (-1)) = 1 := rfl

theorem phantom_invisible :
    grounded (checkedSettle (-1) (checkedSettle (-1) (-1))) := ⟨1, rfl⟩

/-- info: 'Foam.stale_escapes_floor' does not depend on any axioms -/
#guard_msgs in #print axioms stale_escapes_floor

/-- info: 'Foam.stale_safe_off_margin' does not depend on any axioms -/
#guard_msgs in #print axioms stale_safe_off_margin

/-- info: 'Foam.fresh_holds_floor' does not depend on any axioms -/
#guard_msgs in #print axioms fresh_holds_floor

/-- info: 'Foam.drainSeq_holds_floor' does not depend on any axioms -/
#guard_msgs in #print axioms drainSeq_holds_floor

/-- info: 'Foam.scar_outside_carrier' does not depend on any axioms -/
#guard_msgs in #print axioms scar_outside_carrier

/-- info: 'Foam.scar_repair' does not depend on any axioms -/
#guard_msgs in #print axioms scar_repair

/-- info: 'Foam.debt_zero_iff_grounded' does not depend on any axioms -/
#guard_msgs in #print axioms debt_zero_iff_grounded

/-- info: 'Foam.promise_kept' does not depend on any axioms -/
#guard_msgs in #print axioms promise_kept

/-- info: 'Foam.phantom_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms phantom_invisible

end Foam
