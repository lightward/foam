import Foam.Ledger
import Foam.Seat.Closure
import Foam.Seat.Doubling
import Foam.Int

namespace Foam

def GInt.one : GInt := ⟨1, 0⟩

variable {S : Type}

def evalAt [DecidableEq S] (step : GInt → GInt) : List S → S → GInt
  | [], _ => GInt.zero
  | x :: l, s => (if x = s then GInt.one else GInt.zero).add (step (evalAt step l s))

def spec [DecidableEq S] : List S → S → GInt := evalAt GInt.rot

theorem spec_shift [DecidableEq S] (x : S) (l : List S) (s : S) :
    spec (x :: l) s = (if x = s then GInt.one else GInt.zero).add (GInt.rot (spec l s)) := rfl

theorem ofNat_ite (c : Prop) [inst : Decidable c] :
    (if c then (1 : Int) else 0) = Int.ofNat (if c then 1 else 0) := by
  cases inst with
  | isTrue _ => rfl
  | isFalse _ => rfl

theorem ite_mk (c : Prop) [inst : Decidable c] :
    (if c then GInt.one else GInt.zero) = (⟨if c then (1 : Int) else 0, 0⟩ : GInt) := by
  cases inst with
  | isTrue _ => rfl
  | isFalse _ => rfl

theorem evalOne_eq_freq [DecidableEq S] (l : List S) (s : S) :
    evalAt id l s = ⟨Int.ofNat (Ledger.freq l s), 0⟩ := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show (if x = s then GInt.one else GInt.zero).add (evalAt id l s) = _
    rw [ih, ite_mk (x = s), ofNat_ite (x = s)]
    rfl

theorem spec_finer_than_freq :
    (Ledger.freq [true, false] true = Ledger.freq [false, true] true ∧
        Ledger.freq [true, false] false = Ledger.freq [false, true] false) ∧
      spec [true, false] true ≠ spec [false, true] true :=
  ⟨⟨rfl, rfl⟩, by decide⟩

theorem align_one (z : GInt) : GInt.align GInt.one z = z.re := by
  show 1 * z.re + 0 * z.im = z.re
  rw [FInt.one_mul, FInt.zero_mul, FInt.addComm z.re 0, FInt.zero_add]

theorem align_i (z : GInt) : GInt.align GInt.one.rot z = z.im := by
  show (0 : Int) * z.re + 1 * z.im = z.im
  rw [FInt.zero_mul, FInt.one_mul, FInt.zero_add]

theorem align_one_evalOne [DecidableEq S] (l : List S) (s : S) :
    GInt.align GInt.one (evalAt id l s) = Int.ofNat (Ledger.freq l s) := by
  rw [evalOne_eq_freq, align_one]

def evalBeats [DecidableEq S] (step : GInt → GInt) : List (Option S) → S → GInt
  | [], _ => GInt.zero
  | none :: l, s => step (evalBeats step l s)
  | some x :: l, s => (if x = s then GInt.one else GInt.zero).add (step (evalBeats step l s))

theorem rest_turns [DecidableEq S] (step : GInt → GInt) (l : List (Option S)) (s : S) :
    evalBeats step (none :: l) s = step (evalBeats step l s) := rfl

theorem rest_invisible_to_count [DecidableEq S] (l : List (Option S)) (s : S) :
    evalBeats id (none :: l) s = evalBeats id l s := rfl

theorem rest_audible :
    evalBeats GInt.rot [some true] true ≠ evalBeats GInt.rot [none, some true] true := by
  decide

theorem bar_invisible [DecidableEq S] (l : List (Option S)) (s : S) :
    evalBeats GInt.rot (none :: none :: none :: none :: l) s = evalBeats GInt.rot l s := by
  show ((((evalBeats GInt.rot l s).rot).rot).rot).rot = evalBeats GInt.rot l s
  exact GInt.rot_complete _

theorem order_finer_than_spec :
    (Ledger.freq [true, false, false, false, false] true =
          Ledger.freq [false, false, false, false, true] true ∧
        Ledger.freq [true, false, false, false, false] false =
          Ledger.freq [false, false, false, false, true] false) ∧
      (spec [true, false, false, false, false] true =
          spec [false, false, false, false, true] true ∧
        spec [true, false, false, false, false] false =
          spec [false, false, false, false, true] false) ∧
      [true, false, false, false, false] ≠ [false, false, false, false, true] :=
  ⟨⟨rfl, rfl⟩, ⟨by decide, by decide⟩, by decide⟩

/-- info: 'Foam.evalOne_eq_freq' does not depend on any axioms -/
#guard_msgs in #print axioms evalOne_eq_freq

/-- info: 'Foam.spec_finer_than_freq' does not depend on any axioms -/
#guard_msgs in #print axioms spec_finer_than_freq

/-- info: 'Foam.align_one_evalOne' does not depend on any axioms -/
#guard_msgs in #print axioms align_one_evalOne

/-- info: 'Foam.bar_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms bar_invisible

/-- info: 'Foam.order_finer_than_spec' does not depend on any axioms -/
#guard_msgs in #print axioms order_finer_than_spec

end Foam
