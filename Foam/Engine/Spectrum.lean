import Foam.Ledger
import Foam.Seat.Closure
import Foam.Seat.Doubling
import Foam.Int

namespace Foam

def Ty05.d042 : Ty05 := ⟨1, 0⟩

variable {S : Type}

def d089 [DecidableEq S] (step : Ty05 → Ty05) : List S → S → Ty05
  | [], _ => Foam.Ty05.d044
  | x :: l, s => (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (step (d089 step l s))

def d197 [DecidableEq S] : List S → S → Ty05 := d089 Foam.Ty05.d115

theorem t403 [DecidableEq S] (x : S) (l : List S) (s : S) :
    d197 (x :: l) s = (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (Foam.Ty05.d115 (d197 l s)) := rfl

theorem t084 (c : Prop) [inst : Decidable c] :
    (if c then (1 : Int) else 0) = Int.ofNat (if c then 1 else 0) := by
  cases inst with
  | isTrue _ => rfl
  | isFalse _ => rfl

theorem t173 (c : Prop) [inst : Decidable c] :
    (if c then Foam.Ty05.d042 else Foam.Ty05.d044) = (⟨if c then (1 : Int) else 0, 0⟩ : Ty05) := by
  cases inst with
  | isTrue _ => rfl
  | isFalse _ => rfl

theorem t168 [DecidableEq S] (l : List S) (s : S) :
    d089 id l s = ⟨Int.ofNat (Foam.Ty08.d003 l s), 0⟩ := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (d089 id l s) = _
    rw [ih, t173 (x = s), t084 (x = s)]
    rfl

theorem t402 :
    (Foam.Ty08.d003 [true, false] true = Foam.Ty08.d003 [false, true] true ∧
        Foam.Ty08.d003 [true, false] false = Foam.Ty08.d003 [false, true] false) ∧
      d197 [true, false] true ≠ d197 [false, true] true :=
  ⟨⟨rfl, rfl⟩, by decide⟩

theorem t258 (z : Ty05) : Foam.Ty05.d109 Foam.Ty05.d042 z = z.d043 := by
  show 1 * z.d043 + 0 * z.d041 = z.d043
  rw [Foam.t037, Foam.t055, Foam.t004 z.d043 0, Foam.t054]

theorem t257 (z : Ty05) : Foam.Ty05.d109 Foam.Ty05.d042.d115 z = z.d041 := by
  show (0 : Int) * z.d043 + 1 * z.d041 = z.d041
  rw [Foam.t055, Foam.t037, Foam.t054]

theorem t259 [DecidableEq S] (l : List S) (s : S) :
    Foam.Ty05.d109 Foam.Ty05.d042 (d089 id l s) = Int.ofNat (Foam.Ty08.d003 l s) := by
  rw [t168, t258]

def d090 [DecidableEq S] (step : Ty05 → Ty05) : List (Option S) → S → Ty05
  | [], _ => Foam.Ty05.d044
  | none :: l, s => step (d090 step l s)
  | some x :: l, s => (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (step (d090 step l s))

theorem t184 [DecidableEq S] (step : Ty05 → Ty05) (l : List (Option S)) (s : S) :
    d090 step (none :: l) s = step (d090 step l s) := rfl

theorem t183 [DecidableEq S] (l : List (Option S)) (s : S) :
    d090 id (none :: l) s = d090 id l s := rfl

theorem t315 :
    d090 Foam.Ty05.d115 [some true] true ≠ d090 Foam.Ty05.d115 [none, some true] true := by
  decide

theorem t261 [DecidableEq S] (l : List (Option S)) (s : S) :
    d090 Foam.Ty05.d115 (none :: none :: none :: none :: l) s = d090 Foam.Ty05.d115 l s := by
  show ((((d090 Foam.Ty05.d115 l s).d115).d115).d115).d115 = d090 Foam.Ty05.d115 l s
  exact Foam.Ty05.t214 _

theorem t393 :
    (Foam.Ty08.d003 [true, false, false, false, false] true =
          Foam.Ty08.d003 [false, false, false, false, true] true ∧
        Foam.Ty08.d003 [true, false, false, false, false] false =
          Foam.Ty08.d003 [false, false, false, false, true] false) ∧
      (d197 [true, false, false, false, false] true =
          d197 [false, false, false, false, true] true ∧
        d197 [true, false, false, false, false] false =
          d197 [false, false, false, false, true] false) ∧
      [true, false, false, false, false] ≠ [false, false, false, false, true] :=
  ⟨⟨rfl, rfl⟩, ⟨by decide, by decide⟩, by decide⟩

/-- info: 'Foam.t168' does not depend on any axioms -/
#guard_msgs in #print axioms t168

/-- info: 'Foam.t402' does not depend on any axioms -/
#guard_msgs in #print axioms t402

/-- info: 'Foam.t259' does not depend on any axioms -/
#guard_msgs in #print axioms t259

/-- info: 'Foam.t261' does not depend on any axioms -/
#guard_msgs in #print axioms t261

/-- info: 'Foam.t393' does not depend on any axioms -/
#guard_msgs in #print axioms t393

end Foam
