import Foam.Engine.Spectrum
import Foam.Maintenance

namespace Foam

def d206 (S C : Type) [DecidableEq S] : Ty18 :=
  ⟨List S × C, S, Nat × Ty05, fun st s => (Foam.Ty08.d003 st.1 s, d197 st.1 s)⟩

theorem t478 {S C : Type} [DecidableEq S] (refresh : List S → C → C) :
    t217 (d206 S C) (fun st => (st.1, refresh st.1 st.2)) :=
  fun _ _ => rfl

theorem t479 {S C : Type} [DecidableEq S] (refresh : List S → C → C)
    (ps : List S) (st : List S × C) :
    d154 (d206 S C) (fun st => (st.1, refresh st.1 st.2)) st ps
      = d153 (d206 S C) st ps :=
  t386 _ _ (t478 refresh) ps st

theorem t161 (obs : Int) (m : Nat) :
    t073 (d086 obs (Int.ofNat (m + 1))) := by
  cases obs with
  | ofNat n =>
    cases n with
    | zero => exact ⟨m + 1, rfl⟩
    | succ _ => exact ⟨m, t085 m⟩
  | negSucc _ => exact ⟨m + 1, rfl⟩

theorem t181 (obs : Int) :
    d086 obs (Int.ofNat 0) = Int.ofNat 0 ∨
      d086 obs (Int.ofNat 0) = Int.negSucc 0 := by
  cases obs with
  | ofNat n =>
    cases n with
    | zero => exact Or.inl rfl
    | succ _ => exact Or.inr rfl
  | negSucc _ => exact Or.inl rfl

/-- info: 'Foam.t478' does not depend on any axioms -/
#guard_msgs in #print axioms t478

/-- info: 'Foam.t479' does not depend on any axioms -/
#guard_msgs in #print axioms t479

/-- info: 'Foam.t161' does not depend on any axioms -/
#guard_msgs in #print axioms t161

/-- info: 'Foam.t181' does not depend on any axioms -/
#guard_msgs in #print axioms t181

end Foam
