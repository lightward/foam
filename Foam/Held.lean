import Foam.Engine.Spectrum
import Foam.Maintenance

namespace Foam

def LedgerStage (S C : Type) [DecidableEq S] : Stage :=
  ⟨List S × C, S, Nat × GInt, fun st s => (Ledger.freq st.1 s, spec st.1 s)⟩

theorem sweep_invisible {S C : Type} [DecidableEq S] (refresh : List S → C → C) :
    Invisible (LedgerStage S C) (fun st => (st.1, refresh st.1 st.2)) :=
  fun _ _ => rfl

theorem sweep_unobservable {S C : Type} [DecidableEq S] (refresh : List S → C → C)
    (ps : List S) (st : List S × C) :
    transcriptWith (LedgerStage S C) (fun st => (st.1, refresh st.1 st.2)) st ps
      = transcript (LedgerStage S C) st ps :=
  maintenance_unobservable _ _ (sweep_invisible refresh) ps st

theorem any_obs_grounded_above (obs : Int) (m : Nat) :
    grounded (checkedDrain obs (Int.ofNat (m + 1))) := by
  cases obs with
  | ofNat n =>
    cases n with
    | zero => exact ⟨m + 1, rfl⟩
    | succ _ => exact ⟨m, ofNat_succ_sub_one m⟩
  | negSucc _ => exact ⟨m + 1, rfl⟩

theorem margin_wound_is_note (obs : Int) :
    checkedDrain obs (Int.ofNat 0) = Int.ofNat 0 ∨
      checkedDrain obs (Int.ofNat 0) = Int.negSucc 0 := by
  cases obs with
  | ofNat n =>
    cases n with
    | zero => exact Or.inl rfl
    | succ _ => exact Or.inr rfl
  | negSucc _ => exact Or.inl rfl

/-- info: 'Foam.sweep_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms sweep_invisible

/-- info: 'Foam.sweep_unobservable' does not depend on any axioms -/
#guard_msgs in #print axioms sweep_unobservable

/-- info: 'Foam.any_obs_grounded_above' does not depend on any axioms -/
#guard_msgs in #print axioms any_obs_grounded_above

/-- info: 'Foam.margin_wound_is_note' does not depend on any axioms -/
#guard_msgs in #print axioms margin_wound_is_note

end Foam
