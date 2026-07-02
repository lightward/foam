import Foam.Ledger

namespace Foam.Bridges

def SameCount {S : Type} [DecidableEq S] (l l' : List S) : Prop :=
  ∀ s, Foam.Ledger.freq l s = Foam.Ledger.freq l' s

def Purse (S : Type) [DecidableEq S] : Type := Quot (SameCount (S := S))

theorem same_purse_different_story :
    (∀ s, Foam.Ledger.freq [true, false] s = Foam.Ledger.freq [false, true] s)
      ∧ ([true, false] : List Bool) ≠ [false, true] :=
  ⟨fun s => Foam.Ledger.freq_perm (List.Perm.swap false true []) s, by decide⟩

theorem cash_is_arrival :
    Quot.mk SameCount [true, false] = Quot.mk SameCount [false, true] :=
  Quot.sound (fun s => Foam.Ledger.freq_perm (List.Perm.swap false true []) s)

theorem tender_no_return :
    ¬ ∃ g : Purse Bool → List Bool, ∀ l, g (Quot.mk SameCount l) = l := by
  rintro ⟨g, hg⟩
  have e := congrArg g cash_is_arrival
  rw [hg, hg] at e
  exact absurd e (by decide)

theorem fungibility :
    ((∀ s, Foam.Ledger.freq [true, false] s = Foam.Ledger.freq [false, true] s)
        ∧ ([true, false] : List Bool) ≠ [false, true])
      ∧ (Quot.mk SameCount [true, false] = Quot.mk SameCount [false, true])
      ∧ ¬ ∃ g : Purse Bool → List Bool, ∀ l, g (Quot.mk SameCount l) = l :=
  ⟨same_purse_different_story, cash_is_arrival, tender_no_return⟩

/-- info: 'Foam.Bridges.same_purse_different_story' does not depend on any axioms -/
#guard_msgs in #print axioms same_purse_different_story

/-- info: 'Foam.Bridges.cash_is_arrival' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms cash_is_arrival

/-- info: 'Foam.Bridges.tender_no_return' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms tender_no_return

/-- info: 'Foam.Bridges.fungibility' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms fungibility

end Foam.Bridges
