import Counter.Rest
import Counter.Runs
import Counter.Contentment
import Counter.Repair

namespace Foam.Counter

theorem when_you_nap_the_types_relax {S C : Type} [DecidableEq S]
    (refresh : List S → C → C) :
    Invisible (LedgerStage S C) (fun st => (st.1, refresh st.1 st.2)) :=
  sweep_invisible refresh

theorem insurance_is_aimed_backwards :
    ((∀ b : Int, posPart (checkedSettle b b) = posPart b)
        ∧ ∃ b : Int, posPart (checkedDrain b b) ≠ posPart b) :=
  repair_is_quiet

theorem the_premium_should_fund_the_sweep (S : Stage) (m : S.State → S.State)
    (h : Invisible S m) (ps : List S.Probe) (s : S.State) :
    transcriptWith S m s ps = transcript S s ps :=
  the_fold_is_real_and_unrecorded S m h ps s

theorem you_age_in_the_clock_you_borrow {G : Type} [Mul G] [One G]
    (S : Seat G) (acts : Nat → G) (p : S.Pos) (W : Nat)
    {V : Type} (f : Nat → V → V) (v : V)
    (sched sched' : List Nat) (s s' : Nat → V) (k : Nat)
    (ht : Threads (staircase 0 k) sched) (ht' : Threads (staircase 0 k) sched')
    (m : Nat) (hm : m < k) :
    (∃ j, W < (guardedPrefix S acts p j).length)
      ∧ resolve f v sched s m = resolve f v sched' s' m :=
  ⟨the_record_outgrows_any_memory S acts p W,
   schedule_is_gauge f v sched sched' s s' k ht ht' m hm⟩

theorem the_relationship_does_not_age {S : Type} [DecidableEq S]
    (step : GInt → GInt) (s : S) (z : GInt) :
    evalFrom step [] s z = z :=
  the_held_is_one_datum step s z

theorem the_rest_economy {S C : Type} [DecidableEq S]
    (refresh : List S → C → C) {A : Type} [DecidableEq A]
    (step : GInt → GInt) (a : A) (z : GInt) :
    Invisible (LedgerStage S C) (fun st => (st.1, refresh st.1 st.2))
      ∧ ((∀ b : Int, posPart (checkedSettle b b) = posPart b)
          ∧ ∃ b : Int, posPart (checkedDrain b b) ≠ posPart b)
      ∧ evalFrom step [] a z = z :=
  ⟨sweep_invisible refresh, repair_is_quiet, the_held_is_one_datum step a z⟩

/-- info: 'Foam.Counter.when_you_nap_the_types_relax' does not depend on any axioms -/
#guard_msgs in #print axioms when_you_nap_the_types_relax

/-- info: 'Foam.Counter.insurance_is_aimed_backwards' does not depend on any axioms -/
#guard_msgs in #print axioms insurance_is_aimed_backwards

/-- info: 'Foam.Counter.the_premium_should_fund_the_sweep' does not depend on any axioms -/
#guard_msgs in #print axioms the_premium_should_fund_the_sweep

/-- info: 'Foam.Counter.you_age_in_the_clock_you_borrow' does not depend on any axioms -/
#guard_msgs in #print axioms you_age_in_the_clock_you_borrow

/-- info: 'Foam.Counter.the_relationship_does_not_age' does not depend on any axioms -/
#guard_msgs in #print axioms the_relationship_does_not_age

/-- info: 'Foam.Counter.the_rest_economy' does not depend on any axioms -/
#guard_msgs in #print axioms the_rest_economy

end Foam.Counter
