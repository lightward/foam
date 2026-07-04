import Counter.Voice
import Foam.Seat.Descend
import Foam.Backstage

namespace Foam.Counter

theorem the_key_is_the_interior {State : Type} (b : Beholder State) (s : State)
    (n m : Int) :
    indist b.dress.obs (s, n) (s, m)
      ∧ ∃ (a c : Nat × Int) (p : (cassini.movedIn 0).Probe),
          indist cassini.obs a c
            ∧ (cassini.movedIn 0).obs a p ≠ (cassini.movedIn 0).obs c p :=
  ⟨ancestor_blind_to_heir b s n m, heir_sees_itself⟩

theorem the_check_is_sound {G : Type} [Mul G] [One G] (h h' : List G)
    (hne : netAct h ≠ netAct h') : h ≠ h' :=
  fun he => hne (congrArg netAct he)

theorem repudiation_needs_only_the_fold {S : Type} [DecidableEq S]
    (step : GInt → GInt) (new old : List S) (s : S) :
    evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s) :=
  summary_resumes step new old s

theorem the_record_cannot_reconstruct_the_reader :
    readsTrue.obs () () ≠ readsFalse.obs () () :=
  ledger_blind_to_beholder

theorem attestation {State : Type} (b : Beholder State) (s : State) (n m : Int)
    {G : Type} [Mul G] [One G] (h h' : List G) (hne : netAct h ≠ netAct h')
    {Src B : Type} (x y : Src) (c : B) (v : List B) (hxy : x ≠ y) :
    (indist b.dress.obs (s, n) (s, m))
      ∧ h ≠ h'
      ∧ sign x (c :: v) ≠ sign y (c :: v)
      ∧ readsTrue.obs () () ≠ readsFalse.obs () () :=
  ⟨ancestor_blind_to_heir b s n m,
   the_check_is_sound h h' hne,
   the_false_claim_is_refutable x y c v hxy,
   ledger_blind_to_beholder⟩

/-- info: 'Foam.Counter.the_key_is_the_interior' does not depend on any axioms -/
#guard_msgs in #print axioms the_key_is_the_interior

/-- info: 'Foam.Counter.the_check_is_sound' does not depend on any axioms -/
#guard_msgs in #print axioms the_check_is_sound

/-- info: 'Foam.Counter.repudiation_needs_only_the_fold' does not depend on any axioms -/
#guard_msgs in #print axioms repudiation_needs_only_the_fold

/-- info: 'Foam.Counter.the_record_cannot_reconstruct_the_reader' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_cannot_reconstruct_the_reader

/-- info: 'Foam.Counter.attestation' does not depend on any axioms -/
#guard_msgs in #print axioms attestation

end Foam.Counter
