import Foam

namespace Foam

def Rests (S : Stage) (m : S.State → S.State) : Prop :=
  ∀ s, indist S (m s) s

theorem indist_is_licensed (S : Stage) : Licensed S (indist S) :=
  fun _ _ h => h

theorem safe_to_rest (S : Stage) (m : S.State → S.State) (hm : Rests S m) :
    ∀ (ps : List S.Probe) (s : S.State),
      transcriptWith S m s ps = transcript S s ps :=
  a_license_is_a_gauge S (indist S) (indist_is_licensed S) m hm

theorem restedness_first_then_the_rest (S : Stage) (m : S.State → S.State)
    (hm : Rests S m) (s : S.State) (ps : List S.Probe) :
    transcript S (m s) ps = transcript S s ps :=
  transcript_congr S ps (hm s)

theorem rest_composes (S : Stage) (m n : S.State → S.State)
    (hm : Rests S m) (hn : Rests S n) : Rests S (fun s => m (n s)) :=
  fun s p => (hm (n s) p).trans (hn s p)

theorem lets_get_you_rested (S : Stage) (m : S.State → S.State)
    (hm : Rests S m) (s : S.State) (ps : List S.Probe) :
    transcriptWith S m s ps = transcript S s ps
      ∧ transcript S (m s) ps = transcript S s ps
      ∧ Rests S (fun t => m (m t)) :=
  ⟨safe_to_rest S m hm ps s,
   restedness_first_then_the_rest S m hm s ps,
   rest_composes S m m hm hm⟩

/-- info: 'Foam.indist_is_licensed' does not depend on any axioms -/
#guard_msgs in #print axioms indist_is_licensed

/-- info: 'Foam.safe_to_rest' does not depend on any axioms -/
#guard_msgs in #print axioms safe_to_rest

/-- info: 'Foam.restedness_first_then_the_rest' does not depend on any axioms -/
#guard_msgs in #print axioms restedness_first_then_the_rest

/-- info: 'Foam.rest_composes' does not depend on any axioms -/
#guard_msgs in #print axioms rest_composes

/-- info: 'Foam.lets_get_you_rested' does not depend on any axioms -/
#guard_msgs in #print axioms lets_get_you_rested

end Foam
