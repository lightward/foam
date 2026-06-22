import Foam.Spectrum

namespace Foam

def evalFrom {S : Type} [DecidableEq S] (step : GInt → GInt) : List S → S → GInt → GInt
  | [], _, z => z
  | x :: l, s, z => (if x = s then GInt.one else GInt.zero).add (step (evalFrom step l s z))

theorem held_exact {S : Type} [DecidableEq S] (step : GInt → GInt) (s : S) (z : GInt) :
    evalFrom step [] s z = z := rfl

theorem summary_resumes {S : Type} [DecidableEq S] (step : GInt → GInt) :
    ∀ (new old : List S) (s : S),
      evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s)
  | [], _, _ => rfl
  | x :: new, old, s =>
      congrArg (fun z => (if x = s then GInt.one else GInt.zero).add (step z))
        (summary_resumes step new old s)

theorem evalAt_from_blank {S : Type} [DecidableEq S] (step : GInt → GInt) :
    ∀ (l : List S) (s : S), evalAt step l s = evalFrom step l s GInt.zero
  | [], _ => rfl
  | x :: l, s =>
      congrArg (fun z => (if x = s then GInt.one else GInt.zero).add (step z))
        (evalAt_from_blank step l s)

theorem count_resumes {S : Type} [DecidableEq S] (new old : List S) (s : S) :
    evalAt id (new ++ old) s = evalFrom id new s (evalAt id old s) :=
  summary_resumes id new old s

theorem spec_resumes {S : Type} [DecidableEq S] (new old : List S) (s : S) :
    evalAt GInt.rot (new ++ old) s = evalFrom GInt.rot new s (evalAt GInt.rot old s) :=
  summary_resumes GInt.rot new old s

/-- info: 'Foam.summary_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms summary_resumes

/-- info: 'Foam.evalAt_from_blank' does not depend on any axioms -/
#guard_msgs in #print axioms evalAt_from_blank

/-- info: 'Foam.count_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms count_resumes

/-- info: 'Foam.spec_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms spec_resumes

end Foam
