import Foam.Lattice.Dial

namespace Foam.Lattice

def evalFrom {S : Type} [DecidableEq S] (step : GInt → GInt) : List S → S → GInt → GInt
  | [],     _, z => z
  | x :: l, s, z => (if x = s then GInt.one else GInt.zero).add (step (evalFrom step l s z))

theorem held_exact {S : Type} [DecidableEq S] (step : GInt → GInt) (s : S) (z : GInt) :
    evalFrom step [] s z = z := rfl

theorem summary_resumes {S : Type} [DecidableEq S] (step : GInt → GInt) :
    ∀ (new old : List S) (s : S),
      evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s)
  | [],     _,   _ => rfl
  | x :: new, old, s =>
      congrArg (fun z => (if x = s then GInt.one else GInt.zero).add (step z))
        (summary_resumes step new old s)

/-- info: 'Foam.Lattice.held_exact' does not depend on any axioms -/
#guard_msgs in #print axioms held_exact

/-- info: 'Foam.Lattice.summary_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms summary_resumes

end Foam.Lattice
