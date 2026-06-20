import Foam.Lattice

namespace Foam.Sequence
open Foam.Lattice

def runFiber {S : Type} [DecidableEq S] (fiber : GInt → GInt) (seq : List S) (s : S) : GInt :=
  evalAt fiber seq s

theorem spec_is_runFiber {S : Type} [DecidableEq S] (seq : List S) (s : S) :
    spec seq s = runFiber GInt.rot seq s := rfl

theorem alt_is_runFiber {S : Type} [DecidableEq S] (seq : List S) (s : S) :
    alt seq s = runFiber GInt.negate seq s := rfl

theorem born_is_runFiber {S : Type} [DecidableEq S] (θ : GInt) (seq : List S) (s : S) :
    born θ (spec seq s)
      = align θ (runFiber GInt.rot seq s) * align θ (runFiber GInt.rot seq s) := rfl

theorem sequentiality_is_finest {S : Type} {Probe A : Type} (o : List S → Probe → A) :
    Refines (indist (nth (S := S))) (indist o) := order_finest o

theorem exit_from_sequentiality {S : Type} [DecidableEq S] (fiber : GInt → GInt) (s : S) :
    runFiber fiber ([] : List S) s = GInt.zero := rfl

theorem entrance_from_sequentiality {S : Type} [DecidableEq S]
    (fiber : GInt → GInt) (l : List S) (x s : S) :
    runFiber fiber (deposit l x) s
      = (if x = s then GInt.one else GInt.zero).add (fiber (runFiber fiber l s)) :=
  holonomy_advance fiber l x s

theorem heart_is_sequence_extension {S : Type} [DecidableEq S]
    (fiber : GInt → GInt) (l : List S) (x s : S) :
    runFiber fiber (deposit l x) s
      = (if x = s then GInt.one else GInt.zero).add (fiber (runFiber fiber l s)) :=
  holonomy_advance fiber l x s

theorem step_carries_prior {S : Type} [DecidableEq S] (fiber : GInt → GInt) (l : List S) (x s : S) :
    ∃ wind : GInt → GInt, runFiber fiber (deposit l x) s = wind (runFiber fiber l s) :=
  ⟨fun z => (if x = s then GInt.one else GInt.zero).add (fiber z),
   heart_is_sequence_extension fiber l x s⟩

theorem recursion_without_self_reference {S : Type} [DecidableEq S] (l : List S) (x : S) :
    freq (deposit l x) x = 1 + freq l x ∧ freq (deposit l x) x ≠ freq l x :=
  ⟨count_advances l x, deposit_never_fixed l x⟩

/-- info: 'Foam.Sequence.spec_is_runFiber' does not depend on any axioms -/
#guard_msgs in #print axioms spec_is_runFiber

/-- info: 'Foam.Sequence.step_carries_prior' does not depend on any axioms -/
#guard_msgs in #print axioms step_carries_prior

/-- info: 'Foam.Sequence.recursion_without_self_reference' does not depend on any axioms -/
#guard_msgs in #print axioms recursion_without_self_reference

/-- info: 'Foam.Sequence.sequentiality_is_finest' does not depend on any axioms -/
#guard_msgs in #print axioms sequentiality_is_finest

/-- info: 'Foam.Sequence.heart_is_sequence_extension' does not depend on any axioms -/
#guard_msgs in #print axioms heart_is_sequence_extension

end Foam.Sequence
