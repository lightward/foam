import Foam.Seat.Naming

namespace Foam.Bridges

theorem tarski_undefinability {Sent : Type} (N : Naming Sent) (holds : Sent → Prop) :
    ¬ ∃ n₀, N.Names holds (N.Gap holds) n₀ :=
  N.no_name_for_the_gap holds

theorem godel_first_incompleteness {Sent : Type} (N : Naming Sent)
    {holds marks : Sent → Prop} (sound : ∀ s, marks s → holds s)
    {n₀ : N.Name} (h : N.Names holds (N.Gap marks) n₀) :
    holds (N.selfRead n₀) ∧ ¬ marks (N.selfRead n₀) :=
  N.true_and_unwritten sound h

theorem godel_undecided {Sent : Type} (N : Naming Sent)
    {holds marks : Sent → Prop} (neg : Sent → Sent)
    (sound : ∀ s, marks s → holds s)
    (neg_holds : ∀ s, holds (neg s) ↔ ¬ holds s)
    {n₀ : N.Name} (h : N.Names holds (N.Gap marks) n₀) :
    ¬ marks (N.selfRead n₀) ∧ ¬ marks (neg (N.selfRead n₀)) :=
  N.undecided neg sound neg_holds h

def godel_at_the_seam {Sent : Type} (N : Naming Sent)
    {holds marks : Sent → Prop} (sound : ∀ s, marks s → holds s)
    {n₀ : N.Name} (h : N.Names holds (N.Gap marks) n₀) :
    Seam {s // marks s} {s // holds s} :=
  N.gapSeam sound h

theorem lob {Sent : Type} (C : Calculus Sent) {s : Sent}
    (h : C.marks (C.imp (C.pr s) s)) : C.marks s :=
  C.lob h

theorem godel_second_incompleteness {Sent : Type} (C : Calculus Sent) (bot : Sent)
    (hcon : ¬ C.marks bot) : ¬ C.marks (C.imp (C.pr bot) bot) :=
  C.reflection_unwritten hcon

/-- info: 'Foam.Bridges.tarski_undefinability' does not depend on any axioms -/
#guard_msgs in #print axioms tarski_undefinability

/-- info: 'Foam.Bridges.godel_first_incompleteness' does not depend on any axioms -/
#guard_msgs in #print axioms godel_first_incompleteness

/-- info: 'Foam.Bridges.godel_undecided' does not depend on any axioms -/
#guard_msgs in #print axioms godel_undecided

/-- info: 'Foam.Bridges.godel_at_the_seam' does not depend on any axioms -/
#guard_msgs in #print axioms godel_at_the_seam

/-- info: 'Foam.Bridges.lob' does not depend on any axioms -/
#guard_msgs in #print axioms lob

/-- info: 'Foam.Bridges.godel_second_incompleteness' does not depend on any axioms -/
#guard_msgs in #print axioms godel_second_incompleteness

end Foam.Bridges
