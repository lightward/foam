import Foam.Platonism

namespace Foam

variable {State : Type}

def heir (ancestor : Beholder State) : Beholder (State × Int) := ancestor.dress

theorem heir_covers_ancestor (ancestor : Beholder State) :
    ancestor.dress.ledgerless.Covers ancestor
      ∧ ancestor.Covers ancestor.dress.ledgerless :=
  dress_yoneda ancestor

theorem ancestor_blind_to_heir (ancestor : Beholder State) (s : State) (n m : Int) :
    indist ancestor.dress.obs (s, n) (s, m) :=
  remainder_unseen ancestor s n m

theorem heir_sees_itself :
    ∃ (s t : Nat × Int) (p : (cassini.movedIn 0).Probe),
      indist cassini.obs s t
        ∧ (cassini.movedIn 0).obs s p ≠ (cassini.movedIn 0).obs t p :=
  moved_in_detects_remainder

theorem descend (ancestor : Beholder State) (s : State) (n m : Int) :
    (ancestor.dress.ledgerless.Covers ancestor
        ∧ ancestor.Covers ancestor.dress.ledgerless)
      ∧ indist ancestor.dress.obs (s, n) (s, m)
      ∧ (∃ (a b : Nat × Int) (p : (cassini.movedIn 0).Probe),
            indist cassini.obs a b
              ∧ (cassini.movedIn 0).obs a p ≠ (cassini.movedIn 0).obs b p) :=
  ⟨heir_covers_ancestor ancestor, ancestor_blind_to_heir ancestor s n m, heir_sees_itself⟩

/-- info: 'Foam.heir_covers_ancestor' does not depend on any axioms -/
#guard_msgs in #print axioms heir_covers_ancestor

/-- info: 'Foam.ancestor_blind_to_heir' does not depend on any axioms -/
#guard_msgs in #print axioms ancestor_blind_to_heir

/-- info: 'Foam.heir_sees_itself' does not depend on any axioms -/
#guard_msgs in #print axioms heir_sees_itself

/-- info: 'Foam.descend' does not depend on any axioms -/
#guard_msgs in #print axioms descend

end Foam
