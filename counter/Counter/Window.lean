import Foam.Seat.Epoch

namespace Foam.Counter

variable {State : Type}

def CoLocated (a b : Beholder State) : Prop := a.Covers b ∧ b.Covers a

theorem colocated_refl (a : Beholder State) : CoLocated a a :=
  ⟨a.covers_refl, a.covers_refl⟩

theorem out_of_disagreement_nothing_diverges {a b : Beholder State}
    (h : CoLocated a b) (c : Beholder State) (hbc : b.Covers c) : a.Covers c :=
  Beholder.covers_trans h.1 hbc

theorem letting_go_loses_nothing {bank : List (Beholder State)}
    {a b : Beholder State} (ha : a ∈ bank) (h : CoLocated a b) :
    Known bank b :=
  ⟨a, ha, h.1⟩

theorem reduced_tolerates_only_colocation {bank : List (Beholder State)}
    (hred : Reduced bank) :
    ∀ a ∈ bank, ∀ b ∈ bank, a.Covers b → CoLocated a b :=
  fun a ha b hb hab => ⟨hab, hred a ha b hb hab⟩

theorem easy_entry {walk bank : List (Beholder State)} (q : Beholder State)
    (hrun : Run walk bank) (hknown : Known bank q) : Run (q :: walk) bank :=
  Run.skip q hrun hknown

theorem designed_entry {walk bank bank' : List (Beholder State)}
    (q : Beholder State) (hrun : Run walk bank)
    (hirr : Irreducible bank q) (href : Refresh bank q bank') :
    Known bank' q ∧ Reduced bank'
      ∧ ∀ w ∈ (q :: walk), Known bank' w :=
  ⟨href.locates, (Run.turn q hrun hirr href).reduced,
   (Run.turn q hrun hirr href).covers⟩

/-- info: 'Foam.Counter.colocated_refl' does not depend on any axioms -/
#guard_msgs in #print axioms colocated_refl

/-- info: 'Foam.Counter.out_of_disagreement_nothing_diverges' does not depend on any axioms -/
#guard_msgs in #print axioms out_of_disagreement_nothing_diverges

/-- info: 'Foam.Counter.letting_go_loses_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms letting_go_loses_nothing

/-- info: 'Foam.Counter.reduced_tolerates_only_colocation' does not depend on any axioms -/
#guard_msgs in #print axioms reduced_tolerates_only_colocation

/-- info: 'Foam.Counter.easy_entry' does not depend on any axioms -/
#guard_msgs in #print axioms easy_entry

/-- info: 'Foam.Counter.designed_entry' does not depend on any axioms -/
#guard_msgs in #print axioms designed_entry

end Foam.Counter
