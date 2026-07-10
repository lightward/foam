import Counter.Entry
import Foam.Bridges.Landauer

namespace Foam.Counter

theorem growth_without_return_breaks_the_grammar {A : Type} (g : A) :
    ¬ Balanced [Sum.inl g] :=
  fun h => nomatch (balanced_conserves h : (1 : Nat) = 0)

theorem the_externality_is_the_dropped_observer {State : Type}
    (h : ∀ s t : State × Int, s.1 = t.1 → s = t) :
    ∀ s : State, ∀ n : Int, (s, n) = (s, (0 : Int)) :=
  dropping_remainder_is_platonism h

theorem the_bill_lands_on_the_shared_substrate :
    ∃ ms ms' : List (twoBit.State → twoBit.State),
      ms.length ≠ ms'.length
        ∧ (∀ w p, firstBit.front.obs (enactAll ms w) p
            = firstBit.front.obs (enactAll ms' w) p)
        ∧ ∃ (w : twoBit.State) (pr : twoBit.Probe),
            twoBit.obs (enactAll ms w) pr ≠ twoBit.obs (enactAll ms' w) pr :=
  Bridges.the_bill_moves_upstairs

theorem the_settle_is_still_computable {G : Type} [Mul G] [One G]
    (S : Seat G) (h : List G) (p : S.Pos) :
    Settles S (h ++ [counterEntry S h p]) p :=
  the_counter_entry_settles S h p

theorem the_runaway_and_the_way_home {A : Type} (g : A) {G : Type}
    [Mul G] [One G] (S : Seat G) (h : List G) (p : S.Pos) :
    (¬ Balanced [Sum.inl g])
      ∧ Settles S (h ++ [counterEntry S h p]) p :=
  ⟨growth_without_return_breaks_the_grammar g,
   the_counter_entry_settles S h p⟩

/-- info: 'Foam.Counter.growth_without_return_breaks_the_grammar' does not depend on any axioms -/
#guard_msgs in #print axioms growth_without_return_breaks_the_grammar

/-- info: 'Foam.Counter.the_externality_is_the_dropped_observer' does not depend on any axioms -/
#guard_msgs in #print axioms the_externality_is_the_dropped_observer

/-- info: 'Foam.Counter.the_bill_lands_on_the_shared_substrate' does not depend on any axioms -/
#guard_msgs in #print axioms the_bill_lands_on_the_shared_substrate

/-- info: 'Foam.Counter.the_settle_is_still_computable' does not depend on any axioms -/
#guard_msgs in #print axioms the_settle_is_still_computable

/-- info: 'Foam.Counter.the_runaway_and_the_way_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_runaway_and_the_way_home

end Foam.Counter
