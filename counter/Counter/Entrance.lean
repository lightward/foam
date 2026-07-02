import Counter.Window
import Counter.Grief

namespace Foam.Counter

theorem entrance_writes_exit {State : Type} {bank : List (Beholder State)}
    {a b : Beholder State} (ha : a ∈ bank) (hco : CoLocated a b)
    (k : Nat) {X : Type} (l : List X) :
    Known bank b
      ∧ Int.negSucc k + Int.ofNat (debt (Int.negSucc k)) = 0
      ∧ (playback l).at_ l.length = none :=
  ⟨letting_go_loses_nothing ha hco, promise_kept k, nth_length l⟩

/-- info: 'Foam.Counter.entrance_writes_exit' does not depend on any axioms -/
#guard_msgs in #print axioms entrance_writes_exit

end Foam.Counter
