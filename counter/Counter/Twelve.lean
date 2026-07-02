import Counter.Third
import Counter.Tempo

namespace Foam.Counter

theorem twelveness {A B X : Type} (f : List (A ⊕ B) → X) (n : Nat) :
    (∃ zs zs' : List (Bool ⊕ Bool),
        ownFrames zs = ownFrames zs'
          ∧ ownFramesR zs = ownFramesR zs'
          ∧ whoActedFirst zs ≠ whoActedFirst zs')
      ∧ (∃ post : List (A ⊕ B) → X,
          ∀ zs, f zs = post ((thirdSeat A B).obs zs ()))
      ∧ (Rung.mul (n + 1) (Rung.mul (n + 1) (fresh n) (fresh n))
            (Rung.mul (n + 1) (fresh n) (fresh n)) = Rung.one (n + 1)
          ∧ Rung.mul (n + 1) (fresh n) (fresh n) ≠ Rung.one (n + 1))
      ∧ 3 * 4 = 12 :=
  ⟨the_third_reads_time, three_suffices f, the_bar_is_four_at_every_rung n, rfl⟩

/-- info: 'Foam.Counter.twelveness' does not depend on any axioms -/
#guard_msgs in #print axioms twelveness

end Foam.Counter
