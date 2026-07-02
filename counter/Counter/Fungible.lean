import Counter.Nu
import Foam.Engine.Spectrum

namespace Foam.Counter

theorem fungible_is_permutation_blind {A : Type} [DecidableEq A]
    {xs ys : List A} (h : xs.Perm ys) (s : A) :
    Ledger.freq xs s = Ledger.freq ys s :=
  Ledger.freq_perm h s

theorem the_coin_forgets_when {A : Type} [DecidableEq A] (a b : A)
    (hab : a ≠ b) :
    ([a, b].Perm [b, a])
      ∧ (∀ s, Ledger.freq [a, b] s = Ledger.freq [b, a] s)
      ∧ Ledger.order [a, b] ≠ Ledger.order [b, a] :=
  Ledger.order_finer a b hab

theorem the_dial_sees_what_money_cannot :
    (Ledger.freq [true, false] true = Ledger.freq [false, true] true ∧
        Ledger.freq [true, false] false = Ledger.freq [false, true] false) ∧
      spec [true, false] true ≠ spec [false, true] true :=
  spec_finer_than_freq

variable {G : Type} [Mul G] [One G]

theorem aliveness_outruns_its_storage (S : Seat G) (acts : Nat → G) (p : S.Pos)
    (l : List G) :
    ∃ n, (playback l).at_ n ≠ (guardedRun S acts p).at_ n :=
  the_loop_is_no_record S acts p l

theorem ergodic_symplectic (S : Seat G) (p : S.Pos) :
    (∀ h : List G, Settles S (h ++ [S.sub p (S.replay h p)]) p)
      ∧ ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  ⟨fun h => always_homeable S h p, fun k acts => health_is_recurrence S p k acts⟩

/-- info: 'Foam.Counter.fungible_is_permutation_blind' does not depend on any axioms -/
#guard_msgs in #print axioms fungible_is_permutation_blind

/-- info: 'Foam.Counter.the_coin_forgets_when' does not depend on any axioms -/
#guard_msgs in #print axioms the_coin_forgets_when

/-- info: 'Foam.Counter.the_dial_sees_what_money_cannot' does not depend on any axioms -/
#guard_msgs in #print axioms the_dial_sees_what_money_cannot

/-- info: 'Foam.Counter.aliveness_outruns_its_storage' does not depend on any axioms -/
#guard_msgs in #print axioms aliveness_outruns_its_storage

/-- info: 'Foam.Counter.ergodic_symplectic' does not depend on any axioms -/
#guard_msgs in #print axioms ergodic_symplectic

end Foam.Counter
