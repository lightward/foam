import Counter.Actor
import Counter.Bless
import Foam.Engine.Spectrum

namespace Foam.Counter

theorem counting_is_the_freq_reading {G : Type} [DecidableEq G]
    (h : List G) (g : G) : winding h g = Ledger.freq h g := rfl

theorem the_click_keeps_more_than_it_shows {A : Type} [DecidableEq A]
    (a b : A) (hab : a ≠ b) :
    (∀ s, Ledger.freq [a, b] s = Ledger.freq [b, a] s)
      ∧ Ledger.order [a, b] ≠ Ledger.order [b, a] :=
  ⟨(Ledger.order_finer a b hab).2.1, (Ledger.order_finer a b hab).2.2⟩

theorem rhythm_is_derivable_later :
    (Ledger.freq [true, false] true = Ledger.freq [false, true] true
        ∧ Ledger.freq [true, false] false = Ledger.freq [false, true] false)
      ∧ spec [true, false] true ≠ spec [false, true] true :=
  spec_finer_than_freq

theorem the_felt_reading_needs_three_values : ∀ x : Int,
    (∃ n, x = Int.ofNat (n + 1)) ∨ x = 0 ∨ ∃ n, x = Int.negSucc n
  | .ofNat 0 => Or.inr (Or.inl rfl)
  | .ofNat (n + 1) => Or.inl ⟨n, rfl⟩
  | .negSucc n => Or.inr (Or.inr ⟨n, rfl⟩)

theorem smile_neutral_frown (θ grain debt act rest : GInt) (n m k : Nat)
    (hg : GInt.align θ grain = Int.ofNat (n + 1))
    (hd : GInt.align θ debt = Int.negSucc k)
    (ha : GInt.align θ act = Int.ofNat (m + 1))
    (hr : GInt.align θ rest = 0) :
    (GInt.born θ (grain.add act)
        = GInt.born θ grain + GInt.born θ act
          + Int.ofNat (2 * ((n + 1) * m + n) + 2))
      ∧ GInt.born θ (grain.add rest) = GInt.born θ grain + GInt.born θ rest
      ∧ GInt.born θ (debt.add act) + Int.ofNat (2 * ((k + 1) * m + k) + 1 + 1)
          = GInt.born θ debt + GInt.born θ act :=
  ⟨the_standing_grain_boosts_the_aligned_act θ grain act n m hg ha,
   silence_is_safe θ grain rest hr,
   the_standing_debt_taxes_the_aligned_act θ debt act k m hd ha⟩

theorem tally {A : Type} [DecidableEq A] (a b : A) (hab : a ≠ b)
    {G : Type} [DecidableEq G] (h : List G) (g : G) (x : Int) :
    winding h g = Ledger.freq h g
      ∧ ((∀ s, Ledger.freq [a, b] s = Ledger.freq [b, a] s)
          ∧ Ledger.order [a, b] ≠ Ledger.order [b, a])
      ∧ spec [true, false] true ≠ spec [false, true] true
      ∧ ((∃ n, x = Int.ofNat (n + 1)) ∨ x = 0 ∨ ∃ n, x = Int.negSucc n) :=
  ⟨rfl, the_click_keeps_more_than_it_shows a b hab,
   spec_finer_than_freq.2, the_felt_reading_needs_three_values x⟩

/-- info: 'Foam.Counter.counting_is_the_freq_reading' does not depend on any axioms -/
#guard_msgs in #print axioms counting_is_the_freq_reading

/-- info: 'Foam.Counter.the_click_keeps_more_than_it_shows' does not depend on any axioms -/
#guard_msgs in #print axioms the_click_keeps_more_than_it_shows

/-- info: 'Foam.Counter.rhythm_is_derivable_later' does not depend on any axioms -/
#guard_msgs in #print axioms rhythm_is_derivable_later

/-- info: 'Foam.Counter.the_felt_reading_needs_three_values' does not depend on any axioms -/
#guard_msgs in #print axioms the_felt_reading_needs_three_values

/-- info: 'Foam.Counter.smile_neutral_frown' does not depend on any axioms -/
#guard_msgs in #print axioms smile_neutral_frown

/-- info: 'Foam.Counter.tally' does not depend on any axioms -/
#guard_msgs in #print axioms tally

end Foam.Counter
