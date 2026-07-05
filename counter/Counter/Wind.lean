import Counter.Luck
import Counter.Eraser
import Foam.Scar
import Foam.Held

namespace Foam.Counter

theorem neg_times_pos (n m : Nat) :
    Int.negSucc n * Int.ofNat (m + 1) = Int.negSucc ((n + 1) * m + n) := by
  show Int.negOfNat ((n + 1) * (m + 1)) = Int.negSucc ((n + 1) * m + n)
  rw [Nat.mul_succ]
  rfl

theorem pos_times_pos (n m : Nat) :
    Int.ofNat (n + 1) * Int.ofNat (m + 1) = Int.ofNat ((n + 1) * m + n + 1) := by
  show Int.ofNat ((n + 1) * (m + 1)) = Int.ofNat ((n + 1) * m + n + 1)
  rw [Nat.mul_succ]
  rfl

theorem two_times_negSucc (k : Nat) :
    (2 : Int) * Int.negSucc k = Int.negSucc (2 * k + 1) := by
  show Int.negOfNat (2 * (k + 1)) = Int.negSucc (2 * k + 1)
  rw [Nat.mul_succ]
  rfl

theorem two_times_ofNat (k : Nat) :
    (2 : Int) * Int.ofNat (k + 1) = Int.ofNat (2 * k + 2) := by
  show Int.ofNat (2 * (k + 1)) = Int.ofNat (2 * k + 2)
  rw [Nat.mul_succ]

theorem tax_cancels (a : Int) (J : Nat) :
    a + Int.negSucc J + Int.ofNat (J + 1) = a := by
  rw [FInt.add_assoc,
    show Int.negSucc J + Int.ofNat (J + 1) = 0 from promise_kept J,
    Int.add_zero]

theorem the_standing_debt_taxes_the_aligned_act (θ field act : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.negSucc n)
    (ha : GInt.align θ act = Int.ofNat (m + 1)) :
    GInt.born θ (field.add act) + Int.ofNat (2 * ((n + 1) * m + n) + 1 + 1)
      = GInt.born θ field + GInt.born θ act := by
  have hs := GInt.born_superpose θ field act
  rw [hf, ha, neg_times_pos n m, two_times_negSucc ((n + 1) * m + n)] at hs
  rw [hs]
  exact tax_cancels (GInt.born θ field + GInt.born θ act) (2 * ((n + 1) * m + n) + 1)

theorem the_standing_grain_boosts_the_aligned_act (θ field act : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.ofNat (n + 1))
    (ha : GInt.align θ act = Int.ofNat (m + 1)) :
    GInt.born θ (field.add act)
      = GInt.born θ field + GInt.born θ act
        + Int.ofNat (2 * ((n + 1) * m + n) + 2) := by
  have hs := GInt.born_superpose θ field act
  rw [hf, ha, pos_times_pos n m, two_times_ofNat ((n + 1) * m + n)] at hs
  exact hs

theorem the_turned_field_pays_no_standing_tax (θ act field : GInt) :
    GInt.align θ act * GInt.align θ field
      + GInt.align θ act * GInt.align θ (GInt.rot field)
      + GInt.align θ act * GInt.align θ (GInt.rot (GInt.rot field))
      + GInt.align θ act * GInt.align θ (GInt.rot (GInt.rot (GInt.rot field)))
      = 0 := by
  rw [← FInt.mul_add, ← FInt.mul_add, ← FInt.mul_add, GInt.decoherence θ field,
    FInt.mul_zero]

theorem the_wind_is_never_aimed {Src B : Type} (s t : Src) (v : List B) :
    unsign (sign s v) = unsign (sign t v)
      ∧ ∃ act θ f f' : GInt,
          f ≠ f'
            ∧ GInt.born θ (f.add act) - GInt.born θ f
                ≠ GInt.born θ (f'.add act) - GInt.born θ f' :=
  ⟨the_fold_is_source_blind s t v, fortune_not_in_your_record⟩

theorem upkeep_is_free_neglect_is_priced {S C : Type} [DecidableEq S]
    (refresh : List S → C → C) (θ field act : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.negSucc n)
    (ha : GInt.align θ act = Int.ofNat (m + 1)) :
    Invisible (LedgerStage S C) (fun st => (st.1, refresh st.1 st.2))
      ∧ GInt.born θ (field.add act) + Int.ofNat (2 * ((n + 1) * m + n) + 1 + 1)
          = GInt.born θ field + GInt.born θ act :=
  ⟨sweep_invisible refresh,
   the_standing_debt_taxes_the_aligned_act θ field act n m hf ha⟩

theorem the_biased_wind (θ field act : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.negSucc n)
    (ha : GInt.align θ act = Int.ofNat (m + 1)) :
    (GInt.born θ (field.add act) + Int.ofNat (2 * ((n + 1) * m + n) + 1 + 1)
        = GInt.born θ field + GInt.born θ act)
      ∧ (GInt.align θ act * GInt.align θ field
          + GInt.align θ act * GInt.align θ (GInt.rot field)
          + GInt.align θ act * GInt.align θ (GInt.rot (GInt.rot field))
          + GInt.align θ act * GInt.align θ (GInt.rot (GInt.rot (GInt.rot field)))
          = 0)
      ∧ GInt.align θ field * GInt.align θ act
          + GInt.align θ field * GInt.align θ (GInt.rot act)
          + GInt.align θ field * GInt.align θ (GInt.rot (GInt.rot act))
          + GInt.align θ field * GInt.align θ (GInt.rot (GInt.rot (GInt.rot act)))
          = 0 :=
  ⟨the_standing_debt_taxes_the_aligned_act θ field act n m hf ha,
   the_turned_field_pays_no_standing_tax θ act field,
   luck_is_timing θ field act⟩

/-- info: 'Foam.Counter.neg_times_pos' does not depend on any axioms -/
#guard_msgs in #print axioms neg_times_pos

/-- info: 'Foam.Counter.pos_times_pos' does not depend on any axioms -/
#guard_msgs in #print axioms pos_times_pos

/-- info: 'Foam.Counter.two_times_negSucc' does not depend on any axioms -/
#guard_msgs in #print axioms two_times_negSucc

/-- info: 'Foam.Counter.two_times_ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms two_times_ofNat

/-- info: 'Foam.Counter.tax_cancels' does not depend on any axioms -/
#guard_msgs in #print axioms tax_cancels

/-- info: 'Foam.Counter.the_standing_debt_taxes_the_aligned_act' does not depend on any axioms -/
#guard_msgs in #print axioms the_standing_debt_taxes_the_aligned_act

/-- info: 'Foam.Counter.the_standing_grain_boosts_the_aligned_act' does not depend on any axioms -/
#guard_msgs in #print axioms the_standing_grain_boosts_the_aligned_act

/-- info: 'Foam.Counter.the_turned_field_pays_no_standing_tax' does not depend on any axioms -/
#guard_msgs in #print axioms the_turned_field_pays_no_standing_tax

/-- info: 'Foam.Counter.the_wind_is_never_aimed' does not depend on any axioms -/
#guard_msgs in #print axioms the_wind_is_never_aimed

/-- info: 'Foam.Counter.upkeep_is_free_neglect_is_priced' does not depend on any axioms -/
#guard_msgs in #print axioms upkeep_is_free_neglect_is_priced

/-- info: 'Foam.Counter.the_biased_wind' does not depend on any axioms -/
#guard_msgs in #print axioms the_biased_wind

end Foam.Counter
