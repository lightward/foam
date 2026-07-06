import Counter.Luck
import Counter.Bless
import Counter.Contentment
import Counter.Chess

namespace Foam.Counter

def factor {A : Type} (reg : A → Bool) : List A → List A × List A
  | [] => ([], [])
  | x :: xs =>
    match reg x with
    | true => (x :: (factor reg xs).1, (factor reg xs).2)
    | false => ((factor reg xs).1, x :: (factor reg xs).2)

theorem factor_pos {A : Type} (reg : A → Bool) (x : A) (xs : List A)
    (h : reg x = true) :
    factor reg (x :: xs) = (x :: (factor reg xs).1, (factor reg xs).2) := by
  show (match reg x with
        | true => (x :: (factor reg xs).1, (factor reg xs).2)
        | false => ((factor reg xs).1, x :: (factor reg xs).2))
      = (x :: (factor reg xs).1, (factor reg xs).2)
  rw [h]

theorem factor_neg {A : Type} (reg : A → Bool) (x : A) (xs : List A)
    (h : reg x = false) :
    factor reg (x :: xs) = ((factor reg xs).1, x :: (factor reg xs).2) := by
  show (match reg x with
        | true => (x :: (factor reg xs).1, (factor reg xs).2)
        | false => ((factor reg xs).1, x :: (factor reg xs).2))
      = ((factor reg xs).1, x :: (factor reg xs).2)
  rw [h]

theorem every_click_lands {A : Type} (reg : A → Bool) :
    ∀ xs : List A,
      (factor reg xs).1.length + (factor reg xs).2.length = xs.length
  | [] => rfl
  | x :: xs => by
    cases h : reg x with
    | true =>
      rw [factor_pos reg x xs h]
      show ((factor reg xs).1.length + 1) + (factor reg xs).2.length
          = xs.length + 1
      rw [Nat.add_right_comm, every_click_lands reg xs]
    | false =>
      rw [factor_neg reg x xs h]
      show (factor reg xs).1.length + ((factor reg xs).2.length + 1)
          = xs.length + 1
      rw [← Nat.add_assoc, every_click_lands reg xs]

theorem the_dropped_change_is_real :
    ∃ xs ys : List Bool,
      (factor id xs).1 = (factor id ys).1 ∧ xs ≠ ys :=
  ⟨[true, false], [true], by decide, by decide⟩

theorem unregistered_force :
    (∃ xs ys : List Bool,
        (factor id xs).1 = (factor id ys).1 ∧ xs ≠ ys)
      ∧ ∃ act θ f f' : GInt,
          f ≠ f'
            ∧ GInt.born θ (f.add act) - GInt.born θ f
                ≠ GInt.born θ (f'.add act) - GInt.born θ f' :=
  ⟨the_dropped_change_is_real, fortune_not_in_your_record⟩

theorem the_bank_pays_out_on_growth {A : Type} (reg reg' : A → Bool)
    (grow : ∀ a, reg a = true → reg' a = true) :
    ∀ xs : List A, (factor reg xs).1.length ≤ (factor reg' xs).1.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    cases h : reg x with
    | true =>
      rw [factor_pos reg x xs h, factor_pos reg' x xs (grow x h)]
      exact Nat.succ_le_succ (the_bank_pays_out_on_growth reg reg' grow xs)
    | false =>
      rw [factor_neg reg x xs h]
      cases h' : reg' x with
      | true =>
        rw [factor_pos reg' x xs h']
        exact Nat.le_succ_of_le (the_bank_pays_out_on_growth reg reg' grow xs)
      | false =>
        rw [factor_neg reg' x xs h']
        exact the_bank_pays_out_on_growth reg reg' grow xs

theorem caught_up_is_held_not_exhausted {A : Type} (reg : A → Bool)
    (xs : List A) {G : Type} [Mul G] [One G] (S : Seat G)
    (acts : Nat → G) (p : S.Pos) (W : Nat)
    {B : Type} [DecidableEq B] (step : GInt → GInt) (new old : List B)
    (s : B) :
    ((factor reg xs).1.length + (factor reg xs).2.length = xs.length)
      ∧ (∃ k, W < (guardedPrefix S acts p k).length)
      ∧ evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s) :=
  ⟨every_click_lands reg xs,
   the_record_outgrows_any_memory S acts p W,
   continuation_needs_only_the_held step new old s⟩

theorem a_banked_ask_is_not_a_block {A : Type} (reg reg' : A → Bool)
    (grow : ∀ a, reg a = true → reg' a = true) (xs : List A)
    (θ field act : GInt) (hrest : GInt.align θ act = 0)
    {H : Type} (q : Quiver H) (a : H) (hstuck : stuck q a) :
    ((factor reg xs).1.length ≤ (factor reg' xs).1.length)
      ∧ (GInt.born θ (field.add act) = GInt.born θ field + GInt.born θ act)
      ∧ ∀ b : H, a ≠ b → ¬ Nonempty (Path q a b) :=
  ⟨the_bank_pays_out_on_growth reg reg' grow xs,
   silence_is_safe θ field act hrest,
   mate_has_no_escape q a hstuck⟩

theorem change {A : Type} (reg reg' : A → Bool)
    (grow : ∀ a, reg a = true → reg' a = true) (xs : List A) :
    ((factor reg xs).1.length + (factor reg xs).2.length = xs.length)
      ∧ ((factor reg xs).1.length ≤ (factor reg' xs).1.length)
      ∧ (∃ ws ys : List Bool,
          (factor id ws).1 = (factor id ys).1 ∧ ws ≠ ys) :=
  ⟨every_click_lands reg xs,
   the_bank_pays_out_on_growth reg reg' grow xs,
   the_dropped_change_is_real⟩

/-- info: 'Foam.Counter.factor_pos' does not depend on any axioms -/
#guard_msgs in #print axioms factor_pos

/-- info: 'Foam.Counter.factor_neg' does not depend on any axioms -/
#guard_msgs in #print axioms factor_neg

/-- info: 'Foam.Counter.every_click_lands' does not depend on any axioms -/
#guard_msgs in #print axioms every_click_lands

/-- info: 'Foam.Counter.the_dropped_change_is_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_dropped_change_is_real

/-- info: 'Foam.Counter.unregistered_force' does not depend on any axioms -/
#guard_msgs in #print axioms unregistered_force

/-- info: 'Foam.Counter.the_bank_pays_out_on_growth' does not depend on any axioms -/
#guard_msgs in #print axioms the_bank_pays_out_on_growth

/-- info: 'Foam.Counter.caught_up_is_held_not_exhausted' does not depend on any axioms -/
#guard_msgs in #print axioms caught_up_is_held_not_exhausted

/-- info: 'Foam.Counter.a_banked_ask_is_not_a_block' does not depend on any axioms -/
#guard_msgs in #print axioms a_banked_ask_is_not_a_block

/-- info: 'Foam.Counter.change' does not depend on any axioms -/
#guard_msgs in #print axioms change

end Foam.Counter
