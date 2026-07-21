import Foam.Ledger

namespace Foam

theorem nothing_added : ∀ n : Nat, 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (nothing_added n)

theorem adding_associates : ∀ a b c : Nat, a + (b + c) = (a + b) + c
  | _, _, 0 => rfl
  | a, b, c + 1 => congrArg Nat.succ (adding_associates a b c)

theorem succ_adds : ∀ a b : Nat, (a + 1) + b = (a + b) + 1
  | _, 0 => rfl
  | a, b + 1 => congrArg Nat.succ (succ_adds a b)

theorem the_count_adds {A : Type} [DecidableEq A] (a : A) :
    ∀ xs ys : List A, freq (xs ++ ys) a = freq xs a + freq ys a
  | [], ys => (nothing_added (freq ys a)).symm
  | x :: xs, ys => by
      show (if x = a then 1 else 0) + freq (xs ++ ys) a
          = ((if x = a then 1 else 0) + freq xs a) + freq ys a
      rw [the_count_adds a xs ys, adding_associates]

theorem the_mass_adds {A : Type} :
    ∀ xs ys : List A, (xs ++ ys).length = xs.length + ys.length
  | [], ys => (nothing_added ys.length).symm
  | _ :: xs, ys => by
      show (xs ++ ys).length + 1 = (xs.length + 1) + ys.length
      rw [the_mass_adds xs ys, succ_adds]

theorem measure_begins_at_the_count {A : Type} [DecidableEq A]
    (a : A) (xs ys : List A) :
    freq (xs ++ ys) a = freq xs a + freq ys a
      ∧ (xs ++ ys).length = xs.length + ys.length :=
  ⟨the_count_adds a xs ys, the_mass_adds xs ys⟩

/-- info: 'Foam.nothing_added' does not depend on any axioms -/
#guard_msgs in #print axioms nothing_added

/-- info: 'Foam.adding_associates' does not depend on any axioms -/
#guard_msgs in #print axioms adding_associates

/-- info: 'Foam.succ_adds' does not depend on any axioms -/
#guard_msgs in #print axioms succ_adds

/-- info: 'Foam.the_count_adds' does not depend on any axioms -/
#guard_msgs in #print axioms the_count_adds

/-- info: 'Foam.the_mass_adds' does not depend on any axioms -/
#guard_msgs in #print axioms the_mass_adds

/-- info: 'Foam.measure_begins_at_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms measure_begins_at_the_count

end Foam
