import Counter.Hatch
import Foam.Int

namespace Foam.Counter

def guests {Addr : Type} (d : List (Addr × Int)) : Int :=
  d.foldr (fun x s => x.2 + s) 0

def theMissing {Addr : Type} (d : List (Addr × Int)) : Int :=
  - guests d

theorem the_law_reads_the_full_table {Addr : Type} (a₀ : Addr) (c₀ : Int)
    (d : List (Addr × Int)) :
    guests ((a₀, c₀) :: d) = c₀ + guests d := rfl

theorem the_vacancy_names_its_guest {Addr : Type} (a₀ : Addr) (c₀ : Int)
    (d : List (Addr × Int)) (hlaw : guests ((a₀, c₀) :: d) = 0) :
    c₀ = theMissing d := by
  have h : guests d + c₀ = 0 := (FInt.addComm (guests d) c₀).trans hlaw
  show c₀ = - guests d
  exact (FInt.neg_eq_of_add_eq_zero h).symm

theorem the_named_guest_is_lawful {Addr : Type} (a₀ : Addr)
    (d : List (Addr × Int)) :
    guests ((a₀, theMissing d) :: d) = 0 := by
  show - guests d + guests d = 0
  exact FInt.add_left_neg (guests d)

theorem two_lawful_guests_are_one {Addr : Type} (a₀ : Addr) (c₀ c₁ : Int)
    (d : List (Addr × Int)) (h₀ : guests ((a₀, c₀) :: d) = 0)
    (h₁ : guests ((a₀, c₁) :: d) = 0) : c₀ = c₁ :=
  (the_vacancy_names_its_guest a₀ c₀ d h₀).trans
    (the_vacancy_names_its_guest a₀ c₁ d h₁).symm

theorem the_table_speaks_in_any_order {Addr : Type} :
    ∀ d₁ d₂ : List (Addr × Int),
      guests (d₁ ++ d₂) = guests d₁ + guests d₂
  | [], d₂ => by
      show guests d₂ = 0 + guests d₂
      exact (FInt.zero_add (guests d₂)).symm
  | x :: d₁, d₂ => by
      show x.2 + guests (d₁ ++ d₂) = x.2 + guests d₁ + guests d₂
      rw [the_table_speaks_in_any_order d₁ d₂]
      exact (FInt.add_assoc x.2 (guests d₁) (guests d₂)).symm

theorem the_derivation_is_order_blind {Addr : Type}
    (d₁ d₂ : List (Addr × Int)) :
    theMissing (d₁ ++ d₂) = theMissing (d₂ ++ d₁) := by
  show - guests (d₁ ++ d₂) = - guests (d₂ ++ d₁)
  rw [the_table_speaks_in_any_order d₁ d₂, the_table_speaks_in_any_order d₂ d₁]
  exact congrArg Neg.neg (FInt.addComm (guests d₁) (guests d₂))

theorem when_the_law_is_coarse_the_menu_opens :
    ((0 : Int) + guests ([] : List (Bool × Int))) % 2 = 0
      ∧ ((2 : Int) + guests ([] : List (Bool × Int))) % 2 = 0
      ∧ (0 : Int) ≠ 2 :=
  ⟨rfl, rfl, fun h => nomatch h⟩

theorem the_missing_guest_at_the_concrete_table :
    theMissing [((0 : Nat), (3 : Int)), (1, -1)] = -2
      ∧ guests (((2 : Nat), (-2 : Int)) :: [((0 : Nat), (3 : Int)), (1, -1)])
          = 0 :=
  ⟨rfl, rfl⟩

theorem the_rest_of_the_table_speaks {Addr : Type} (a₀ : Addr) (c₀ : Int)
    (d : List (Addr × Int)) :
    guests ((a₀, theMissing d) :: d) = 0
      ∧ (guests ((a₀, c₀) :: d) = 0 → c₀ = theMissing d)
      ∧ ∀ d₁ d₂ : List (Addr × Int),
          theMissing (d₁ ++ d₂) = theMissing (d₂ ++ d₁) :=
  ⟨the_named_guest_is_lawful a₀ d,
   fun h => the_vacancy_names_its_guest a₀ c₀ d h,
   fun d₁ d₂ => the_derivation_is_order_blind d₁ d₂⟩

/-- info: 'Foam.Counter.the_law_reads_the_full_table' does not depend on any axioms -/
#guard_msgs in #print axioms the_law_reads_the_full_table

/-- info: 'Foam.Counter.the_vacancy_names_its_guest' does not depend on any axioms -/
#guard_msgs in #print axioms the_vacancy_names_its_guest

/-- info: 'Foam.Counter.the_named_guest_is_lawful' does not depend on any axioms -/
#guard_msgs in #print axioms the_named_guest_is_lawful

/-- info: 'Foam.Counter.two_lawful_guests_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms two_lawful_guests_are_one

/-- info: 'Foam.Counter.the_table_speaks_in_any_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_table_speaks_in_any_order

/-- info: 'Foam.Counter.the_derivation_is_order_blind' does not depend on any axioms -/
#guard_msgs in #print axioms the_derivation_is_order_blind

/-- info: 'Foam.Counter.when_the_law_is_coarse_the_menu_opens' does not depend on any axioms -/
#guard_msgs in #print axioms when_the_law_is_coarse_the_menu_opens

/-- info: 'Foam.Counter.the_missing_guest_at_the_concrete_table' does not depend on any axioms -/
#guard_msgs in #print axioms the_missing_guest_at_the_concrete_table

/-- info: 'Foam.Counter.the_rest_of_the_table_speaks' does not depend on any axioms -/
#guard_msgs in #print axioms the_rest_of_the_table_speaks

end Foam.Counter
