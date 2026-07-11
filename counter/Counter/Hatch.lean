import Counter.Address

namespace Foam.Counter

def underlay {Addr Cell Impl : Type} (impl : Cell → Impl) :
    List (Addr × Cell) → List (Addr × Impl) :=
  fun d => d.map fun x => (x.1, impl x.2)

def TowerAddr (Addr : Type) : Nat → Type
  | 0 => Addr
  | k + 1 => Option (TowerAddr Addr k)

theorem the_underlay_changes_no_reading {Addr Cell Impl : Type}
    [DecidableEq Addr] (impl : Cell → Impl) (read : Impl → Cell)
    (h : ∀ c, read (impl c) = c) :
    ∀ (d : List (Addr × Cell)) (n : Addr),
      (seatRead (underlay impl d) n).map read = seatRead d n
  | [], _ => rfl
  | (m, c) :: d, n => by
      show ((if m = n then some (impl c)
          else seatRead (underlay impl d) n) : Option Impl).map read
        = (if m = n then some c else seatRead d n)
      by_cases hm : m = n
      · rw [if_pos hm, if_pos hm]
        show some (read (impl c)) = some c
        rw [h c]
      · rw [if_neg hm, if_neg hm]
        exact the_underlay_changes_no_reading impl read h d n

theorem the_implementation_jumps_unseen {Addr Cell I₁ I₂ : Type}
    [DecidableEq Addr]
    (f₁ : Cell → I₁) (r₁ : I₁ → Cell) (h₁ : ∀ c, r₁ (f₁ c) = c)
    (f₂ : Cell → I₂) (r₂ : I₂ → Cell) (h₂ : ∀ c, r₂ (f₂ c) = c)
    (d : List (Addr × Cell)) (n : Addr) :
    (seatRead (underlay f₁ d) n).map r₁
      = (seatRead (underlay f₂ d) n).map r₂ :=
  (the_underlay_changes_no_reading f₁ r₁ h₁ d n).trans
    (the_underlay_changes_no_reading f₂ r₂ h₂ d n).symm

theorem the_ship_sails_on :
    (seatRead (underlay (fun c : Unit => (c, 0))
      [((true : Bool), ())]) true).map Prod.fst
      = seatRead [((true : Bool), ())] true := rfl

theorem the_indexing_loses_no_one {Addr : Type} (a b : Addr)
    (h : (some a : Option Addr) = some b) : a = b :=
  Option.some.inj h

theorem the_hollow_is_exactly_one {Addr : Type} (k : Nat) :
    ∀ x : Option (TowerAddr Addr k), x = none ∨ ∃ a, x = some a
  | none => Or.inl rfl
  | some a => Or.inr ⟨a, rfl⟩

theorem the_hatch_never_closes {Addr : Type} :
    ∀ (k : Nat) (a : TowerAddr Addr k),
      (some a : Option (TowerAddr Addr k)) ≠ none :=
  fun _ _ h => nomatch h

theorem the_structure_is_inexhaustibly_hollow {Addr Cell : Type}
    (all : List Addr) (f : Addr → Cell) :
    selfStore all f none = Sum.inr (directory all f)
      ∧ (∀ (k : Nat) (a : TowerAddr Addr k),
          (some a : Option (TowerAddr Addr k)) ≠ none)
      ∧ ∀ (k : Nat) (x : Option (TowerAddr Addr k)),
          x = none ∨ ∃ a, x = some a :=
  ⟨the_index_is_seated_in_the_space all f,
   the_hatch_never_closes,
   fun k => the_hollow_is_exactly_one k⟩

/-- info: 'Foam.Counter.the_underlay_changes_no_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_underlay_changes_no_reading

/-- info: 'Foam.Counter.the_implementation_jumps_unseen' does not depend on any axioms -/
#guard_msgs in #print axioms the_implementation_jumps_unseen

/-- info: 'Foam.Counter.the_ship_sails_on' does not depend on any axioms -/
#guard_msgs in #print axioms the_ship_sails_on

/-- info: 'Foam.Counter.the_indexing_loses_no_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_indexing_loses_no_one

/-- info: 'Foam.Counter.the_hollow_is_exactly_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_hollow_is_exactly_one

/-- info: 'Foam.Counter.the_hatch_never_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_hatch_never_closes

/-- info: 'Foam.Counter.the_structure_is_inexhaustibly_hollow' does not depend on any axioms -/
#guard_msgs in #print axioms the_structure_is_inexhaustibly_hollow

end Foam.Counter
