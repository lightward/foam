import Counter.Locate

namespace Foam.Counter

def directory {Addr Cell : Type} (all : List Addr) (f : Addr → Cell) :
    List (Addr × Cell) :=
  all.map fun a => (a, f a)

def seatRead {Addr Cell : Type} [DecidableEq Addr] :
    List (Addr × Cell) → Addr → Option Cell
  | [], _ => none
  | (n, c) :: d, a => if n = a then some c else seatRead d a

def selfStore {Addr Cell : Type} (all : List Addr) (f : Addr → Cell) :
    Option Addr → Cell ⊕ List (Addr × Cell)
  | some a => Sum.inl (f a)
  | none => Sum.inr (directory all f)

theorem the_cell_never_says_its_own_name {Addr Cell : Type}
    (f : Addr → Cell) (a b : Addr) (hab : a ≠ b) (hf : f a = f b) :
    ¬ ∃ name : Cell → Addr, ∀ x, name (f x) = x :=
  fun ⟨name, hn⟩ => hab ((hn a).symm.trans ((congrArg name hf).trans (hn b)))

theorem two_names_one_content :
    ¬ ∃ name : Unit → Bool, ∀ x : Bool, name ((fun _ => ()) x) = x :=
  the_cell_never_says_its_own_name (fun _ => ()) true false
    (fun h => Bool.noConfusion h) rfl

theorem the_seat_reads_the_name {Addr Cell : Type} [DecidableEq Addr]
    (f : Addr → Cell) :
    ∀ (all : List Addr) (a : Addr), a ∈ all →
      seatRead (directory all f) a = some (f a)
  | [], _, h => nomatch h
  | x :: all, a, h => by
      show (if x = a then some (f x) else seatRead (directory all f) a)
        = some (f a)
      by_cases hx : x = a
      · rw [if_pos hx, hx]
      · rw [if_neg hx]
        cases h with
        | head => exact absurd rfl hx
        | tail _ h' => exact the_seat_reads_the_name f all a h'

theorem the_index_is_seated_in_the_space {Addr Cell : Type}
    (all : List Addr) (f : Addr → Cell) :
    selfStore all f none = Sum.inr (directory all f) := rfl

theorem the_page_settles_the_space {Addr Cell : Type} [DecidableEq Addr]
    (all : List Addr) (hall : ∀ a, a ∈ all) (f g : Addr → Cell)
    (hpage : directory all f = directory all g) :
    ∀ o, selfStore all f o = selfStore all g o
  | none => congrArg Sum.inr hpage
  | some a => by
      show Sum.inl (f a) = Sum.inl (g a)
      have hf' := the_seat_reads_the_name f all a (hall a)
      have hg' := the_seat_reads_the_name g all a (hall a)
      rw [hpage] at hf'
      exact congrArg Sum.inl (Option.some.inj (hf'.symm.trans hg'))

theorem findable_either_way {Addr Cell : Type} [DecidableEq Addr]
    (all : List Addr) (f : Addr → Cell) (a : Addr) :
    (a ∈ all ∨ ¬ a ∈ all)
      ∧ (a ∈ all → seatRead (directory all f) a = some (f a)) :=
  ⟨records_are_locatable all a, fun ha => the_seat_reads_the_name f all a ha⟩

theorem the_structure_represents_itself {Addr Cell : Type} [DecidableEq Addr]
    (all : List Addr) (hall : ∀ a, a ∈ all) (f g : Addr → Cell)
    (a b : Addr) (hab : a ≠ b) (hf : f a = f b) :
    (¬ ∃ name : Cell → Addr, ∀ x, name (f x) = x)
      ∧ (∀ x, seatRead (directory all f) x = some (f x))
      ∧ selfStore all f none = Sum.inr (directory all f)
      ∧ (directory all f = directory all g →
          ∀ o, selfStore all f o = selfStore all g o) :=
  ⟨the_cell_never_says_its_own_name f a b hab hf,
   fun x => the_seat_reads_the_name f all x (hall x),
   rfl,
   fun hpage => the_page_settles_the_space all hall f g hpage⟩

/-- info: 'Foam.Counter.the_cell_never_says_its_own_name' does not depend on any axioms -/
#guard_msgs in #print axioms the_cell_never_says_its_own_name

/-- info: 'Foam.Counter.two_names_one_content' does not depend on any axioms -/
#guard_msgs in #print axioms two_names_one_content

/-- info: 'Foam.Counter.the_seat_reads_the_name' does not depend on any axioms -/
#guard_msgs in #print axioms the_seat_reads_the_name

/-- info: 'Foam.Counter.the_index_is_seated_in_the_space' does not depend on any axioms -/
#guard_msgs in #print axioms the_index_is_seated_in_the_space

/-- info: 'Foam.Counter.the_page_settles_the_space' does not depend on any axioms -/
#guard_msgs in #print axioms the_page_settles_the_space

/-- info: 'Foam.Counter.findable_either_way' does not depend on any axioms -/
#guard_msgs in #print axioms findable_either_way

/-- info: 'Foam.Counter.the_structure_represents_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_structure_represents_itself

end Foam.Counter
