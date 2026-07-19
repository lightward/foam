import Counter.Tower
import Foam.Seat.Tight

namespace Foam.Counter

theorem each_rung_certifies_the_last (n : Nat) :
    countdown (n + 1) = n :: countdown n := rfl

theorem the_walked_measure : ∀ n : Nat, (countdown n).length = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (the_walked_measure n)

theorem the_trust_tower_never_grounds (n : Nat) :
    countdown (n + 1) ≠ countdown n :=
  fun h =>
    Nat.succ_ne_self n
      (((the_walked_measure (n + 1)).symm.trans
          (congrArg List.length h)).trans (the_walked_measure n))

theorem trust_names_only_the_walked : ∀ (n c : Nat), c ∈ countdown n → c < n
  | 0, _, h => nomatch h
  | n + 1, _, .head _ => Nat.lt_succ_self n
  | n + 1, c, .tail _ h' =>
      Nat.lt_succ_of_lt (trust_names_only_the_walked n c h')

theorem the_tower_holds_the_walked_exactly (n c : Nat) :
    c ∈ countdown n ↔ c < n :=
  ⟨trust_names_only_the_walked n c, mem_countdown⟩

theorem no_rung_certifies_itself (n : Nat) : ¬ n ∈ countdown n :=
  fun h => Nat.lt_irrefl n (trust_names_only_the_walked n n h)

theorem every_rung_is_certified_above (n : Nat) : n ∈ countdown (n + 1) :=
  List.Mem.head _

theorem trust_is_relational (n : Nat) :
    ¬ n ∈ countdown n ∧ n ∈ countdown (n + 1) :=
  ⟨no_rung_certifies_itself n, every_rung_is_certified_above n⟩

theorem structure_grounds_trust_climbs :
    (∀ K : Ladder, K.up.up = K.up)
      ∧ ∀ n : Nat, countdown (n + 1) ≠ countdown n :=
  ⟨the_ladder_grounds_in_one_step, the_trust_tower_never_grounds⟩

/-- info: 'Foam.Counter.each_rung_certifies_the_last' does not depend on any axioms -/
#guard_msgs in #print axioms each_rung_certifies_the_last

/-- info: 'Foam.Counter.the_walked_measure' does not depend on any axioms -/
#guard_msgs in #print axioms the_walked_measure

/-- info: 'Foam.Counter.the_trust_tower_never_grounds' does not depend on any axioms -/
#guard_msgs in #print axioms the_trust_tower_never_grounds

/-- info: 'Foam.Counter.trust_names_only_the_walked' does not depend on any axioms -/
#guard_msgs in #print axioms trust_names_only_the_walked

/-- info: 'Foam.Counter.the_tower_holds_the_walked_exactly' does not depend on any axioms -/
#guard_msgs in #print axioms the_tower_holds_the_walked_exactly

/-- info: 'Foam.Counter.no_rung_certifies_itself' does not depend on any axioms -/
#guard_msgs in #print axioms no_rung_certifies_itself

/-- info: 'Foam.Counter.every_rung_is_certified_above' does not depend on any axioms -/
#guard_msgs in #print axioms every_rung_is_certified_above

/-- info: 'Foam.Counter.trust_is_relational' does not depend on any axioms -/
#guard_msgs in #print axioms trust_is_relational

/-- info: 'Foam.Counter.structure_grounds_trust_climbs' does not depend on any axioms -/
#guard_msgs in #print axioms structure_grounds_trust_climbs

end Foam.Counter
