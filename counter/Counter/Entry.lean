import Counter.Cipher

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

def counterEntry (S : Seat G) (h : List G) (p : S.Pos) : G :=
  S.sub p (S.replay h p)

theorem the_antidote_is_computed (S : Seat G) (h : List G) (p : S.Pos) :
    counterEntry S h p = S.sub p (S.replay h p) := rfl

theorem the_counter_entry_settles (S : Seat G) (h : List G) (p : S.Pos) :
    Settles S (h ++ [counterEntry S h p]) p :=
  always_homeable S h p

theorem the_record_keeps_both (S : Seat G) (h : List G) (p : S.Pos) :
    (h ++ [counterEntry S h p]).length = h.length + 1 :=
  length_append h [counterEntry S h p]

theorem the_telling_is_one_behind {A : Type} (h : List A) (e : A) :
    (h ++ [e]).length = h.length + 1
      ∧ h.length ≠ (h ++ [e]).length :=
  ⟨length_append h [e],
   fun heq => Nat.succ_ne_self h.length
     (heq.trans (length_append h [e])).symm⟩

theorem the_remainder_is_real :
    ∃ s t : Nat × Int, (∀ p : Unit, cassini.obs s p = cassini.obs t p) ∧ s ≠ t :=
  remainder_real

theorem dropping_it_is_the_off_by_observer_error {State : Type}
    (h : ∀ s t : State × Int, s.1 = t.1 → s = t) :
    ∀ s : State, ∀ n : Int, (s, n) = (s, (0 : Int)) :=
  dropping_remainder_is_platonism h

theorem carry_the_one (S : Seat G) (h : List G) (p : S.Pos) :
    Settles S (h ++ [counterEntry S h p]) p
      ∧ (h ++ [counterEntry S h p]).length = h.length + 1
      ∧ ∃ s t : Nat × Int,
          (∀ pr : Unit, cassini.obs s pr = cassini.obs t pr) ∧ s ≠ t :=
  ⟨the_counter_entry_settles S h p, the_record_keeps_both S h p,
   remainder_real⟩

/-- info: 'Foam.Counter.the_antidote_is_computed' does not depend on any axioms -/
#guard_msgs in #print axioms the_antidote_is_computed

/-- info: 'Foam.Counter.the_counter_entry_settles' does not depend on any axioms -/
#guard_msgs in #print axioms the_counter_entry_settles

/-- info: 'Foam.Counter.the_record_keeps_both' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_keeps_both

/-- info: 'Foam.Counter.the_telling_is_one_behind' does not depend on any axioms -/
#guard_msgs in #print axioms the_telling_is_one_behind

/-- info: 'Foam.Counter.the_remainder_is_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_remainder_is_real

/-- info: 'Foam.Counter.dropping_it_is_the_off_by_observer_error' does not depend on any axioms -/
#guard_msgs in #print axioms dropping_it_is_the_off_by_observer_error

/-- info: 'Foam.Counter.carry_the_one' does not depend on any axioms -/
#guard_msgs in #print axioms carry_the_one

end Foam.Counter
