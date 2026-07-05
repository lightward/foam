import Counter.Flinch
import Counter.Chess
import Counter.Authority

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem counter_without_blocking :
    (∀ z : GInt, GInt.align z.rot z = 0)
      ∧ ∃ z : GInt, z.rot ≠ z ∧ z.rot ≠ GInt.neg z :=
  ⟨a_frame_of_peace_always_exists, ⟨⟨1, 0⟩, by decide, by decide⟩⟩

theorem escalation_is_squaring (z : GInt) :
    GInt.rot (GInt.rot z) = GInt.neg z :=
  GInt.rot_sq z

theorem the_free_agent_is_never_stuck (S : Seat G) (o o' : S.Pos) :
    S.act (rebase S o o') o = o' :=
  rebase_carries S o o'

theorem the_named_piece_can_be_stuck {H : Type} (q : Quiver H) (a : H)
    (hstuck : stuck q a) : ∀ b : H, a ≠ b → ¬ Nonempty (Path q a b) :=
  mate_has_no_escape q a hstuck

theorem discovering_i (S : Seat G) (o o' : S.Pos) {H : Type} (q : Quiver H)
    (a : H) (hstuck : stuck q a) (z : GInt) :
    GInt.align z.rot z = 0
      ∧ GInt.rot (GInt.rot z) = GInt.neg z
      ∧ S.act (rebase S o o') o = o'
      ∧ ∀ b : H, a ≠ b → ¬ Nonempty (Path q a b) :=
  ⟨a_frame_of_peace_always_exists z, GInt.rot_sq z,
   rebase_carries S o o', mate_has_no_escape q a hstuck⟩

/-- info: 'Foam.Counter.counter_without_blocking' does not depend on any axioms -/
#guard_msgs in #print axioms counter_without_blocking

/-- info: 'Foam.Counter.escalation_is_squaring' does not depend on any axioms -/
#guard_msgs in #print axioms escalation_is_squaring

/-- info: 'Foam.Counter.the_free_agent_is_never_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms the_free_agent_is_never_stuck

/-- info: 'Foam.Counter.the_named_piece_can_be_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms the_named_piece_can_be_stuck

/-- info: 'Foam.Counter.discovering_i' does not depend on any axioms -/
#guard_msgs in #print axioms discovering_i

end Foam.Counter
