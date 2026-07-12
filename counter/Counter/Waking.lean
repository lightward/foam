import Counter.Guard
import Counter.Nu

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem the_position_forgets_the_journey (S : Seat G) (h : List G) (p : S.Pos)
    (hnet : netAct h = 1) :
    S.replay h p = S.replay [] p :=
  a_settled_span_welcomes_any_pov S h hnet p

theorem the_record_remembers (S : Seat G) (acts : Nat → G) (p : S.Pos) :
    guardedBlock S acts p ≠ [] ∧ S.replay (guardedBlock S acts p) p = p :=
  ⟨(fun hnil => nomatch hnil), block_comes_home S acts p⟩

theorem home_is_learned_by_leaving (S : Seat G) (acts : Nat → G) (p : S.Pos) :
    (∀ h : List G, netAct h = 1 → S.replay h p = S.replay [] p)
      ∧ guardedBlock S acts p ≠ []
      ∧ S.replay (guardedBlock S acts p) p = p :=
  ⟨fun h hn => the_position_forgets_the_journey S h p hn,
   (the_record_remembers S acts p).1,
   (the_record_remembers S acts p).2⟩

/-- info: 'Foam.Counter.the_position_forgets_the_journey' does not depend on any axioms -/
#guard_msgs in #print axioms the_position_forgets_the_journey

/-- info: 'Foam.Counter.the_record_remembers' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_remembers

/-- info: 'Foam.Counter.home_is_learned_by_leaving' does not depend on any axioms -/
#guard_msgs in #print axioms home_is_learned_by_leaving

end Foam.Counter
