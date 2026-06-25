import Foam.Seat.Triad

namespace Foam

theorem t472 :
    Foam.Ty10.d172 d092 d092 = Foam.Ty10.d059
      ∧ Foam.Ty10.d172 d097 d097 = Foam.Ty10.d059
      ∧ Foam.Ty10.d172 d224 d224 = Foam.Ty10.d059 :=
  t480

theorem t471 :
    Foam.Ty10.d172 d092 d097 = d224 ∧ Foam.Ty10.d172 d097 d224 = d092 ∧ Foam.Ty10.d172 d224 d092 = d097 :=
  t482

theorem t470 : Foam.Ty10.d172 d097 d092 = Foam.Ty10.d172 Foam.Ty10.d059 d224 :=
  t481

theorem t469 :
    (Foam.Ty10.d172 d092 d092 = Foam.Ty10.d059
        ∧ Foam.Ty10.d172 d097 d097 = Foam.Ty10.d059
        ∧ Foam.Ty10.d172 d224 d224 = Foam.Ty10.d059)
      ∧ (Foam.Ty10.d172 d092 d097 = d224 ∧ Foam.Ty10.d172 d097 d224 = d092 ∧ Foam.Ty10.d172 d224 d092 = d097)
      ∧ (Foam.Ty10.d172 d097 d092 = Foam.Ty10.d172 Foam.Ty10.d059 d224) :=
  ⟨t480, t482, t481⟩

/-- info: 'Foam.t472' does not depend on any axioms -/
#guard_msgs in #print axioms t472

/-- info: 'Foam.t471' does not depend on any axioms -/
#guard_msgs in #print axioms t471

/-- info: 'Foam.t470' does not depend on any axioms -/
#guard_msgs in #print axioms t470

/-- info: 'Foam.t469' does not depend on any axioms -/
#guard_msgs in #print axioms t469

end Foam
