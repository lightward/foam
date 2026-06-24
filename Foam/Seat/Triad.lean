import Foam.Seat.Doubling

namespace Foam

theorem t482 :
    Foam.Ty10.d172 d092 d097 = d224
      ∧ Foam.Ty10.d172 d097 d224 = d092
      ∧ Foam.Ty10.d172 d224 d092 = d097 := by decide

theorem t481 : Foam.Ty10.d172 d097 d092 = Foam.Ty10.d172 Foam.Ty10.d059 d224 := by decide

theorem t461 : Foam.Ty10.d172 (Foam.Ty10.d172 d092 d097) d224 = Foam.Ty10.d059 := by decide

/-- info: 'Foam.t482' does not depend on any axioms -/
#guard_msgs in #print axioms t482

/-- info: 'Foam.t481' does not depend on any axioms -/
#guard_msgs in #print axioms t481

/-- info: 'Foam.t461' does not depend on any axioms -/
#guard_msgs in #print axioms t461

end Foam
