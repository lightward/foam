import Foam.Seat.Octo

namespace Foam

def Ty12.d213 : Ty12 → Ty10
  | Foam.Ty12.c1 => Foam.Ty10.d060
  | Foam.Ty12.c2 => d092
  | Foam.Ty12.c3 => Foam.Ty10.d059
  | Foam.Ty12.c4 => Foam.Ty10.d172 Foam.Ty10.d059 d092

theorem Ty12.t430 (a b : Ty12) :
    (a * b).d213 = Foam.Ty10.d172 a.d213 b.d213 := by
  cases a <;> cases b <;> decide

theorem Ty12.t428 (a b : Ty12) :
    a.d213 = b.d213 → a = b := by
  cases a <;> cases b <;> decide

theorem Ty12.t429 : Foam.Ty12.d213 Foam.Ty12.c2 = d092 := rfl

/-- info: 'Foam.Ty12.t430' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t430

/-- info: 'Foam.Ty12.t428' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t428

end Foam
