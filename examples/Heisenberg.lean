import Foam.Seat.Forcing

namespace Foam

theorem t296 (z w : Ty05) :
    Foam.Ty05.d109 z w * Foam.Ty05.d109 z w + Foam.Ty05.d111 z w * Foam.Ty05.d111 z w
      = z.d114 * w.d114 :=
  t302 z w

theorem t295 (w z : Ty05) :
    Foam.Ty05.d111 w.d115 z.d115 = Foam.Ty05.d111 w z :=
  t276 w z

theorem t294 (z w : Ty05) :
    (Foam.Ty05.d109 z w * Foam.Ty05.d109 z w + Foam.Ty05.d111 z w * Foam.Ty05.d111 z w = z.d114 * w.d114)
      ∧ (Foam.Ty05.d111 w.d115 z.d115 = Foam.Ty05.d111 w z) :=
  ⟨t302 z w, t276 w z⟩

/-- info: 'Foam.t296' does not depend on any axioms -/
#guard_msgs in #print axioms t296

/-- info: 'Foam.t295' does not depend on any axioms -/
#guard_msgs in #print axioms t295

/-- info: 'Foam.t294' does not depend on any axioms -/
#guard_msgs in #print axioms t294

end Foam
