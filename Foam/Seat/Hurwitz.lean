import Foam.Seat.Norm
import Foam.Seat.Sed

namespace Foam

theorem t297 (z w : Ty05) : (z.d112 w).d114 = z.d114 * w.d114 :=
  Foam.Ty05.t212 z w

theorem t460 :
    Foam.Ty09.d209 (Foam.Ty09.d209 d191 d192) d188 ≠ Foam.Ty09.d209 d191 (Foam.Ty09.d209 d192 d188) :=
  t466

theorem t486 :
    Foam.Ty17.d227 d226 d195 = Foam.Ty17.d216 ∧ d226 ≠ Foam.Ty17.d216 ∧ d195 ≠ Foam.Ty17.d216 :=
  t484

theorem t487 :
    (∀ z w : Ty05, (z.d112 w).d114 = z.d114 * w.d114)
      ∧ (Foam.Ty09.d209 (Foam.Ty09.d209 d191 d192) d188 ≠ Foam.Ty09.d209 d191 (Foam.Ty09.d209 d192 d188))
      ∧ (Foam.Ty17.d227 d226 d195 = Foam.Ty17.d216 ∧ d226 ≠ Foam.Ty17.d216 ∧ d195 ≠ Foam.Ty17.d216) :=
  ⟨Foam.Ty05.t212, t466, t484⟩

/-- info: 'Foam.t297' does not depend on any axioms -/
#guard_msgs in #print axioms t297

/-- info: 'Foam.t460' does not depend on any axioms -/
#guard_msgs in #print axioms t460

/-- info: 'Foam.t486' does not depend on any axioms -/
#guard_msgs in #print axioms t486

/-- info: 'Foam.t487' does not depend on any axioms -/
#guard_msgs in #print axioms t487

end Foam
