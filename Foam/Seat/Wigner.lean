import Foam.Seat.Norm
import Foam.Seat.Characters
import Foam.Seat.Schrodinger

namespace Foam

theorem t330 (z : Ty05) : (Foam.Ty05.d115 z).d114 = z.d114 :=
  t280 z

theorem t328 (z : Ty05) : z.d110.d114 = z.d114 :=
  Foam.Ty05.t211 z

theorem t407 : Foam.d103 ≠ Foam.d162 :=
  Foam.t342

theorem t329 (a b : Ty12) :
    Foam.d103 (a * b) = Foam.Ty05.d112 (Foam.d103 a) (Foam.d103 b) :=
  Foam.t201 a b

theorem t406 (z : Ty05) :
    ((Foam.Ty05.d115 z).d114 = z.d114)
      ∧ (z.d110.d114 = z.d114)
      ∧ (Foam.d103 ≠ Foam.d162)
      ∧ (∀ a b, Foam.d103 (a * b) = Foam.Ty05.d112 (Foam.d103 a) (Foam.d103 b)) :=
  ⟨t280 z, Foam.Ty05.t211 z, Foam.t342, Foam.t201⟩

/-- info: 'Foam.t330' does not depend on any axioms -/
#guard_msgs in #print axioms t330

/-- info: 'Foam.t328' does not depend on any axioms -/
#guard_msgs in #print axioms t328

/-- info: 'Foam.t407' does not depend on any axioms -/
#guard_msgs in #print axioms t407

/-- info: 'Foam.t329' does not depend on any axioms -/
#guard_msgs in #print axioms t329

/-- info: 'Foam.t406' does not depend on any axioms -/
#guard_msgs in #print axioms t406

end Foam
