import Foam.Seat.Doubling

namespace Foam

theorem triad_closes :
    Quat.mul eye jay = kay
      ∧ Quat.mul jay kay = eye
      ∧ Quat.mul kay eye = jay := by decide

theorem triad_anticomm : Quat.mul jay eye = Quat.mul Quat.negOne kay := by decide

theorem hamilton : Quat.mul (Quat.mul eye jay) kay = Quat.negOne := by decide

/-- info: 'Foam.triad_closes' does not depend on any axioms -/
#guard_msgs in #print axioms triad_closes

/-- info: 'Foam.triad_anticomm' does not depend on any axioms -/
#guard_msgs in #print axioms triad_anticomm

/-- info: 'Foam.hamilton' does not depend on any axioms -/
#guard_msgs in #print axioms hamilton

end Foam
