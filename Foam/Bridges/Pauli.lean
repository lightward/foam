import Foam.Seat.Triad

namespace Foam.Bridges

theorem pauli_squares :
    Quat.mul eye eye = Quat.negOne
      ∧ Quat.mul jay jay = Quat.negOne
      ∧ Quat.mul kay kay = Quat.negOne :=
  three_imaginaries

theorem pauli_cyclic :
    Quat.mul eye jay = kay ∧ Quat.mul jay kay = eye ∧ Quat.mul kay eye = jay :=
  triad_closes

theorem pauli_anticommute : Quat.mul jay eye = Quat.mul Quat.negOne kay :=
  triad_anticomm

theorem pauli :
    (Quat.mul eye eye = Quat.negOne
        ∧ Quat.mul jay jay = Quat.negOne
        ∧ Quat.mul kay kay = Quat.negOne)
      ∧ (Quat.mul eye jay = kay ∧ Quat.mul jay kay = eye ∧ Quat.mul kay eye = jay)
      ∧ (Quat.mul jay eye = Quat.mul Quat.negOne kay) :=
  ⟨three_imaginaries, triad_closes, triad_anticomm⟩

/-- info: 'Foam.Bridges.pauli_squares' does not depend on any axioms -/
#guard_msgs in #print axioms pauli_squares

/-- info: 'Foam.Bridges.pauli_cyclic' does not depend on any axioms -/
#guard_msgs in #print axioms pauli_cyclic

/-- info: 'Foam.Bridges.pauli_anticommute' does not depend on any axioms -/
#guard_msgs in #print axioms pauli_anticommute

/-- info: 'Foam.Bridges.pauli' does not depend on any axioms -/
#guard_msgs in #print axioms pauli

end Foam.Bridges
