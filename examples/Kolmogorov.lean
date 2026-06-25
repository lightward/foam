import Foam.Seat.Epoch

namespace Foam

theorem t464 {State : Type} {walk bank : List (Ty01 State)}
    (h : t100 walk bank) : (∀ q ∈ walk, t354 bank q) ∧ t356 bank :=
  h.t431

/-- info: 'Foam.t464' does not depend on any axioms -/
#guard_msgs in #print axioms t464

end Foam
