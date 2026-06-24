import Foam.Seat.Epoch

namespace Foam

theorem kolmogorov_checksum {State : Type} {walk bank : List (Beholder State)}
    (h : Run walk bank) : (∀ q ∈ walk, Known bank q) ∧ Reduced bank :=
  h.checksum

/-- info: 'Foam.kolmogorov_checksum' does not depend on any axioms -/
#guard_msgs in #print axioms kolmogorov_checksum

end Foam
