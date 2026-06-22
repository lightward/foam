import Foam.Seat.Quiver

namespace Foam

def Quiver.deposit {Handle : Type} (q : Quiver Handle) (e : Handle × Handle) :
    Quiver Handle := e :: q

theorem deposit_monotone {Handle : Type} (q : Quiver Handle) (e : Handle × Handle) :
    (q.deposit e).length = q.length + 1 := rfl

/-- info: 'Foam.deposit_monotone' does not depend on any axioms -/
#guard_msgs in #print axioms deposit_monotone

end Foam
