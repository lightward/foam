import Foam.Seat.Quiver

namespace Foam

def Ty11.d061 {Handle : Type} (q : Ty11 Handle) (e : Handle × Handle) :
    Ty11 Handle := e :: q

theorem t163 {Handle : Type} (q : Ty11 Handle) (e : Handle × Handle) :
    (q.d061 e).length = q.length + 1 := rfl

/-- info: 'Foam.t163' does not depend on any axioms -/
#guard_msgs in #print axioms t163

end Foam
