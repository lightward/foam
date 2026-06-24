import Foam.Seat.Signature

namespace Foam

theorem t293 (κ : Int) (f : Int → Int)
    (h : ∀ w z : Ty05, f (d140 κ w z) - κ * f (d142 w z) = d149 κ w * d149 κ z) :
    ∀ a : Int, f a = a * a + κ * f 0 :=
  t284 κ f h

/-- info: 'Foam.t293' does not depend on any axioms -/
#guard_msgs in #print axioms t293

end Foam
