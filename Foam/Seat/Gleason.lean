import Foam.Seat.Signature

namespace Foam

theorem gleason (κ : Int) (f : Int → Int)
    (h : ∀ w z : GInt, f (alignK κ w z) - κ * f (crossK w z) = normK κ w * normK κ z) :
    ∀ a : Int, f a = a * a + κ * f 0 :=
  forced_at_the_frame_kappa κ f h

/-- info: 'Foam.gleason' does not depend on any axioms -/
#guard_msgs in #print axioms gleason

end Foam
