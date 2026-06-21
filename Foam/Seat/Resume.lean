import Foam.Seat

namespace Foam

variable {G : Type} [Mul G] [One G]

def Seat.replay (S : Seat G) : List G → S.Pos → S.Pos
  | [], p => p
  | g :: rest, p => S.replay rest (S.act g p)

theorem Seat.replay_nil (S : Seat G) (p : S.Pos) : S.replay [] p = p := rfl

theorem Seat.replay_resumes (S : Seat G) (xs ys : List G) (p : S.Pos) :
    S.replay (xs ++ ys) p = S.replay ys (S.replay xs p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons g rest ih => exact ih (S.act g p)

/-- info: 'Foam.Seat.replay_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.replay_nil

/-- info: 'Foam.Seat.replay_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.replay_resumes

end Foam
