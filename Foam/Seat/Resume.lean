import Foam.Seat

namespace Foam

variable {G : Type} [Mul G] [One G]

def Ty16.d132 (S : Ty16 G) : List G → S.Ty24 → S.Ty24
  | [], p => p
  | g :: rest, p => S.d132 rest (S.d131 g p)

theorem Ty16.t245 (S : Ty16 G) (p : S.Ty24) : S.d132 [] p = p := rfl

theorem Ty16.t246 (S : Ty16 G) (xs ys : List G) (p : S.Ty24) :
    S.d132 (xs ++ ys) p = S.d132 ys (S.d132 xs p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons g rest ih => exact ih (S.d131 g p)

theorem Ty16.t253 (S : Ty16 G) (p q r : S.Ty24) :
    S.d132 [S.d133 q p, S.d133 r q, S.d133 p r] p = p := by
  show S.d131 (S.d133 p r) (S.d131 (S.d133 r q) (S.d131 (S.d133 q p) p)) = p
  rw [S.t237 p q, S.t237 q r, S.t237 r p]

/-- info: 'Foam.Ty16.t253' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t253

/-- info: 'Foam.Ty16.t245' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t245

/-- info: 'Foam.Ty16.t246' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t246

end Foam
