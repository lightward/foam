import Foam.Seat

namespace Foam

variable {G : Type} [Mul G] [One G]

theorem Seat.path_telescopes (S : Seat G) (p q r : S.Pos) :
    S.sub p q * S.sub q r = S.sub p r :=
  (S.sub_cocycle p q r).symm

theorem Seat.round_trip (S : Seat G) (p q : S.Pos) :
    S.sub p q * S.sub q p = 1 :=
  S.sub_inv q p

theorem Seat.triangle_unwinds (S : Seat G) (p q r : S.Pos) :
    S.sub p q * S.sub q r * S.sub r p = 1 := by
  rw [← S.sub_cocycle p q r]
  exact S.sub_inv r p

theorem Seat.quad_unwinds (S : Seat G) (p q r s : S.Pos) :
    S.sub p q * S.sub q r * S.sub r s * S.sub s p = 1 := by
  rw [← S.sub_cocycle p q r, ← S.sub_cocycle p r s]
  exact S.sub_inv s p

theorem Seat.repeat_unwinds (S : Seat G) (g : G) (p : S.Pos) :
    S.sub p (S.act g p)
      * S.sub (S.act g p) (S.act g (S.act g p))
      * S.sub (S.act g (S.act g p)) p = 1 :=
  S.triangle_unwinds p (S.act g p) (S.act g (S.act g p))

/-- info: 'Foam.Seat.repeat_unwinds' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.repeat_unwinds

/-- info: 'Foam.Seat.path_telescopes' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.path_telescopes

/-- info: 'Foam.Seat.triangle_unwinds' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.triangle_unwinds

/-- info: 'Foam.Seat.quad_unwinds' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.quad_unwinds

end Foam
