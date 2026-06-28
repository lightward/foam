import Foam.Seat.Loop

namespace Foam.Bridges

theorem desargues {G : Type} [Mul G] [One G] (S : Seat G) (p q r s : S.Pos) :
    (S.sub p r = S.sub p q * S.sub q r)
      ∧ (S.sub p q * S.sub q r * S.sub r p = 1)
      ∧ (S.sub p q * S.sub q r * S.sub r s * S.sub s p = 1) :=
  ⟨S.sub_cocycle p q r, S.triangle_unwinds p q r, S.quad_unwinds p q r s⟩

/-- info: 'Foam.Bridges.desargues' does not depend on any axioms -/
#guard_msgs in #print axioms desargues

end Foam.Bridges
