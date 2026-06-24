import Foam.Seat

namespace Foam

variable {G : Type} [Mul G] [One G]

theorem Ty16.t242 (S : Ty16 G) (p q r : S.Ty24) :
    S.d133 p q * S.d133 q r = S.d133 p r :=
  (S.t250 p q r).symm

theorem Ty16.t247 (S : Ty16 G) (p q : S.Ty24) :
    S.d133 p q * S.d133 q p = 1 :=
  S.t251 q p

theorem Ty16.t254 (S : Ty16 G) (p q r : S.Ty24) :
    S.d133 p q * S.d133 q r * S.d133 r p = 1 := by
  rw [← S.t250 p q r]
  exact S.t251 r p

theorem Ty16.t243 (S : Ty16 G) (p q r s : S.Ty24) :
    S.d133 p q * S.d133 q r * S.d133 r s * S.d133 s p = 1 := by
  rw [← S.t250 p q r, ← S.t250 p r s]
  exact S.t251 s p

theorem Ty16.t244 (S : Ty16 G) (g : G) (p : S.Ty24) :
    S.d133 p (S.d131 g p)
      * S.d133 (S.d131 g p) (S.d131 g (S.d131 g p))
      * S.d133 (S.d131 g (S.d131 g p)) p = 1 :=
  S.t254 p (S.d131 g p) (S.d131 g (S.d131 g p))

/-- info: 'Foam.Ty16.t244' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t244

/-- info: 'Foam.Ty16.t242' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t242

/-- info: 'Foam.Ty16.t254' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t254

/-- info: 'Foam.Ty16.t243' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t243

end Foam
