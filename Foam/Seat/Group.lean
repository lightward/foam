import Foam.Seat

namespace Foam

class Ty06 (G : Type) extends Mul G, One G where
  d046       : G → G
  t144   : ∀ a : G, 1 * a = a
  t143   : ∀ a : G, a * 1 = a
  t141 : ∀ a b c : G, a * b * c = a * (b * c)
  t142   : ∀ a : G, a * d046 a = 1
  t140   : ∀ a : G, d046 a * a = 1

def Ty16.d181 (G : Type) [Ty06 G] : Ty16 G where
  Ty24     := G
  d131     := fun g x => g * x
  t241 := fun x => Foam.Ty06.t144 x
  t239 := fun g h x => Foam.Ty06.t141 g h x
  d133     := fun a b => a * Foam.Ty06.d046 b
  t237 := fun p q => by
    show (q * Foam.Ty06.d046 p) * p = q
    rw [Foam.Ty06.t141, Foam.Ty06.t140, Foam.Ty06.t143]
  t249 := fun g p => by
    show (g * p) * Foam.Ty06.d046 p = g
    rw [Foam.Ty06.t141, Foam.Ty06.t142, Foam.Ty06.t143]

/-- info: 'Foam.Ty16.d181' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.d181

end Foam
