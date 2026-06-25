import Foam.Seat

namespace Foam

class Grp (G : Type) extends Mul G, One G where
  inv       : G → G
  one_mul   : ∀ a : G, 1 * a = a
  mul_one   : ∀ a : G, a * 1 = a
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  mul_inv   : ∀ a : G, a * inv a = 1
  inv_mul   : ∀ a : G, inv a * a = 1

def Seat.principal (G : Type) [Grp G] : Seat G where
  Pos     := G
  act     := fun g x => g * x
  one_act := fun x => Grp.one_mul x
  mul_act := fun g h x => Grp.mul_assoc g h x
  sub     := fun a b => a * Grp.inv b
  act_sub := fun p q => by
    show (q * Grp.inv p) * p = q
    rw [Grp.mul_assoc, Grp.inv_mul, Grp.mul_one]
  sub_act := fun g p => by
    show (g * p) * Grp.inv p = g
    rw [Grp.mul_assoc, Grp.mul_inv, Grp.mul_one]

/-- info: 'Foam.Seat.principal' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.principal

end Foam
