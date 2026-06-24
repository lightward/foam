import Foam.Seat

namespace Foam

structure Ty18 where
  Ty27 : Type
  Ty26 : Type
  Ty25   : Type
  d134   : Ty27 → Ty26 → Ty25

variable {G : Type} [Mul G] [One G]

def Ty16.d182 (S : Ty16 G) : Ty18 where
  Ty27 := S.Ty24
  Ty26 := S.Ty24
  Ty25   := G
  d134   := S.d133

theorem Ty16.t240 (S : Ty16 G) (s t : S.Ty24)
    (h : ∀ p, S.d133 s p = S.d133 t p) : s = t := by
  have h1 := h t
  rw [S.t252] at h1
  have h2 := S.t237 t s
  rw [h1, S.t241] at h2
  exact h2.symm

/-- info: 'Foam.Ty16.t240' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t240

end Foam
