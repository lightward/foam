import Foam.Seat

namespace Foam

structure Stage where
  State : Type
  Probe : Type
  Ans   : Type
  obs   : State → Probe → Ans

variable {G : Type} [Mul G] [One G]

def Seat.toStage (S : Seat G) : Stage where
  State := S.Pos
  Probe := S.Pos
  Ans   := G
  obs   := S.sub

theorem Seat.obs_faithful (S : Seat G) (s t : S.Pos)
    (h : ∀ p, S.sub s p = S.sub t p) : s = t := by
  have h1 := h t
  rw [S.sub_self] at h1
  have h2 := S.act_sub t s
  rw [h1, S.one_act] at h2
  exact h2.symm

/-- info: 'Foam.Seat.obs_faithful' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.obs_faithful

end Foam
