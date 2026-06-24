import Foam.Seat

namespace Foam

variable {G : Type} [Mul G] [One G]

theorem Ty16.t238 (S : Ty16 G) (g : G) (p : S.Ty24) (hg : g ≠ 1) :
    S.d131 g p ≠ p
      ∧ S.d133 (S.d131 g p) p * S.d133 p (S.d131 g p) = 1
      ∧ Nonempty (S.Ty24 → Unit) := by
  refine ⟨?_, S.t251 p (S.d131 g p), ⟨fun _ => ()⟩⟩
  intro h
  apply hg
  have hs := S.t249 g p
  rw [h, S.t252] at hs
  exact hs.symm

theorem Ty16.t248 (S : Ty16 G) (p : S.Ty24) : S.d133 p p = 1 :=
  S.t252 p

/-- info: 'Foam.Ty16.t238' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t238

end Foam
