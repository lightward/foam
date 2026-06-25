import Foam.Seat

namespace Foam

variable {G : Type} [Mul G] [One G]

theorem Seat.good_loop (S : Seat G) (g : G) (p : S.Pos) (hg : g ≠ 1) :
    S.act g p ≠ p
      ∧ S.sub (S.act g p) p * S.sub p (S.act g p) = 1
      ∧ Nonempty (S.Pos → Unit) := by
  refine ⟨?_, S.sub_inv p (S.act g p), ⟨fun _ => ()⟩⟩
  intro h
  apply hg
  have hs := S.sub_act g p
  rw [h, S.sub_self] at hs
  exact hs.symm

theorem Seat.self_health (S : Seat G) (p : S.Pos) : S.sub p p = 1 :=
  S.sub_self p

/-- info: 'Foam.Seat.good_loop' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.good_loop

end Foam
