namespace Foam

structure Iso (A B : Type) where
  fwd     : A → B
  bwd     : B → A
  fwd_bwd : ∀ b, fwd (bwd b) = b
  bwd_fwd : ∀ a, bwd (fwd a) = a

variable {G : Type} [Mul G] [One G]

structure Seat (G : Type) [Mul G] [One G] where
  Pos     : Type
  act     : G → Pos → Pos
  one_act : ∀ p, act 1 p = p
  mul_act : ∀ g h p, act (g * h) p = act g (act h p)
  sub     : Pos → Pos → G
  act_sub : ∀ p q, act (sub q p) p = q
  sub_act : ∀ g p, sub (act g p) p = g

theorem Seat.sub_self (S : Seat G) (p : S.Pos) : S.sub p p = 1 := by
  have h := S.sub_act 1 p
  rw [S.one_act] at h
  exact h

def Seat.chart (S : Seat G) (origin : S.Pos) : Iso S.Pos G where
  fwd     := fun p => S.sub p origin
  bwd     := fun g => S.act g origin
  fwd_bwd := fun g => S.sub_act g origin
  bwd_fwd := fun p => S.act_sub origin p

theorem Seat.change_of_frame (S : Seat G) (o o' p : S.Pos) :
    (S.chart o).fwd p = (S.chart o').fwd p * S.sub o' o := by
  show S.sub p o = S.sub p o' * S.sub o' o
  have e : S.act (S.sub p o' * S.sub o' o) o = p := by
    rw [S.mul_act, S.act_sub o o', S.act_sub o' p]
  have h := S.sub_act (S.sub p o' * S.sub o' o) o
  rw [e] at h
  exact h

theorem Seat.chart_origin_dependent (S : Seat G) (o o' : S.Pos) (h : o ≠ o') :
    ∃ p, (S.chart o).fwd p ≠ (S.chart o').fwd p := by
  refine ⟨o, ?_⟩
  show S.sub o o ≠ S.sub o o'
  rw [S.sub_self]
  intro hbad
  apply h
  have h1 := S.act_sub o' o
  rw [← hbad, S.one_act] at h1
  exact h1.symm

/-- info: 'Foam.Seat.sub_self' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.sub_self

/-- info: 'Foam.Seat.change_of_frame' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.change_of_frame

/-- info: 'Foam.Seat.chart_origin_dependent' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.chart_origin_dependent

end Foam
