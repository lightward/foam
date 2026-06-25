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

theorem Seat.sub_inv (S : Seat G) (p q : S.Pos) : S.sub q p * S.sub p q = 1 := by
  have e : S.act (S.sub q p * S.sub p q) q = q := by
    rw [S.mul_act, S.act_sub q p, S.act_sub p q]
  have h := S.sub_act (S.sub q p * S.sub p q) q
  rw [e, S.sub_self] at h
  exact h.symm

theorem Seat.sub_cocycle (S : Seat G) (p q r : S.Pos) :
    S.sub p r = S.sub p q * S.sub q r := by
  have e : S.act (S.sub p q * S.sub q r) r = p := by
    rw [S.mul_act, S.act_sub r q, S.act_sub q p]
  have h := S.sub_act (S.sub p q * S.sub q r) r
  rw [e] at h
  exact h

def Seat.chart (S : Seat G) (origin : S.Pos) : Iso S.Pos G where
  fwd     := fun p => S.sub p origin
  bwd     := fun g => S.act g origin
  fwd_bwd := fun g => S.sub_act g origin
  bwd_fwd := fun p => S.act_sub origin p

theorem Seat.chart_equivariant (S : Seat G) (g : G) (p o : S.Pos) :
    (S.chart o).fwd (S.act g p) = g * (S.chart o).fwd p := by
  show S.sub (S.act g p) o = g * S.sub p o
  have e : S.act (g * S.sub p o) o = S.act g p := by
    rw [S.mul_act, S.act_sub o p]
  have h := S.sub_act (g * S.sub p o) o
  rw [e] at h
  exact h

theorem Seat.change_of_frame (S : Seat G) (o o' p : S.Pos) :
    (S.chart o).fwd p = (S.chart o').fwd p * S.sub o' o := by
  show S.sub p o = S.sub p o' * S.sub o' o
  exact S.sub_cocycle p o' o

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

/-- info: 'Foam.Seat.sub_inv' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.sub_inv

/-- info: 'Foam.Seat.sub_cocycle' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.sub_cocycle

/-- info: 'Foam.Seat.chart_equivariant' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.chart_equivariant

/-- info: 'Foam.Seat.change_of_frame' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.change_of_frame

/-- info: 'Foam.Seat.chart_origin_dependent' does not depend on any axioms -/
#guard_msgs in #print axioms Seat.chart_origin_dependent

end Foam
