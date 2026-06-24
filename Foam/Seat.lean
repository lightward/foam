namespace Foam

structure Ty07 (A B : Type) where
  d051     : A → B
  d049     : B → A
  t146 : ∀ b, d051 (d049 b) = b
  t145 : ∀ a, d049 (d051 a) = a

variable {G : Type} [Mul G] [One G]

structure Ty16 (G : Type) [Mul G] [One G] where
  Ty24     : Type
  d131     : G → Ty24 → Ty24
  t241 : ∀ p, d131 1 p = p
  t239 : ∀ g h p, d131 (g * h) p = d131 g (d131 h p)
  d133     : Ty24 → Ty24 → G
  t237 : ∀ p q, d131 (d133 q p) p = q
  t249 : ∀ g p, d133 (d131 g p) p = g

theorem Ty16.t252 (S : Ty16 G) (p : S.Ty24) : S.d133 p p = 1 := by
  have h := S.t249 1 p
  rw [S.t241] at h
  exact h

theorem Ty16.t251 (S : Ty16 G) (p q : S.Ty24) : S.d133 q p * S.d133 p q = 1 := by
  have e : S.d131 (S.d133 q p * S.d133 p q) q = q := by
    rw [S.t239, S.t237 q p, S.t237 p q]
  have h := S.t249 (S.d133 q p * S.d133 p q) q
  rw [e, S.t252] at h
  exact h.symm

theorem Ty16.t250 (S : Ty16 G) (p q r : S.Ty24) :
    S.d133 p r = S.d133 p q * S.d133 q r := by
  have e : S.d131 (S.d133 p q * S.d133 q r) r = p := by
    rw [S.t239, S.t237 r q, S.t237 q p]
  have h := S.t249 (S.d133 p q * S.d133 q r) r
  rw [e] at h
  exact h

def Ty16.d214 (S : Ty16 G) (origin : S.Ty24) : Ty07 S.Ty24 G where
  d051     := fun p => S.d133 p origin
  d049     := fun g => S.d131 g origin
  t146 := fun g => S.t249 g origin
  t145 := fun p => S.t237 origin p

theorem Ty16.t437 (S : Ty16 G) (g : G) (p o : S.Ty24) :
    (S.d214 o).d051 (S.d131 g p) = g * (S.d214 o).d051 p := by
  show S.d133 (S.d131 g p) o = g * S.d133 p o
  have e : S.d131 (g * S.d133 p o) o = S.d131 g p := by
    rw [S.t239, S.t237 o p]
  have h := S.t249 (g * S.d133 p o) o
  rw [e] at h
  exact h

theorem Ty16.t436 (S : Ty16 G) (o o' p : S.Ty24) :
    (S.d214 o).d051 p = (S.d214 o').d051 p * S.d133 o' o := by
  show S.d133 p o = S.d133 p o' * S.d133 o' o
  exact S.t250 p o' o

theorem Ty16.t438 (S : Ty16 G) (o o' : S.Ty24) (h : o ≠ o') :
    ∃ p, (S.d214 o).d051 p ≠ (S.d214 o').d051 p := by
  refine ⟨o, ?_⟩
  show S.d133 o o ≠ S.d133 o o'
  rw [S.t252]
  intro hbad
  apply h
  have h1 := S.t237 o' o
  rw [← hbad, S.t241] at h1
  exact h1.symm

/-- info: 'Foam.Ty16.t252' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t252

/-- info: 'Foam.Ty16.t251' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t251

/-- info: 'Foam.Ty16.t250' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t250

/-- info: 'Foam.Ty16.t437' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t437

/-- info: 'Foam.Ty16.t436' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t436

/-- info: 'Foam.Ty16.t438' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t438

end Foam
