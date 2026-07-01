import Counter.Actor

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

def rebase (S : Seat G) (o o' : S.Pos) : G := S.sub o' o

theorem rebase_carries (S : Seat G) (o o' : S.Pos) :
    S.act (rebase S o o') o = o' :=
  S.act_sub o o'

theorem rebase_unique (S : Seat G) (o o' : S.Pos) (g : G)
    (h : S.act g o = o') : g = rebase S o o' := by
  have hs := S.sub_act g o
  rw [h] at hs
  exact hs.symm

theorem rebase_self (S : Seat G) (o : S.Pos) : rebase S o o = 1 :=
  S.sub_self o

theorem rebase_lands_in_own_history (S : Seat G) (h : List G) (o o' : S.Pos) :
    S.replay (h ++ [rebase S (S.replay h o) o']) o = o' := by
  rw [S.replay_resumes h [rebase S (S.replay h o) o'] o]
  show S.act (rebase S (S.replay h o) o') (S.replay h o) = o'
  exact S.act_sub (S.replay h o) o'

theorem homing_is_rebase_to_self (S : Seat G) (h : List G) (p : S.Pos) :
    S.sub p (S.replay h p) = rebase S (S.replay h p) p := rfl

/-- info: 'Foam.Counter.rebase_carries' does not depend on any axioms -/
#guard_msgs in #print axioms rebase_carries

/-- info: 'Foam.Counter.rebase_unique' does not depend on any axioms -/
#guard_msgs in #print axioms rebase_unique

/-- info: 'Foam.Counter.rebase_self' does not depend on any axioms -/
#guard_msgs in #print axioms rebase_self

/-- info: 'Foam.Counter.rebase_lands_in_own_history' does not depend on any axioms -/
#guard_msgs in #print axioms rebase_lands_in_own_history

/-- info: 'Foam.Counter.homing_is_rebase_to_self' does not depend on any axioms -/
#guard_msgs in #print axioms homing_is_rebase_to_self

end Foam.Counter
