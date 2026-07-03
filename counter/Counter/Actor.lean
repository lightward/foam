import Foam.Seat
import Foam.Seat.Loop
import Foam.Seat.Resume
import Foam.Ledger

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

def netAct : List G → G
  | [] => 1
  | g :: rest => netAct rest * g

theorem replay_is_netAct (S : Seat G) (h : List G) (p : S.Pos) :
    S.replay h p = S.act (netAct h) p := by
  induction h generalizing p with
  | nil => exact (S.one_act p).symm
  | cons g rest ih =>
    show S.replay rest (S.act g p) = S.act (netAct rest * g) p
    rw [ih (S.act g p), S.mul_act (netAct rest) g p]

def Settles (S : Seat G) (h : List G) (p : S.Pos) : Prop := S.replay h p = p

theorem settles_iff_home (S : Seat G) (h : List G) (p : S.Pos) :
    Settles S h p ↔ netAct h = 1 := by
  unfold Settles
  rw [replay_is_netAct]
  constructor
  · intro hh
    have e : S.act (netAct h) p = S.act 1 p := by rw [hh, S.one_act]
    exact S.act_faithful p e
  · intro hh; rw [hh, S.one_act]

theorem always_homeable (S : Seat G) (h : List G) (p : S.Pos) :
    Settles S (h ++ [S.sub p (S.replay h p)]) p := by
  unfold Settles
  rw [S.replay_resumes h [S.sub p (S.replay h p)] p]
  show S.act (S.sub p (S.replay h p)) (S.replay h p) = p
  exact S.act_sub (S.replay h p) p

def winding [DecidableEq G] (h : List G) (g : G) : Nat := Ledger.freq h g

theorem lone_actor_settled (S : Seat G) (hsing : ∀ p q : S.Pos, p = q)
    (h : List G) (p : S.Pos) : S.sub (S.replay h p) p = 1 :=
  S.singleton_no_field hsing (S.replay h p) p

theorem pressure_needs_a_second (S : Seat G) (p : S.Pos) (h : List G)
    (hp : S.replay h p ≠ p) : S.sub (S.replay h p) p ≠ 1 :=
  S.two_observers_substantiate (S.replay h p) p hp

/-- info: 'Foam.Counter.replay_is_netAct' does not depend on any axioms -/
#guard_msgs in #print axioms replay_is_netAct

/-- info: 'Foam.Counter.settles_iff_home' does not depend on any axioms -/
#guard_msgs in #print axioms settles_iff_home

/-- info: 'Foam.Counter.always_homeable' does not depend on any axioms -/
#guard_msgs in #print axioms always_homeable

/-- info: 'Foam.Counter.lone_actor_settled' does not depend on any axioms -/
#guard_msgs in #print axioms lone_actor_settled

/-- info: 'Foam.Counter.pressure_needs_a_second' does not depend on any axioms -/
#guard_msgs in #print axioms pressure_needs_a_second

end Foam.Counter
