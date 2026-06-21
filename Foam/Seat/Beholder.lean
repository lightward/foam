import Foam.Seat.Stage
import Foam.Seat.Observer

namespace Foam

structure Beholder (State : Type) where
  Probe : Type
  Ans : Type
  obs : State → Probe → Ans

def Beholder.toStage {State : Type} (b : Beholder State) : Stage where
  State := State
  Probe := b.Probe
  Ans := b.Ans
  obs := b.obs

def Beholder.pair {State : Type} (a b : Beholder State) : Beholder State where
  Probe := a.Probe × b.Probe
  Ans := a.Ans × b.Ans
  obs s pq := (a.obs s pq.1, b.obs s pq.2)

theorem pair_sees_left {State : Type} (a b : Beholder State)
    (s : State) (p : a.Probe) (q : b.Probe) :
    ((a.pair b).obs s (p, q)).1 = a.obs s p := rfl

/-- info: 'Foam.pair_sees_left' does not depend on any axioms -/
#guard_msgs in #print axioms pair_sees_left

theorem pair_sees_right {State : Type} (a b : Beholder State)
    (s : State) (p : a.Probe) (q : b.Probe) :
    ((a.pair b).obs s (p, q)).2 = b.obs s q := rfl

/-- info: 'Foam.pair_sees_right' does not depend on any axioms -/
#guard_msgs in #print axioms pair_sees_right

def compare {State R : Type} (a b : Beholder State)
    (g : a.Ans → b.Ans → R) (s : State) (p : a.Probe) (q : b.Probe) : R :=
  g (a.obs s p) (b.obs s q)

theorem compare_through_pair {State R : Type} (a b : Beholder State)
    (g : a.Ans → b.Ans → R) (s : State) (p : a.Probe) (q : b.Probe) :
    compare a b g s p q = g ((a.pair b).obs s (p, q)).1 ((a.pair b).obs s (p, q)).2 :=
  rfl

/-- info: 'Foam.compare_through_pair' does not depend on any axioms -/
#guard_msgs in #print axioms compare_through_pair

theorem no_view_from_nowhere {State R : Type} (a b : Beholder State)
    (g : a.Ans → b.Ans → R) :
    ∃ c : Beholder State, ∃ post : c.Ans → R, ∃ enc : a.Probe × b.Probe → c.Probe,
      ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))) :=
  ⟨a.pair b, fun ans => g ans.1 ans.2, id, fun _ _ _ => rfl⟩

/-- info: 'Foam.no_view_from_nowhere' does not depend on any axioms -/
#guard_msgs in #print axioms no_view_from_nowhere

def Stage.behold (S : Stage) : Beholder S.State := ⟨S.Probe, S.Ans, S.obs⟩

theorem Stage.behold_toStage (S : Stage) : S.behold.toStage = S := rfl

/-- info: 'Foam.Stage.behold_toStage' does not depend on any axioms -/
#guard_msgs in #print axioms Stage.behold_toStage

theorem Beholder.toStage_behold {State : Type} (b : Beholder State) :
    b.toStage.behold = b := rfl

/-- info: 'Foam.Beholder.toStage_behold' does not depend on any axioms -/
#guard_msgs in #print axioms Beholder.toStage_behold

end Foam
