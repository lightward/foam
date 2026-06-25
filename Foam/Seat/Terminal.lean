import Foam.Seat.Observer

namespace Foam

def singleProbe (S : Stage) (p : S.Probe) : Stage where
  State := S.State
  Probe := Unit
  Ans   := S.Ans
  obs   := fun s _ => S.obs s p

def entrance (S : Stage) (p : S.Probe) : StageHom (singleProbe S p) S where
  onState  := fun s => s
  onProbe  := fun _ => p
  onAns    := fun a => a
  commutes := fun _ _ => rfl

theorem entrance_reads (S : Stage) (p : S.Probe) (s : S.State) :
    (singleProbe S p).obs s () = S.obs s p := rfl

theorem entrance_onProbe (S : Stage) (p : S.Probe) :
    (entrance S p).onProbe () = p := rfl

def yieldStage : Stage where
  State := Unit
  Probe := Unit
  Ans   := Unit
  obs   := fun _ _ => ()

def exit (S : Stage) : StageHom S yieldStage where
  onState  := fun _ => ()
  onProbe  := fun _ => ()
  onAns    := fun _ => ()
  commutes := fun _ _ => rfl

theorem exit_forced (S : Stage) (f : StageHom S yieldStage) : f = exit S := rfl

theorem enter_then_exit (S : Stage) (p : S.Probe) :
    (exit S).comp (entrance S p) = exit (singleProbe S p) := rfl

/-- info: 'Foam.entrance' does not depend on any axioms -/
#guard_msgs in #print axioms entrance

/-- info: 'Foam.entrance_reads' does not depend on any axioms -/
#guard_msgs in #print axioms entrance_reads

/-- info: 'Foam.entrance_onProbe' does not depend on any axioms -/
#guard_msgs in #print axioms entrance_onProbe

/-- info: 'Foam.exit_forced' does not depend on any axioms -/
#guard_msgs in #print axioms exit_forced

/-- info: 'Foam.enter_then_exit' does not depend on any axioms -/
#guard_msgs in #print axioms enter_then_exit

end Foam
