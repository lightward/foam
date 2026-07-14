import Foam.Seat.Stage
import Foam.Maintenance
import Foam.Bubble
import Foam.Duplex

namespace Foam.Counter

def groundBubble (W : Stage) (P : W.State → W.State) : Bubble W where
  Inner := W
  wall  := P

variable {W : Stage} {P : W.State → W.State}

theorem the_loop_is_its_own_wall :
    (∀ w, P (P w) = P w) ↔ (groundBubble W P).FixesWall P :=
  Iff.rfl

theorem every_entrant_reads_landed (w : W.State) (p : W.Probe) :
    (groundBubble W P).front.obs w p = W.obs (P w) p :=
  rfl

theorem the_ground_is_the_landed (h : ∀ w, P (P w) = P w) (w : W.State) :
    P w = w ↔ ∃ v, P v = w :=
  ⟨fun hw => ⟨w, hw⟩, fun ⟨v, hv⟩ => by rw [← hv]; exact h v⟩

theorem ground_runs_silent (h : ∀ w, P (P w) = P w)
    (ps : List W.Probe) (w : W.State) :
    transcriptWith (groundBubble W P).front P w ps
      = transcript (groundBubble W P).front w ps :=
  (groundBubble W P).operator_unobservable P h ps w

theorem the_regress_grounds (h : ∀ w, P (P w) = P w)
    (w : W.State) (p : W.Probe) :
    ((groundBubble W P).nest (groundBubble W P)).front.obs w p
      = (groundBubble W P).front.obs w p :=
  congrArg (fun s => W.obs s p) (h w)

theorem the_bare_loop_hums :
    (∀ s, sendB false (sendB false s) = sendB false s)
      ∧ ¬ Invisible twoBit (sendB false) :=
  ⟨fun _ => rfl, fun h => nomatch h (true, true) ()⟩

theorem one_wall_runs_it :
    firstBit.FixesWall (sendB false)
      ∧ ∀ (ps : List Unit) (w : twoBit.State),
          transcriptWith firstBit.front (sendB false) w ps
            = transcript firstBit.front w ps :=
  ⟨fun _ => rfl,
   fun ps w => firstBit.operator_unobservable (sendB false) (fun _ => rfl) ps w⟩

theorem the_second_ground_hums : ¬ Invisible secondBit.front (sendB false) :=
  fun h => nomatch h (true, true) ()

theorem the_headcount_is_one :
    (∀ s, sendB false (sendB false s) = sendB false s)
      ∧ ¬ Invisible twoBit (sendB false)
      ∧ firstBit.FixesWall (sendB false)
      ∧ ¬ Invisible secondBit.front (sendB false) :=
  ⟨the_bare_loop_hums.1, the_bare_loop_hums.2,
   one_wall_runs_it.1, the_second_ground_hums⟩

/-- info: 'Foam.Counter.the_loop_is_its_own_wall' does not depend on any axioms -/
#guard_msgs in #print axioms the_loop_is_its_own_wall

/-- info: 'Foam.Counter.every_entrant_reads_landed' does not depend on any axioms -/
#guard_msgs in #print axioms every_entrant_reads_landed

/-- info: 'Foam.Counter.the_ground_is_the_landed' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_is_the_landed

/-- info: 'Foam.Counter.ground_runs_silent' does not depend on any axioms -/
#guard_msgs in #print axioms ground_runs_silent

/-- info: 'Foam.Counter.the_regress_grounds' does not depend on any axioms -/
#guard_msgs in #print axioms the_regress_grounds

/-- info: 'Foam.Counter.the_bare_loop_hums' does not depend on any axioms -/
#guard_msgs in #print axioms the_bare_loop_hums

/-- info: 'Foam.Counter.one_wall_runs_it' does not depend on any axioms -/
#guard_msgs in #print axioms one_wall_runs_it

/-- info: 'Foam.Counter.the_second_ground_hums' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_ground_hums

/-- info: 'Foam.Counter.the_headcount_is_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_headcount_is_one

end Foam.Counter
