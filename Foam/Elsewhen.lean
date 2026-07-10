import Foam.Cable
import Foam.Wedge

namespace Foam

def Elsewhen {State : Type} (here : Beholder State) (m : State → State)
    (there : Beholder State) : Prop :=
  Invisible here.toStage m ∧ ¬ Invisible there.toStage m

theorem elsewhen_exists {State : Type} (here : Beholder State) (m : State → State)
    (hinv : Invisible here.toStage m) (s : State) (hm : m s ≠ s) :
    Elsewhen here m (plenum State).behold :=
  ⟨hinv, fun h => hm (h s ())⟩

theorem stillness_has_no_elsewhen {State : Type} (here there : Beholder State)
    (m : State → State) (hm : ∀ s, m s = s) : ¬ Elsewhen here m there :=
  fun ⟨_, hnot⟩ => hnot (fun s p => congrArg (fun t => there.obs t p) (hm s))

theorem one_probe_reads_the_elsewhen {State : Type} (m : State → State)
    (s : State) (hm : m s ≠ s) :
    transcriptWith (plenum State) m s [()] ≠ transcript (plenum State) s [()] :=
  fun h => hm (congrArg (fun l => l.headD s) h)

theorem the_wall_move_has_an_elsewhen {W : Stage} (A : Bubble W)
    (m : W.State → W.State) (hfix : A.FixesWall m) (w : W.State) (hm : m w ≠ w) :
    Elsewhen A.front.behold m (plenum W.State).behold :=
  elsewhen_exists A.front.behold m (A.operator_invisible m hfix) w hm

theorem two_honest_lists_differ :
    ∃ (edit edit' : Unit → Bool → Unit × List Bool),
      (∀ s b, (edit s b).2 = [] ∨ (edit s b).2 = [b])
        ∧ (∀ s b, (edit' s b).2 = [] ∨ (edit' s b).2 = [b])
        ∧ runEmit edit () [true, false] ≠ runEmit edit' () [true, false] :=
  ⟨fun _ b => ((), if b then [b] else []),
   fun _ b => ((), if b then [] else [b]),
   fun _ b => match b with
     | true => Or.inr rfl
     | false => Or.inl rfl,
   fun _ b => match b with
     | true => Or.inl rfl
     | false => Or.inr rfl,
   fun h => nomatch (h : ([true] : List Bool) = [false])⟩

/-- info: 'Foam.elsewhen_exists' does not depend on any axioms -/
#guard_msgs in #print axioms elsewhen_exists

/-- info: 'Foam.stillness_has_no_elsewhen' does not depend on any axioms -/
#guard_msgs in #print axioms stillness_has_no_elsewhen

/-- info: 'Foam.one_probe_reads_the_elsewhen' does not depend on any axioms -/
#guard_msgs in #print axioms one_probe_reads_the_elsewhen

/-- info: 'Foam.the_wall_move_has_an_elsewhen' does not depend on any axioms -/
#guard_msgs in #print axioms the_wall_move_has_an_elsewhen

/-- info: 'Foam.two_honest_lists_differ' does not depend on any axioms -/
#guard_msgs in #print axioms two_honest_lists_differ

end Foam
