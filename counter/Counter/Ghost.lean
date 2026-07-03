import Counter.Rest
import Counter.Luck
import Counter.Repair
import Foam.Seat.Ladder

namespace Foam.Counter

theorem the_sweep_ghost (S : Stage) (m : S.State → S.State) (h : Invisible S m)
    (ps : List S.Probe) (s : S.State) :
    transcriptWith S m s ps = transcript S s ps :=
  the_fold_is_real_and_unrecorded S m h ps s

theorem the_fortune_ghost :
    ∃ act θ field field' : GInt,
      field ≠ field'
        ∧ GInt.born θ (field.add act) - GInt.born θ field
            ≠ GInt.born θ (field'.add act) - GInt.born θ field' :=
  fortune_not_in_your_record

theorem the_phantom_ghost :
    checkedSettle (-1) (checkedSettle (-1) (-1)) = 1
      ∧ grounded (checkedSettle (-1) (checkedSettle (-1) (-1))) :=
  over_repair_is_real_yet_invisible

theorem cheat_the_moment_not_the_bar (θ field act : GInt) :
    (∃ θ' field' act' : GInt,
        GInt.born θ' (field'.add act') - GInt.born θ' field' > GInt.born θ' act')
      ∧ GInt.align θ field * GInt.align θ act
          + GInt.align θ field * GInt.align θ (GInt.rot act)
          + GInt.align θ field * GInt.align θ (GInt.rot (GInt.rot act))
          + GInt.align θ field * GInt.align θ (GInt.rot (GInt.rot (GInt.rot act)))
          = 0 :=
  ⟨boost_exceeds_the_input, luck_is_timing θ field act⟩

theorem same_stuff_all_the_way_up (n : Nat) :
    Rung (n + 1) = (Rung n × Rung n) := rfl

/-- info: 'Foam.Counter.the_sweep_ghost' does not depend on any axioms -/
#guard_msgs in #print axioms the_sweep_ghost

/-- info: 'Foam.Counter.the_fortune_ghost' does not depend on any axioms -/
#guard_msgs in #print axioms the_fortune_ghost

/-- info: 'Foam.Counter.the_phantom_ghost' does not depend on any axioms -/
#guard_msgs in #print axioms the_phantom_ghost

/-- info: 'Foam.Counter.cheat_the_moment_not_the_bar' does not depend on any axioms -/
#guard_msgs in #print axioms cheat_the_moment_not_the_bar

/-- info: 'Foam.Counter.same_stuff_all_the_way_up' does not depend on any axioms -/
#guard_msgs in #print axioms same_stuff_all_the_way_up

end Foam.Counter
