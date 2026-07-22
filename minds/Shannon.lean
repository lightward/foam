import Foam
import Foam.Expectation
import Foam.Marks
import Foam.Surprise
import Foam.Width

namespace Foam.Minds.Shannon

theorem the_channel_is_the_only_commons :
    ∀ (S : Stage) (s : S.State) (n m : Int), n ≠ m → ∀ ps,
      transcript (dress S) (s, n) ps = transcript (dress S) (s, m) ps
        ∧ (s, n) ≠ (s, m) :=
  fun S s n m h ps =>
    ⟨transcript_congr (dress S) ps (the_remainder_is_unseen S s n m),
     fun he => h (congrArg Prod.snd he)⟩

theorem only_surprise_informs :
    ∀ (H : Type) (q : List (H × H)) (a b : H),
      ((a, b) ∈ q → Nonempty (Path q a b))
        ∧ (¬ (a, b) ∈ q →
            (∀ (x y : H) (p : Path q x y), ¬ (a, b) ∈ p.edges)
              ∧ Nonempty (Path ((a, b) :: q) a b)) :=
  fun _ q a b =>
    ⟨fun h => the_known_edge_already_reaches h,
     fun hfresh =>
      ⟨fun _ _ p => a_fresh_edge_rides_no_path hfresh p,
       (only_surprise_extends_reach q a b hfresh).2⟩⟩

def distinct_messages_need_distinct_marks := @Foam.the_hallway_is_too_small

theorem entropy_of_the_source :
    ∀ (n : Nat) (f : List Bool → List Bool),
      (∀ w1 w2, w1 ∈ book n → w2 ∈ book n → w1 ≠ w2 →
        ¬ ∃ t, f w1 ++ t = f w2) →
      n * (book n).length ≤ (pool ((book n).map f)).length :=
  the_marks_pay_the_depth

/-- info: 'Foam.Minds.Shannon.the_channel_is_the_only_commons' does not depend on any axioms -/
#guard_msgs in #print axioms the_channel_is_the_only_commons

/-- info: 'Foam.Minds.Shannon.only_surprise_informs' does not depend on any axioms -/
#guard_msgs in #print axioms only_surprise_informs

/-- info: 'Foam.Minds.Shannon.distinct_messages_need_distinct_marks' does not depend on any axioms -/
#guard_msgs in #print axioms distinct_messages_need_distinct_marks

/-- info: 'Foam.Minds.Shannon.entropy_of_the_source' does not depend on any axioms -/
#guard_msgs in #print axioms entropy_of_the_source

end Foam.Minds.Shannon
