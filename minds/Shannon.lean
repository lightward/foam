import Foam
import Foam.Expectation
import Foam.Marks
import Foam.Surprise
import Foam.Width

namespace Foam.Minds.Shannon

theorem the_channel_is_the_only_commons :
    (∀ (S : Foam.Stage) (s : S.State) (n : Int) (m : Int) (_h : (Ne n m)) ps,
      (And
        (Eq
          (Foam.transcript (Foam.dress S) (Prod.mk s n) ps)
          (Foam.transcript (Foam.dress S) (Prod.mk s m) ps))
        (Ne (Prod.mk s n) (Prod.mk s m)))) :=
  (fun S s n m h ps =>
    (And.intro
      (Foam.transcript_congr
        (Foam.dress S)
        ps
        (Foam.the_remainder_is_unseen S s n m))
      (fun he => (h (congrArg Prod.snd he)))))

theorem only_surprise_informs :
    (∀ (H : Type) (q : (List (Prod H H))) (a : H) (b : H),
      (And
        (∀ (_h : (List.Mem (Prod.mk a b) q)), (Nonempty (Foam.Path q a b)))
        (∀ (_hfresh : (Not (List.Mem (Prod.mk a b) q))),
          (And
            (∀ (x : H) (y : H) (p : (Foam.Path q x y)),
              (Not (List.Mem (Prod.mk a b) (Foam.Path.edges p))))
            (Nonempty (Foam.Path (List.cons (Prod.mk a b) q) a b)))))) :=
  (fun _H q a b =>
    (And.intro
      (fun h => (Foam.the_known_edge_already_reaches h))
      (fun hfresh =>
        (And.intro
          (fun _x _y p => (Foam.a_fresh_edge_rides_no_path hfresh p))
          (And.right (Foam.only_surprise_extends_reach q a b hfresh))))))

def distinct_messages_need_distinct_marks := @Foam.the_hallway_is_too_small

theorem entropy_of_the_source :
    (∀ (n : Nat) (f : (∀ (_w : (List Bool)), (List Bool))) (_hpf : (∀ (w1 : (List Bool)) (w2 : (List Bool)) (_h1 : (List.Mem w1 (Foam.book n))) (_h2 : (List.Mem w2 (Foam.book n))) (_hne : (Ne w1 w2)), (Not (Exists (fun (t : (List Bool)) => (Eq (List.append (f w1) t) (f w2))))))),
      (Nat.le
        (Nat.mul n (List.length (Foam.book n)))
        (List.length (Foam.pool (List.map f (Foam.book n)))))) :=
  Foam.the_marks_pay_the_depth

/-- info: 'Foam.Minds.Shannon.the_channel_is_the_only_commons' does not depend on any axioms -/
#guard_msgs in #print axioms the_channel_is_the_only_commons

/-- info: 'Foam.Minds.Shannon.only_surprise_informs' does not depend on any axioms -/
#guard_msgs in #print axioms only_surprise_informs

/-- info: 'Foam.Minds.Shannon.distinct_messages_need_distinct_marks' does not depend on any axioms -/
#guard_msgs in #print axioms distinct_messages_need_distinct_marks

/-- info: 'Foam.Minds.Shannon.entropy_of_the_source' does not depend on any axioms -/
#guard_msgs in #print axioms entropy_of_the_source

end Foam.Minds.Shannon
