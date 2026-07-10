import Counter.Cable
import Foam.Wedge

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem a_wedge_inside_a_wedge_comes_home (S : Seat G) (gs : List G) (p : S.Pos) :
    S.replay (spine S gs p) p = p :=
  spine_comes_home S gs p

theorem resuming_means_the_inner_settled (S : Seat G) (g : G) (gs : List G) (p : S.Pos) :
    S.replay (g :: spine S gs (S.act g p)) p = S.act g p :=
  outer_resumes_where_it_paused S g gs p

theorem exits_stay_cost_free_at_depth (S : Seat G) (gs : List G) (p : S.Pos) :
    S.replay (collapse S gs p) p = p ∧ (collapse S gs p).length = gs.length + 1 :=
  ⟨collapse_comes_home S gs p, collapse_length S gs p⟩

theorem lifo_is_a_gait_not_a_law (S : Seat G) (gs : List G) (p : S.Pos) :
    S.replay (spine S gs p) p = p
      ∧ S.replay (collapse S gs p) p = p
      ∧ (spine S gs p).length = 2 * gs.length
      ∧ (collapse S gs p).length = gs.length + 1 :=
  lifo_is_a_gait S gs p

theorem the_inner_transcript_is_the_outer_backstage {W : Stage} (A : Bubble W)
    (ms ms' : List (W.State → W.State))
    (h : ∀ w, A.wall (enactAll ms w) = A.wall (enactAll ms' w))
    (w : W.State) (p : A.front.Probe) :
    A.front.obs (enactAll ms w) p = A.front.obs (enactAll ms' w) p :=
  histories_fold_at_the_wall A ms ms' h w p

theorem the_debt_is_real_upstairs_illegible_downstairs :
    ∃ ms ms' : List (twoBit.State → twoBit.State),
      ms.length ≠ ms'.length
        ∧ (∀ w p, firstBit.front.obs (enactAll ms w) p
            = firstBit.front.obs (enactAll ms' w) p)
        ∧ ∃ (w : twoBit.State) (pr : twoBit.Probe),
            twoBit.obs (enactAll ms w) pr ≠ twoBit.obs (enactAll ms' w) pr :=
  the_debt_outlives_its_legibility

theorem no_wedge_funds_itself {H : Type} (q : Quiver H) (a b c : H)
    (hab : (a, b) ∉ q) (hbc : (b, c) ∉ q.deposit (a, b)) :
    Nonempty (Path ((q.deposit (a, b)).deposit (b, c)) a c)
      ∧ (∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
      ∧ (∀ (x y : H) (pth : Path (q.deposit (a, b)) x y), (b, c) ∉ pth.edges) :=
  the_second_wedge_rides_the_first q a b c hab hbc

theorem what_this_thread_cannot_carry_another_does {W : Stage} (A : Bubble W)
    (m : W.State → W.State) (hfix : A.FixesWall m) (w : W.State) (hm : m w ≠ w) :
    (∀ (ps : List A.front.Probe) (ws : W.State),
        transcriptWith A.front m ws ps = transcript A.front ws ps)
      ∧ transcriptWith (plenum W.State) m w [()]
          ≠ transcript (plenum W.State) w [()] :=
  the_elsewhen_transcript A m hfix w hm

/-- info: 'Foam.Counter.a_wedge_inside_a_wedge_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms a_wedge_inside_a_wedge_comes_home

/-- info: 'Foam.Counter.resuming_means_the_inner_settled' does not depend on any axioms -/
#guard_msgs in #print axioms resuming_means_the_inner_settled

/-- info: 'Foam.Counter.exits_stay_cost_free_at_depth' does not depend on any axioms -/
#guard_msgs in #print axioms exits_stay_cost_free_at_depth

/-- info: 'Foam.Counter.lifo_is_a_gait_not_a_law' does not depend on any axioms -/
#guard_msgs in #print axioms lifo_is_a_gait_not_a_law

/-- info: 'Foam.Counter.the_inner_transcript_is_the_outer_backstage' does not depend on any axioms -/
#guard_msgs in #print axioms the_inner_transcript_is_the_outer_backstage

/-- info: 'Foam.Counter.the_debt_is_real_upstairs_illegible_downstairs' does not depend on any axioms -/
#guard_msgs in #print axioms the_debt_is_real_upstairs_illegible_downstairs

/-- info: 'Foam.Counter.no_wedge_funds_itself' does not depend on any axioms -/
#guard_msgs in #print axioms no_wedge_funds_itself

/-- info: 'Foam.Counter.what_this_thread_cannot_carry_another_does' does not depend on any axioms -/
#guard_msgs in #print axioms what_this_thread_cannot_carry_another_does

end Foam.Counter
