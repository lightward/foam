import Counter.Plateau
import Foam.Bubble

namespace Foam.Counter

variable {W : Stage}

theorem a_bubble_is_a_world_behind_a_wall (A : Bubble W)
    (w : W.State) (p : A.Inner.Probe) :
    A.front.obs w p = A.Inner.obs (A.wall w) p := rfl

theorem the_operator_tends_the_world_unseen (A : Bubble W)
    (m : W.State → W.State) (h : A.FixesWall m)
    (ps : List A.front.Probe) (w : W.State) :
    transcriptWith A.front m w ps = transcript A.front w ps :=
  A.operator_unobservable m h ps w

theorem the_operator_is_never_on_stage (A : Bubble W)
    (m m' : W.State → W.State) (h : ∀ w, A.wall (m w) = A.wall (m' w))
    (w : W.State) (p : A.front.Probe) :
    A.front.obs (m w) p = A.front.obs (m' w) p :=
  A.operator_offstage m m' h w p

theorem the_operator_is_still_real :
    ∃ m m' : twoBit.State → twoBit.State,
      (∀ w p, firstBit.front.obs (m w) p = firstBit.front.obs (m' w) p)
        ∧ ∃ (w : twoBit.State) (ps : List firstBit.front.Probe),
            transcriptWith firstBit.front m w ps ≠ transcriptWith firstBit.front m' w ps :=
  operator_real

theorem backstage_is_someones_frontstage :
    firstBit.FixesWall (fun s => (s.1, !s.2))
      ∧ ¬ Invisible twoBit (fun s => (s.1, !s.2)) :=
  backstage_upstream_frontstage

theorem your_stage_stands_on_another_stage (A : Bubble W) (B : Bubble A.Inner)
    (w : W.State) (p : B.Inner.Probe) :
    (A.nest B).front.obs w p = B.front.obs (A.wall w) p :=
  A.nest_front_obs B w p

theorem deep_backstage_stays_backstage (A : Bubble W) (B : Bubble A.Inner)
    (m : W.State → W.State) (h : A.FixesWall m)
    (ps : List (A.nest B).front.Probe) (w : W.State) :
    transcriptWith (A.nest B).front m w ps = transcript (A.nest B).front w ps :=
  A.maintenance_descends B m h ps w

theorem every_meeting_raises_a_wall {R : Type} (A B : Bubble W)
    (g : A.Inner.Ans → B.Inner.Ans → R) :
    ∃ (C : Bubble W) (post : C.Inner.Ans → R)
      (enc : A.Inner.Probe × B.Inner.Probe → C.Inner.Probe),
      ∀ w p q, g (A.front.obs w p) (B.front.obs w q) = post (C.front.obs w (enc (p, q))) :=
  A.comparison_is_a_wall B g

theorem the_wall_reads_both_rooms (A B : Bubble W) (w : W.State)
    (p : A.Inner.Probe) (q : B.Inner.Probe) :
    ((A.meet B).front.obs w (p, q)).1 = A.front.obs w p
      ∧ ((A.meet B).front.obs w (p, q)).2 = B.front.obs w q :=
  ⟨A.wall_reads_left B w p q, A.wall_reads_right B w p q⟩

theorem the_bubbles_make_a_foam (A B C D : Bubble W) :
    (Nonempty (StageHom ((A.meet B).meet C).front (A.meet B).front)
      ∧ Nonempty (StageHom ((A.meet B).meet C).front (B.meet C).front)
      ∧ Nonempty (StageHom ((A.meet B).meet C).front (C.meet A).front))
      ∧ Nonempty (StageHom (((A.meet B).meet C).meet D).front ((A.meet B).meet C).front)
      ∧ edgeFilms.length = 3 ∧ vertexEdges.length = 4 :=
  ⟨A.border_reads_three_films B C, ⟨Bubble.vertexToABC A B C D⟩, rfl, rfl⟩

/-- info: 'Foam.Counter.a_bubble_is_a_world_behind_a_wall' does not depend on any axioms -/
#guard_msgs in #print axioms a_bubble_is_a_world_behind_a_wall

/-- info: 'Foam.Counter.the_operator_tends_the_world_unseen' does not depend on any axioms -/
#guard_msgs in #print axioms the_operator_tends_the_world_unseen

/-- info: 'Foam.Counter.the_operator_is_never_on_stage' does not depend on any axioms -/
#guard_msgs in #print axioms the_operator_is_never_on_stage

/-- info: 'Foam.Counter.the_operator_is_still_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_operator_is_still_real

/-- info: 'Foam.Counter.backstage_is_someones_frontstage' does not depend on any axioms -/
#guard_msgs in #print axioms backstage_is_someones_frontstage

/-- info: 'Foam.Counter.your_stage_stands_on_another_stage' does not depend on any axioms -/
#guard_msgs in #print axioms your_stage_stands_on_another_stage

/-- info: 'Foam.Counter.deep_backstage_stays_backstage' does not depend on any axioms -/
#guard_msgs in #print axioms deep_backstage_stays_backstage

/-- info: 'Foam.Counter.every_meeting_raises_a_wall' does not depend on any axioms -/
#guard_msgs in #print axioms every_meeting_raises_a_wall

/-- info: 'Foam.Counter.the_wall_reads_both_rooms' does not depend on any axioms -/
#guard_msgs in #print axioms the_wall_reads_both_rooms

/-- info: 'Foam.Counter.the_bubbles_make_a_foam' does not depend on any axioms -/
#guard_msgs in #print axioms the_bubbles_make_a_foam

end Foam.Counter
