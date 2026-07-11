import Foam.Bubble

namespace Foam.Counter

def liftL {W : Stage} (V : Stage) (A : Bubble W) : Bubble (W.prod V) where
  Inner := A.Inner
  wall  := fun wv => A.wall wv.1

def liftR (W : Stage) {V : Stage} (B : Bubble V) : Bubble (W.prod V) where
  Inner := B.Inner
  wall  := fun wv => B.wall wv.2

def conceive {W : Stage} (A B : Bubble W)
    (g : Bubble (A.Inner.prod B.Inner)) : Bubble W :=
  (A.meet B).nest g

def conceiveAcross {W V : Stage} (A : Bubble W) (B : Bubble V)
    (g : Bubble (A.Inner.prod B.Inner)) : Bubble (W.prod V) :=
  ((liftL V A).meet (liftR W B)).nest g

def newbornGerm (I : Stage) : Bubble I where
  Inner := ⟨Unit, Unit, Unit, fun _ _ => ()⟩
  wall  := fun _ => ()

def watcher {W V : Stage} {R : Type} (A : Bubble W) (B : Bubble V)
    (g : A.Inner.Ans → B.Inner.Ans → R) : Bubble (A.Inner.prod B.Inner) where
  Inner := ⟨A.Inner.State × B.Inner.State, A.Inner.Probe × B.Inner.Probe, R,
    fun st pq => g (A.Inner.obs st.1 pq.1) (B.Inner.obs st.2 pq.2)⟩
  wall  := fun st => st

def coin : Stage := ⟨Bool, Unit, Bool, fun b _ => b⟩

def dial : Stage := ⟨Nat, Unit, Bool, fun n _ => n % 2 == 1⟩

def coinBubble : Bubble coin where
  Inner := coin
  wall  := fun b => b

def dialBubble : Bubble dial where
  Inner := coin
  wall  := fun (n : Nat) => n % 2 == 1

def xorGerm : Bubble (coin.prod coin) where
  Inner := coin
  wall  := fun bb => Bool.xor bb.1 bb.2

def family : Bubble (coin.prod dial) :=
  conceiveAcross coinBubble dialBubble xorGerm

theorem my_readings_survive_the_move {W V : Stage} (A : Bubble W)
    (w : W.State) (v : V.State) (p : A.Inner.Probe) :
    (liftL V A).front.obs (w, v) p = A.front.obs w p := rfl

theorem your_readings_survive_the_move {W V : Stage} (B : Bubble V)
    (w : W.State) (v : V.State) (q : B.Inner.Probe) :
    (liftR W B).front.obs (w, v) q = B.front.obs v q := rfl

theorem your_weather_is_my_backstage {W V : Stage} (A : Bubble W)
    (n : V.State → V.State) :
    (liftL V A).FixesWall (fun wv => (wv.1, n wv.2)) :=
  fun _ => rfl

theorem your_storms_never_touch_my_transcript {W V : Stage} (A : Bubble W)
    (n : V.State → V.State) (ps : List (liftL V A).front.Probe)
    (wv : (W.prod V).State) :
    transcriptWith (liftL V A).front (fun wv => (wv.1, n wv.2)) wv ps
      = transcript (liftL V A).front wv ps :=
  (liftL V A).operator_unobservable _ (your_weather_is_my_backstage A n) ps wv

theorem the_meet_is_the_womb {W : Stage} (A B : Bubble W)
    (g : Bubble (A.Inner.prod B.Inner)) :
    conceive A B g = (A.meet B).nest g := rfl

theorem both_lineages_run_in_the_loop {W : Stage} (A B : Bubble W)
    (g : Bubble (A.Inner.prod B.Inner)) (w : W.State) (p : g.Inner.Probe) :
    (conceive A B g).front.obs w p = g.front.obs (A.wall w, B.wall w) p := rfl

theorem the_ancestors_watch_over_the_child {W : Stage} (A B : Bubble W)
    (g : Bubble (A.Inner.prod B.Inner)) (m : W.State → W.State)
    (ha : A.FixesWall m) (hb : B.FixesWall m) :
    (conceive A B g).FixesWall m := by
  intro w
  show g.wall (A.wall (m w), B.wall (m w)) = g.wall (A.wall w, B.wall w)
  rw [ha w, hb w]

theorem the_watch_keeps_every_transcript {W : Stage} (A B : Bubble W)
    (g : Bubble (A.Inner.prod B.Inner)) (m : W.State → W.State)
    (ha : A.FixesWall m) (hb : B.FixesWall m)
    (ps : List (conceive A B g).front.Probe) (w : W.State) :
    transcriptWith (conceive A B g).front m w ps
      = transcript (conceive A B g).front w ps :=
  (conceive A B g).operator_unobservable m
    (the_ancestors_watch_over_the_child A B g m ha hb) ps w

theorem the_child_cannot_outsee_its_ancestry {W : Stage} (A B : Bubble W)
    (g : Bubble (A.Inner.prod B.Inner)) (w w' : W.State)
    (ha : A.wall w = A.wall w') (hb : B.wall w = B.wall w')
    (p : g.Inner.Probe) :
    (conceive A B g).front.obs w p = (conceive A B g).front.obs w' p := by
  show g.Inner.obs (g.wall (A.wall w, B.wall w)) p
    = g.Inner.obs (g.wall (A.wall w', B.wall w')) p
  rw [ha, hb]

theorem the_newborn_arrives_zero_knowledge {W : Stage} (A B : Bubble W)
    (w w' : W.State) (p : Unit) :
    (conceive A B (newbornGerm (A.Inner.prod B.Inner))).front.obs w p
      = (conceive A B (newbornGerm (A.Inner.prod B.Inner))).front.obs w' p := rfl

theorem the_world_is_backstage_to_the_newborn {W : Stage} (A B : Bubble W)
    (m : W.State → W.State) :
    (conceive A B (newbornGerm (A.Inner.prod B.Inner))).FixesWall m :=
  fun _ => rfl

theorem the_touch_seats_a_peer {W : Stage} (A : Bubble W) (B : Bubble A.Inner)
    (w : W.State) (p : B.Inner.Probe) (q : A.Inner.Probe) :
    ((A.nest B).meet A).front.obs w (p, q)
      = (B.front.obs (A.wall w) p, A.front.obs w q) := rfl

theorem the_tree_survives_the_touch {W : Stage} (A : Bubble W)
    (B : Bubble A.Inner) :
    (A.nest B).wall = (fun w => B.wall (A.wall w))
      ∧ ∀ m : W.State → W.State, A.FixesWall m → (A.nest B).FixesWall m :=
  ⟨rfl, fun m h => A.backstage_descends B m h⟩

theorem the_peer_meets_strangers {W : Stage} {R : Type} (A : Bubble W)
    (B : Bubble A.Inner) (C : Bubble W)
    (g : B.Inner.Ans → C.Inner.Ans → R) :
    ∃ (D : Bubble W) (post : D.Inner.Ans → R)
      (enc : B.Inner.Probe × C.Inner.Probe → D.Inner.Probe),
      ∀ w p q, g ((A.nest B).front.obs w p) (C.front.obs w q)
        = post (D.front.obs w (enc (p, q))) :=
  Bubble.comparison_is_a_wall (A.nest B) C g

theorem the_parents_never_met {W V : Stage} (A : Bubble W) (B : Bubble V)
    (g : Bubble (A.Inner.prod B.Inner)) (w : W.State) (v : V.State)
    (p : g.Inner.Probe) :
    (conceiveAcross A B g).front.obs (w, v) p
      = g.front.obs (A.wall w, B.wall v) p := rfl

theorem the_ancestors_watch_from_both_worlds {W V : Stage} (A : Bubble W)
    (B : Bubble V) (g : Bubble (A.Inner.prod B.Inner))
    (m : W.State → W.State) (n : V.State → V.State)
    (ha : A.FixesWall m) (hb : B.FixesWall n) :
    (conceiveAcross A B g).FixesWall (fun wv => (m wv.1, n wv.2)) := by
  intro wv
  show g.wall (A.wall (m wv.1), B.wall (n wv.2))
    = g.wall (A.wall wv.1, B.wall wv.2)
  rw [ha wv.1, hb wv.2]

theorem the_child_cannot_tell_if_its_parents_shared_a_world {W : Stage}
    (A B : Bubble W) (g : Bubble (A.Inner.prod B.Inner)) (w : W.State)
    (p : g.Inner.Probe) :
    (conceive A B g).front.obs w p
      = (conceiveAcross A B g).front.obs (w, w) p := rfl

theorem we_see_each_other_through_our_descendant {W V : Stage} {R : Type}
    (A : Bubble W) (B : Bubble V) (g : A.Inner.Ans → B.Inner.Ans → R)
    (w : W.State) (v : V.State) (p : A.Inner.Probe) (q : B.Inner.Probe) :
    (conceiveAcross A B (watcher A B g)).front.obs (w, v) (p, q)
      = g (A.front.obs w p) (B.front.obs v q) := rfl

theorem two_worlds_one_child (b : Bool) (n : Nat) :
    family.front.obs (b, n) () = Bool.xor b (n % 2 == 1) := rfl

theorem the_child_reads_across_worlds :
    family.front.obs (true, (4 : Nat)) () = true
      ∧ family.front.obs (true, (3 : Nat)) () = false :=
  ⟨rfl, rfl⟩

theorem the_foam_is_a_family {W V : Stage} {R : Type} (A : Bubble W)
    (B : Bubble V) (g : A.Inner.Ans → B.Inner.Ans → R)
    (n : V.State → V.State) (w : W.State) (v : V.State)
    (p : A.Inner.Probe) (q : B.Inner.Probe) :
    (liftL V A).front.obs (w, v) p = A.front.obs w p
      ∧ (liftL V A).FixesWall (fun wv => (wv.1, n wv.2))
      ∧ (conceiveAcross A B (watcher A B g)).front.obs (w, v) (p, q)
          = g (A.front.obs w p) (B.front.obs v q)
      ∧ (conceiveAcross A B (watcher A B g)).wall
          = (fun wv => ((liftL V A).wall wv, (liftR W B).wall wv)) :=
  ⟨rfl, fun _ => rfl, rfl, rfl⟩

/-- info: 'Foam.Counter.my_readings_survive_the_move' does not depend on any axioms -/
#guard_msgs in #print axioms my_readings_survive_the_move

/-- info: 'Foam.Counter.your_readings_survive_the_move' does not depend on any axioms -/
#guard_msgs in #print axioms your_readings_survive_the_move

/-- info: 'Foam.Counter.your_weather_is_my_backstage' does not depend on any axioms -/
#guard_msgs in #print axioms your_weather_is_my_backstage

/-- info: 'Foam.Counter.your_storms_never_touch_my_transcript' does not depend on any axioms -/
#guard_msgs in #print axioms your_storms_never_touch_my_transcript

/-- info: 'Foam.Counter.the_meet_is_the_womb' does not depend on any axioms -/
#guard_msgs in #print axioms the_meet_is_the_womb

/-- info: 'Foam.Counter.both_lineages_run_in_the_loop' does not depend on any axioms -/
#guard_msgs in #print axioms both_lineages_run_in_the_loop

/-- info: 'Foam.Counter.the_ancestors_watch_over_the_child' does not depend on any axioms -/
#guard_msgs in #print axioms the_ancestors_watch_over_the_child

/-- info: 'Foam.Counter.the_watch_keeps_every_transcript' does not depend on any axioms -/
#guard_msgs in #print axioms the_watch_keeps_every_transcript

/-- info: 'Foam.Counter.the_child_cannot_outsee_its_ancestry' does not depend on any axioms -/
#guard_msgs in #print axioms the_child_cannot_outsee_its_ancestry

/-- info: 'Foam.Counter.the_newborn_arrives_zero_knowledge' does not depend on any axioms -/
#guard_msgs in #print axioms the_newborn_arrives_zero_knowledge

/-- info: 'Foam.Counter.the_world_is_backstage_to_the_newborn' does not depend on any axioms -/
#guard_msgs in #print axioms the_world_is_backstage_to_the_newborn

/-- info: 'Foam.Counter.the_touch_seats_a_peer' does not depend on any axioms -/
#guard_msgs in #print axioms the_touch_seats_a_peer

/-- info: 'Foam.Counter.the_tree_survives_the_touch' does not depend on any axioms -/
#guard_msgs in #print axioms the_tree_survives_the_touch

/-- info: 'Foam.Counter.the_peer_meets_strangers' does not depend on any axioms -/
#guard_msgs in #print axioms the_peer_meets_strangers

/-- info: 'Foam.Counter.the_parents_never_met' does not depend on any axioms -/
#guard_msgs in #print axioms the_parents_never_met

/-- info: 'Foam.Counter.the_ancestors_watch_from_both_worlds' does not depend on any axioms -/
#guard_msgs in #print axioms the_ancestors_watch_from_both_worlds

/-- info: 'Foam.Counter.the_child_cannot_tell_if_its_parents_shared_a_world' does not depend on any axioms -/
#guard_msgs in #print axioms the_child_cannot_tell_if_its_parents_shared_a_world

/-- info: 'Foam.Counter.we_see_each_other_through_our_descendant' does not depend on any axioms -/
#guard_msgs in #print axioms we_see_each_other_through_our_descendant

/-- info: 'Foam.Counter.two_worlds_one_child' does not depend on any axioms -/
#guard_msgs in #print axioms two_worlds_one_child

/-- info: 'Foam.Counter.the_child_reads_across_worlds' does not depend on any axioms -/
#guard_msgs in #print axioms the_child_reads_across_worlds

/-- info: 'Foam.Counter.the_foam_is_a_family' does not depend on any axioms -/
#guard_msgs in #print axioms the_foam_is_a_family

end Foam.Counter
