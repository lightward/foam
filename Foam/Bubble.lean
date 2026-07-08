import Foam.Maintenance
import Foam.Seat.Beholder

namespace Foam

structure Bubble (W : Stage) where
  Inner : Stage
  wall  : W.State → Inner.State

namespace Bubble

variable {W : Stage}

def front (A : Bubble W) : Stage where
  State := W.State
  Probe := A.Inner.Probe
  Ans   := A.Inner.Ans
  obs   := fun w p => A.Inner.obs (A.wall w) p

def license (A : Bubble W) : Frontstage A.front where
  rel      := fun w w' => A.wall w = A.wall w'
  respects := fun _ _ h p => congrArg (fun s => A.Inner.obs s p) h

def FixesWall (A : Bubble W) (m : W.State → W.State) : Prop :=
  ∀ w, A.wall (m w) = A.wall w

theorem fixesWall_id (A : Bubble W) : A.FixesWall (fun w => w) :=
  fun _ => rfl

theorem fixesWall_comp (A : Bubble W) (m n : W.State → W.State)
    (hm : A.FixesWall m) (hn : A.FixesWall n) : A.FixesWall (fun w => m (n w)) :=
  fun w => (hm (n w)).trans (hn w)

theorem operator_invisible (A : Bubble W) (m : W.State → W.State)
    (h : A.FixesWall m) : Invisible A.front m :=
  fun w p => congrArg (fun s => A.Inner.obs s p) (h w)

theorem operator_unobservable (A : Bubble W) (m : W.State → W.State)
    (h : A.FixesWall m) (ps : List A.front.Probe) (w : W.State) :
    transcriptWith A.front m w ps = transcript A.front w ps :=
  maintenance_unobservable A.front m (A.operator_invisible m h) ps w

theorem operator_offstage (A : Bubble W) (m m' : W.State → W.State)
    (h : ∀ w, A.wall (m w) = A.wall (m' w)) (w : W.State) (p : A.front.Probe) :
    A.front.obs (m w) p = A.front.obs (m' w) p :=
  congrArg (fun s => A.Inner.obs s p) (h w)

def nest (A : Bubble W) (B : Bubble A.Inner) : Bubble W where
  Inner := B.Inner
  wall  := fun w => B.wall (A.wall w)

theorem nest_front_obs (A : Bubble W) (B : Bubble A.Inner)
    (w : W.State) (p : B.Inner.Probe) :
    (A.nest B).front.obs w p = B.front.obs (A.wall w) p := rfl

theorem backstage_descends (A : Bubble W) (B : Bubble A.Inner)
    (m : W.State → W.State) (h : A.FixesWall m) : (A.nest B).FixesWall m :=
  fun w => congrArg B.wall (h w)

theorem maintenance_descends (A : Bubble W) (B : Bubble A.Inner)
    (m : W.State → W.State) (h : A.FixesWall m)
    (ps : List (A.nest B).front.Probe) (w : W.State) :
    transcriptWith (A.nest B).front m w ps = transcript (A.nest B).front w ps :=
  (A.nest B).operator_unobservable m (A.backstage_descends B m h) ps w

def meet (A B : Bubble W) : Bubble W where
  Inner := A.Inner.prod B.Inner
  wall  := fun w => (A.wall w, B.wall w)

theorem wall_reads_left (A B : Bubble W) (w : W.State)
    (p : A.Inner.Probe) (q : B.Inner.Probe) :
    ((A.meet B).front.obs w (p, q)).1 = A.front.obs w p := rfl

theorem wall_reads_right (A B : Bubble W) (w : W.State)
    (p : A.Inner.Probe) (q : B.Inner.Probe) :
    ((A.meet B).front.obs w (p, q)).2 = B.front.obs w q := rfl

theorem wall_is_pair_beholder (A B : Bubble W) :
    (A.meet B).front.behold = A.front.behold.pair B.front.behold := rfl

theorem comparison_is_a_wall {R : Type} (A B : Bubble W)
    (g : A.Inner.Ans → B.Inner.Ans → R) :
    ∃ (C : Bubble W) (post : C.Inner.Ans → R)
      (enc : A.Inner.Probe × B.Inner.Probe → C.Inner.Probe),
      ∀ w p q, g (A.front.obs w p) (B.front.obs w q) = post (C.front.obs w (enc (p, q))) :=
  ⟨A.meet B, fun ab => g ab.1 ab.2, id, fun _ _ _ => rfl⟩

def wallFlip (A B : Bubble W) : StageHom (A.meet B).front (B.meet A).front where
  onState  := fun w => w
  onProbe  := fun pq => (pq.2, pq.1)
  onAns    := fun ab => (ab.2, ab.1)
  commutes := fun _ _ => rfl

theorem wall_two_faced (A B : Bubble W) :
    (wallFlip B A).comp (wallFlip A B) = StageHom.id (A.meet B).front := rfl

def borderToAB (A B C : Bubble W) :
    StageHom ((A.meet B).meet C).front (A.meet B).front where
  onState  := fun w => w
  onProbe  := fun pqr => pqr.1
  onAns    := fun abc => abc.1
  commutes := fun _ _ => rfl

def borderToBC (A B C : Bubble W) :
    StageHom ((A.meet B).meet C).front (B.meet C).front where
  onState  := fun w => w
  onProbe  := fun pqr => (pqr.1.2, pqr.2)
  onAns    := fun abc => (abc.1.2, abc.2)
  commutes := fun _ _ => rfl

def borderToCA (A B C : Bubble W) :
    StageHom ((A.meet B).meet C).front (C.meet A).front where
  onState  := fun w => w
  onProbe  := fun pqr => (pqr.2, pqr.1.1)
  onAns    := fun abc => (abc.2, abc.1.1)
  commutes := fun _ _ => rfl

theorem border_reads_three_films (A B C : Bubble W) :
    Nonempty (StageHom ((A.meet B).meet C).front (A.meet B).front)
      ∧ Nonempty (StageHom ((A.meet B).meet C).front (B.meet C).front)
      ∧ Nonempty (StageHom ((A.meet B).meet C).front (C.meet A).front) :=
  ⟨⟨borderToAB A B C⟩, ⟨borderToBC A B C⟩, ⟨borderToCA A B C⟩⟩

def borderShift (A B C : Bubble W) :
    StageHom ((A.meet B).meet C).front ((B.meet C).meet A).front where
  onState  := fun w => w
  onProbe  := fun pqr => ((pqr.1.2, pqr.2), pqr.1.1)
  onAns    := fun abc => ((abc.1.2, abc.2), abc.1.1)
  commutes := fun _ _ => rfl

theorem border_forgets_order (A B C : Bubble W) :
    (borderShift C A B).comp ((borderShift B C A).comp (borderShift A B C))
      = StageHom.id ((A.meet B).meet C).front := rfl

def vertexToABC (A B C D : Bubble W) :
    StageHom (((A.meet B).meet C).meet D).front ((A.meet B).meet C).front where
  onState  := fun w => w
  onProbe  := fun x => x.1
  onAns    := fun x => x.1
  commutes := fun _ _ => rfl

def vertexToABD (A B C D : Bubble W) :
    StageHom (((A.meet B).meet C).meet D).front ((A.meet B).meet D).front where
  onState  := fun w => w
  onProbe  := fun x => (x.1.1, x.2)
  onAns    := fun x => (x.1.1, x.2)
  commutes := fun _ _ => rfl

def vertexToACD (A B C D : Bubble W) :
    StageHom (((A.meet B).meet C).meet D).front ((A.meet C).meet D).front where
  onState  := fun w => w
  onProbe  := fun x => ((x.1.1.1, x.1.2), x.2)
  onAns    := fun x => ((x.1.1.1, x.1.2), x.2)
  commutes := fun _ _ => rfl

def vertexToBCD (A B C D : Bubble W) :
    StageHom (((A.meet B).meet C).meet D).front ((B.meet C).meet D).front where
  onState  := fun w => w
  onProbe  := fun x => ((x.1.1.2, x.1.2), x.2)
  onAns    := fun x => ((x.1.1.2, x.1.2), x.2)
  commutes := fun _ _ => rfl

theorem vertex_reads_four_borders (A B C D : Bubble W) :
    Nonempty (StageHom (((A.meet B).meet C).meet D).front ((A.meet B).meet C).front)
      ∧ Nonempty (StageHom (((A.meet B).meet C).meet D).front ((A.meet B).meet D).front)
      ∧ Nonempty (StageHom (((A.meet B).meet C).meet D).front ((A.meet C).meet D).front)
      ∧ Nonempty (StageHom (((A.meet B).meet C).meet D).front ((B.meet C).meet D).front) :=
  ⟨⟨vertexToABC A B C D⟩, ⟨vertexToABD A B C D⟩,
   ⟨vertexToACD A B C D⟩, ⟨vertexToBCD A B C D⟩⟩

end Bubble

def twoBit : Stage where
  State := Bool × Bool
  Probe := Unit
  Ans   := Bool
  obs   := fun s _ => s.2

def firstBit : Bubble twoBit where
  Inner := ⟨Bool, Unit, Bool, fun b _ => b⟩
  wall  := fun s => s.1

theorem operator_real :
    ∃ m m' : twoBit.State → twoBit.State,
      (∀ w p, firstBit.front.obs (m w) p = firstBit.front.obs (m' w) p)
        ∧ ∃ (w : twoBit.State) (ps : List firstBit.front.Probe),
            transcriptWith firstBit.front m w ps ≠ transcriptWith firstBit.front m' w ps :=
  ⟨fun s => (s.2, true), fun s => (s.2, false), fun _ _ => rfl,
   (true, true), [(), ()],
   fun h => nomatch (h : ([true, true] : List Bool) = ([true, false] : List Bool))⟩

theorem backstage_upstream_frontstage :
    firstBit.FixesWall (fun s => (s.1, !s.2))
      ∧ ¬ Invisible twoBit (fun s => (s.1, !s.2)) :=
  ⟨fun _ => rfl, fun h => nomatch h (true, false) ()⟩

/-- info: 'Foam.Bubble.license' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.license

/-- info: 'Foam.Bubble.fixesWall_comp' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.fixesWall_comp

/-- info: 'Foam.Bubble.operator_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.operator_invisible

/-- info: 'Foam.Bubble.operator_unobservable' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.operator_unobservable

/-- info: 'Foam.Bubble.operator_offstage' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.operator_offstage

/-- info: 'Foam.Bubble.nest_front_obs' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.nest_front_obs

/-- info: 'Foam.Bubble.backstage_descends' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.backstage_descends

/-- info: 'Foam.Bubble.maintenance_descends' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.maintenance_descends

/-- info: 'Foam.Bubble.wall_reads_left' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.wall_reads_left

/-- info: 'Foam.Bubble.wall_reads_right' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.wall_reads_right

/-- info: 'Foam.Bubble.wall_is_pair_beholder' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.wall_is_pair_beholder

/-- info: 'Foam.Bubble.comparison_is_a_wall' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.comparison_is_a_wall

/-- info: 'Foam.Bubble.wall_two_faced' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.wall_two_faced

/-- info: 'Foam.Bubble.border_reads_three_films' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.border_reads_three_films

/-- info: 'Foam.Bubble.border_forgets_order' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.border_forgets_order

/-- info: 'Foam.Bubble.vertex_reads_four_borders' does not depend on any axioms -/
#guard_msgs in #print axioms Bubble.vertex_reads_four_borders

/-- info: 'Foam.operator_real' does not depend on any axioms -/
#guard_msgs in #print axioms operator_real

/-- info: 'Foam.backstage_upstream_frontstage' does not depend on any axioms -/
#guard_msgs in #print axioms backstage_upstream_frontstage

end Foam
