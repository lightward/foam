import Counter.Laugh

namespace Foam.Counter

def bubbleOfHom {S T : Stage} (f : StageHom S T) : Bubble S where
  Inner := T
  wall  := f.onState

def renderOf {W : Stage} {R : Type} (A : Bubble W) (p : A.Inner.Probe)
    (l : A.Inner.Ans → R) : Render W R where
  seat  := A
  probe := p
  lens  := l

def naked (W : Stage) : Bubble W where
  Inner := W
  wall  := fun w => w

theorem a_bubble_is_its_own_punchline {W : Stage} (A : Bubble W) :
    (bubbleOfHom (punchline A)).Inner = A.Inner
      ∧ (bubbleOfHom (punchline A)).wall = A.wall :=
  ⟨rfl, rfl⟩

theorem a_bubble_renders {W : Stage} {R : Type} (A : Bubble W)
    (p : A.Inner.Probe) (l : A.Inner.Ans → R) (w : W.State) :
    (renderOf A p l).read w = l (A.front.obs w p) := rfl

theorem a_render_is_a_seated_cell {W : Stage} {R : Type} (v : Render W R) :
    renderOf v.seat v.probe v.lens = v := rfl

theorem a_bubble_is_arrow_and_render {W : Stage} {R : Type} (A : Bubble W)
    (p : A.Inner.Probe) (l : A.Inner.Ans → R) (w : W.State) :
    (bubbleOfHom (punchline A)).wall = A.wall
      ∧ (punchline A).onState = A.wall
      ∧ (renderOf A p l).read w = l (A.front.obs w p) :=
  ⟨rfl, rfl, rfl⟩

theorem the_spec_reduces {W : Stage} (S : Stage) (A : Bubble W)
    {R : Type} (v : Render W R) :
    S.behold.toStage = S
      ∧ (bubbleOfHom (punchline A)).wall = A.wall
      ∧ renderOf v.seat v.probe v.lens = v :=
  ⟨rfl, rfl, rfl⟩

theorem no_wall_no_backstage {W : Stage} (m : W.State → W.State)
    (h : (naked W).FixesWall m) : ∀ w, m w = w :=
  h

theorem the_wall_is_the_slack {W : Stage} (A : Bubble W)
    (m : W.State → W.State) (h : A.FixesWall m)
    (ps : List A.front.Probe) (w : W.State) :
    transcriptWith A.front m w ps = transcript A.front w ps :=
  A.operator_unobservable m h ps w

/-- info: 'Foam.Counter.a_bubble_is_its_own_punchline' does not depend on any axioms -/
#guard_msgs in #print axioms a_bubble_is_its_own_punchline

/-- info: 'Foam.Counter.a_bubble_renders' does not depend on any axioms -/
#guard_msgs in #print axioms a_bubble_renders

/-- info: 'Foam.Counter.a_render_is_a_seated_cell' does not depend on any axioms -/
#guard_msgs in #print axioms a_render_is_a_seated_cell

/-- info: 'Foam.Counter.a_bubble_is_arrow_and_render' does not depend on any axioms -/
#guard_msgs in #print axioms a_bubble_is_arrow_and_render

/-- info: 'Foam.Counter.the_spec_reduces' does not depend on any axioms -/
#guard_msgs in #print axioms the_spec_reduces

/-- info: 'Foam.Counter.no_wall_no_backstage' does not depend on any axioms -/
#guard_msgs in #print axioms no_wall_no_backstage

/-- info: 'Foam.Counter.the_wall_is_the_slack' does not depend on any axioms -/
#guard_msgs in #print axioms the_wall_is_the_slack

end Foam.Counter
