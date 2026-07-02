import Foam.Seat.Resume
import Foam.Seat.Observer

namespace Foam.Bridges

variable {G : Type} [Mul G] [One G]

def Endpoint (S : Foam.Seat G) (p : S.Pos) (h h' : List G) : Prop :=
  S.replay h p = S.replay h' p

theorem approach_is_yours (S : Foam.Seat G) (p : S.Pos) (h : List G)
    (hs : S.replay h p = p) : Endpoint S p h [] := hs

def Arrived (S : Foam.Seat G) (p : S.Pos) : Type := Quot (Endpoint S p)

theorem arrival_received (S : Foam.Seat G) (p : S.Pos) (h : List G)
    (hs : S.replay h p = p) :
    Quot.mk (Endpoint S p) h = Quot.mk (Endpoint S p) [] :=
  Quot.sound hs

theorem no_return (S : Foam.Seat G) (p : S.Pos) (h : List G)
    (hs : S.replay h p = p) (hne : h ≠ []) :
    ¬ ∃ g : Arrived S p → List G,
        ∀ l, g (Quot.mk (Endpoint S p) l) = l := by
  rintro ⟨g, hg⟩
  have e := congrArg g (arrival_received S p h hs)
  rw [hg, hg] at e
  exact hne e

theorem all_homecomings_are_one (S : Foam.Seat G) (p : S.Pos) (h h' : List G)
    (hs : S.replay h p = p) (hs' : S.replay h' p = p) :
    (S.replay h p = p) = (S.replay h' p = p) :=
  propext ⟨fun _ => hs', fun _ => hs⟩

theorem merged_reading {State Probe A : Type} (o : State → Probe → A)
    (s t : State) (hind : Foam.indist o s t) : o s = o t :=
  funext hind

/-- info: 'Foam.Bridges.approach_is_yours' does not depend on any axioms -/
#guard_msgs in #print axioms approach_is_yours

/-- info: 'Foam.Bridges.arrival_received' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms arrival_received

/-- info: 'Foam.Bridges.no_return' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms no_return

/-- info: 'Foam.Bridges.all_homecomings_are_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms all_homecomings_are_one

/-- info: 'Foam.Bridges.merged_reading' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms merged_reading

end Foam.Bridges
