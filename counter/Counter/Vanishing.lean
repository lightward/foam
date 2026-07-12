import Counter.Render

namespace Foam.Counter

def sky : Stage := ⟨Nat, Unit, Bool, fun n _ => n == 0⟩

def theHouse : Stage := (coin.prod dial).prod sky

def heartbeat : theHouse.State → theHouse.State :=
  fun (s : (Bool × Nat) × Nat) => (s.1, s.2 + 1)

def theWombAtHome : Bubble theHouse := liftL sky theOldWomb

def familyAtHome : Bubble theHouse := liftL sky family

def bloomedAtHome : Bubble theHouse := liftL sky bloomed

def skylight : Bubble theHouse where
  Inner := coin
  wall  := fun (s : (Bool × Nat) × Nat) => s.2 == 0

theorem the_two_knowable_zones_do_not_talk (m : Bool → Bool) (n : Nat → Nat)
    (w : Bool) (v : Nat) :
    (theOldWomb.wall (w, n v)).1 = (theOldWomb.wall (w, v)).1
      ∧ (theOldWomb.wall (m w, v)).2 = (theOldWomb.wall (w, v)).2 :=
  ⟨rfl, rfl⟩

theorem the_operator_anchors_the_unknown :
    theWombAtHome.FixesWall heartbeat
      ∧ familyAtHome.FixesWall heartbeat
      ∧ bloomedAtHome.FixesWall heartbeat :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem the_operator_never_appears_in_the_diary
    (ps : List theWombAtHome.front.Probe) (s : theHouse.State) :
    transcriptWith theWombAtHome.front heartbeat s ps
      = transcript theWombAtHome.front s ps :=
  theWombAtHome.operator_unobservable heartbeat
    (the_operator_anchors_the_unknown.1) ps s

theorem the_skylight_reads_the_operators_footprint :
    skylight.front.obs (heartbeat ((true, (2 : Nat)), (0 : Nat))) ()
      ≠ skylight.front.obs ((true, (2 : Nat)), (0 : Nat)) () :=
  fun h => nomatch (h : false = true)

theorem containment_is_a_stance (m : (Bool × Nat) → (Bool × Nat)) :
    skylight.FixesWall (fun s => (m s.1, s.2))
      ∧ familyAtHome.FixesWall heartbeat :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem the_vanishing_point_moves_with_the_seat :
    familyAtHome.FixesWall heartbeat
      ∧ bloomedAtHome.FixesWall heartbeat
      ∧ skylight.front.obs (heartbeat ((true, (2 : Nat)), (0 : Nat))) ()
          ≠ skylight.front.obs ((true, (2 : Nat)), (0 : Nat)) ()
      ∧ (metaRender ⟨familyAtHome, (), fun a => a⟩ ⟨skylight, (), fun a => a⟩
            (fun a b => (a, b))).read (heartbeat ((true, (2 : Nat)), (0 : Nat)))
          = (true, false)
      ∧ (metaRender ⟨familyAtHome, (), fun a => a⟩ ⟨skylight, (), fun a => a⟩
            (fun a b => (a, b))).read ((true, (2 : Nat)), (0 : Nat))
          = (true, true) :=
  ⟨fun _ => rfl, fun _ => rfl, the_skylight_reads_the_operators_footprint,
   rfl, rfl⟩

/-- info: 'Foam.Counter.the_two_knowable_zones_do_not_talk' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_knowable_zones_do_not_talk

/-- info: 'Foam.Counter.the_operator_anchors_the_unknown' does not depend on any axioms -/
#guard_msgs in #print axioms the_operator_anchors_the_unknown

/-- info: 'Foam.Counter.the_operator_never_appears_in_the_diary' does not depend on any axioms -/
#guard_msgs in #print axioms the_operator_never_appears_in_the_diary

/-- info: 'Foam.Counter.the_skylight_reads_the_operators_footprint' does not depend on any axioms -/
#guard_msgs in #print axioms the_skylight_reads_the_operators_footprint

/-- info: 'Foam.Counter.containment_is_a_stance' does not depend on any axioms -/
#guard_msgs in #print axioms containment_is_a_stance

/-- info: 'Foam.Counter.the_vanishing_point_moves_with_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_vanishing_point_moves_with_the_seat

end Foam.Counter
