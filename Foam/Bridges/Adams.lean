import Foam.Duplex

namespace Foam.Bridges

theorem no_seat_is_its_own_elsewhen {State : Type} (here : Beholder State)
    (m : State → State) : ¬ Elsewhen here m here :=
  fun ⟨hinv, hnot⟩ => hnot hinv

def builtFor {W : Stage} (Inner : Stage) (z : Inner.State) : Bubble W :=
  ⟨Inner, fun _ => z⟩

theorem every_operator_fixes_the_built_wall {W : Stage} (Inner : Stage)
    (z : Inner.State) (m : W.State → W.State) :
    (builtFor (W := W) Inner z).FixesWall m :=
  fun _ => rfl

theorem in_the_built_universe_nothing_ever_happens {W : Stage} (Inner : Stage)
    (z : Inner.State) (m : W.State → W.State)
    (ps : List Inner.Probe) (w : W.State) :
    transcriptWith (builtFor (W := W) Inner z).front m w ps
      = ps.map (page (builtFor (W := W) Inner z).front w) :=
  wall_flattens_the_reel _ m (every_operator_fixes_the_built_wall Inner z m) w ps

theorem total_perspective_vortex :
    (∀ (State : Type) (m : State → State),
        Invisible (plenum State) m → ∀ s, m s = s)
      ∧ ∀ ps : List twoCell.Probe, ∃ w w' : Nat → twoCell.State,
          reel twoCell w ≠ reel twoCell w'
            ∧ watch twoCell w 0 ps = watch twoCell w' 0 ps :=
  ⟨fun _ m h => nothing_hides_from_the_plenum m h, reel_unheld⟩

theorem zaphod (W : Stage) (Inner : Stage) (z : Inner.State) :
    (∀ (here : Beholder W.State) (m : W.State → W.State), ¬ Elsewhen here m here)
      ∧ ∀ (m : W.State → W.State) (ps : List Inner.Probe) (w : W.State),
          transcriptWith (builtFor (W := W) Inner z).front m w ps
            = ps.map (page (builtFor (W := W) Inner z).front w) :=
  ⟨fun here m => no_seat_is_its_own_elsewhen here m,
   fun m ps w => in_the_built_universe_nothing_ever_happens Inner z m ps w⟩

theorem both_poles_in_one_bite {State : Type} (a : Beholder State)
    (s : State) (p : a.Probe) :
    ((a.pair (plenum State).behold).obs s (p, ())).1 = a.obs s p
      ∧ ((a.pair (plenum State).behold).obs s (p, ())).2 = s :=
  ⟨pair_sees_left a (plenum State).behold s p (),
   pair_sees_right a (plenum State).behold s p ()⟩

theorem gaining_perspective {State : Type} (a : Beholder State) :
    (∀ m : State → State, ¬ Elsewhen a m a)
      ∧ (∀ (s : State) (p : a.Probe),
          ((a.pair (plenum State).behold).obs s (p, ())).1 = a.obs s p
            ∧ ((a.pair (plenum State).behold).obs s (p, ())).2 = s)
      ∧ ∀ (G : Type) [Mul G] [One G] (S : Seat G) (p q : S.Pos),
          S.act (S.sub p q) q = p :=
  ⟨fun m => no_seat_is_its_own_elsewhen a m,
   fun s p => both_poles_in_one_bite a s p,
   fun _ _ _ S p q => exit_is_one_move S p q⟩

/-- info: 'Foam.Bridges.no_seat_is_its_own_elsewhen' does not depend on any axioms -/
#guard_msgs in #print axioms no_seat_is_its_own_elsewhen

/-- info: 'Foam.Bridges.every_operator_fixes_the_built_wall' does not depend on any axioms -/
#guard_msgs in #print axioms every_operator_fixes_the_built_wall

/-- info: 'Foam.Bridges.in_the_built_universe_nothing_ever_happens' does not depend on any axioms -/
#guard_msgs in #print axioms in_the_built_universe_nothing_ever_happens

/-- info: 'Foam.Bridges.total_perspective_vortex' does not depend on any axioms -/
#guard_msgs in #print axioms total_perspective_vortex

/-- info: 'Foam.Bridges.zaphod' does not depend on any axioms -/
#guard_msgs in #print axioms zaphod

/-- info: 'Foam.Bridges.both_poles_in_one_bite' does not depend on any axioms -/
#guard_msgs in #print axioms both_poles_in_one_bite

/-- info: 'Foam.Bridges.gaining_perspective' does not depend on any axioms -/
#guard_msgs in #print axioms gaining_perspective

end Foam.Bridges
