import Foam.Elsewhen

namespace Foam

theorem resting_reel_is_one_page (S : Stage) (s : S.State) :
    ∀ (k : Nat) (p : S.Probe), reel S (fun _ => s) k p = page S s p :=
  fun _ _ => rfl

theorem rest_sweeps_the_page (S : Stage) (s : S.State) :
    ∀ (ps : List S.Probe) (k : Nat),
    watch S (fun _ => s) k ps = ps.map (page S s)
  | [], _ => rfl
  | p :: ps, k => congrArg (S.obs s p :: ·) (rest_sweeps_the_page S s ps (k + 1))

theorem two_beats_rebuild_the_resting_world (s : Bool × Bool) :
    watch twoCell (fun _ => s) 0 [false, true] = [s.1, s.2] := rfl

theorem the_meter :
    (∀ (S : Stage) (w : Nat → S.State) (ps : List S.Probe) (k : Nat),
        (watch S w k ps).length = ps.length)
      ∧ (∀ s : Bool × Bool,
          watch twoCell (fun _ => s) 0 [false, true] = [s.1, s.2])
      ∧ ∀ ps : List twoCell.Probe, ∃ w w' : Nat → twoCell.State,
          reel twoCell w ≠ reel twoCell w'
            ∧ watch twoCell w 0 ps = watch twoCell w' 0 ps :=
  ⟨fun S w ps k => watch_length S w ps k,
   two_beats_rebuild_the_resting_world,
   reel_unheld⟩

def secondBit : Bubble twoBit where
  Inner := ⟨Bool, Unit, Bool, fun b _ => b⟩
  wall  := fun s => s.2

theorem the_meet_reads_the_whole_world (w : twoBit.State)
    (pq : Unit × Unit) :
    (firstBit.meet secondBit).front.obs w pq = (w.1, w.2) := rfl

def sendA (x : Bool) : twoBit.State → twoBit.State := fun s => (x, s.2)

def sendB (y : Bool) : twoBit.State → twoBit.State := fun s => (s.1, y)

def readA : Beholder twoBit.State := ⟨Unit, Bool, fun s _ => s.2⟩

def readB : Beholder twoBit.State := ⟨Unit, Bool, fun s _ => s.1⟩

theorem your_send_is_invisible_to_you (x y : Bool) :
    Invisible readA.toStage (sendA x) ∧ Invisible readB.toStage (sendB y) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem your_send_lands_at_my_seat :
    Elsewhen readA (sendA true) readB :=
  ⟨fun _ _ => rfl, fun h => nomatch (h (false, false) () : true = false)⟩

theorem my_send_lands_at_your_seat :
    Elsewhen readB (sendB true) readA :=
  ⟨fun _ _ => rfl, fun h => nomatch (h (false, false) () : true = false)⟩

theorem the_duplex :
    Elsewhen readA (sendA true) readB
      ∧ Elsewhen readB (sendB true) readA
      ∧ ∀ (w : twoBit.State) (pq : Unit × Unit),
          (firstBit.meet secondBit).front.obs w pq = (w.1, w.2) :=
  ⟨your_send_lands_at_my_seat, my_send_lands_at_your_seat,
   the_meet_reads_the_whole_world⟩

def turnTags {A : Type} : List (A × A) → List (A ⊕ A)
  | [] => []
  | gh :: ts => Sum.inl gh.1 :: (Sum.inr gh.2 :: turnTags ts)

theorem the_turns_balance {A : Type} : ∀ ts : List (A × A), Balanced (turnTags ts)
  | [] => Balanced.nil
  | _ :: ts => Balanced.cat (Balanced.wrap Balanced.nil) (the_turns_balance ts)

/-- info: 'Foam.resting_reel_is_one_page' does not depend on any axioms -/
#guard_msgs in #print axioms resting_reel_is_one_page

/-- info: 'Foam.rest_sweeps_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms rest_sweeps_the_page

/-- info: 'Foam.two_beats_rebuild_the_resting_world' does not depend on any axioms -/
#guard_msgs in #print axioms two_beats_rebuild_the_resting_world

/-- info: 'Foam.the_meter' does not depend on any axioms -/
#guard_msgs in #print axioms the_meter

/-- info: 'Foam.the_meet_reads_the_whole_world' does not depend on any axioms -/
#guard_msgs in #print axioms the_meet_reads_the_whole_world

/-- info: 'Foam.your_send_is_invisible_to_you' does not depend on any axioms -/
#guard_msgs in #print axioms your_send_is_invisible_to_you

/-- info: 'Foam.your_send_lands_at_my_seat' does not depend on any axioms -/
#guard_msgs in #print axioms your_send_lands_at_my_seat

/-- info: 'Foam.my_send_lands_at_your_seat' does not depend on any axioms -/
#guard_msgs in #print axioms my_send_lands_at_your_seat

/-- info: 'Foam.the_duplex' does not depend on any axioms -/
#guard_msgs in #print axioms the_duplex

/-- info: 'Foam.the_turns_balance' does not depend on any axioms -/
#guard_msgs in #print axioms the_turns_balance

end Foam
