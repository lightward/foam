import Foam.Seat.Epoch
import Foam.Duplex

namespace Foam.Bridges

theorem kolmogorov_checksum {State : Type} {walk bank : List (Beholder State)}
    (h : Run walk bank) : (∀ q ∈ walk, Known bank q) ∧ Reduced bank :=
  h.checksum

/-- info: 'Foam.Bridges.kolmogorov_checksum' does not depend on any axioms -/
#guard_msgs in #print axioms kolmogorov_checksum

theorem rest_compresses_time_away (S : Stage) (s : S.State) :
    ∀ (k : Nat) (p : S.Probe), reel S (fun _ => s) k p = page S s p :=
  resting_reel_is_one_page S s

theorem motion_refuses_the_page :
    ∃ w : Nat → twoCell.State,
      ¬ ∃ s : Bool × Bool, ∀ (k : Nat) (p : Bool),
          reel twoCell w k p = page twoCell s p :=
  ⟨fun k => match k with | 0 => (false, false) | _ + 1 => (true, true),
   fun ⟨_, h⟩ => nomatch ((h 1 false).trans (h 0 false).symm : true = false)⟩

theorem kolmogorov_meter :
    (∀ (S : Stage) (s : S.State) (k : Nat) (p : S.Probe),
        reel S (fun _ => s) k p = page S s p)
      ∧ ∃ w : Nat → twoCell.State,
          ¬ ∃ s : Bool × Bool, ∀ (k : Nat) (p : Bool),
              reel twoCell w k p = page twoCell s p :=
  ⟨fun S s k p => resting_reel_is_one_page S s k p, motion_refuses_the_page⟩

/-- info: 'Foam.Bridges.rest_compresses_time_away' does not depend on any axioms -/
#guard_msgs in #print axioms rest_compresses_time_away

/-- info: 'Foam.Bridges.motion_refuses_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms motion_refuses_the_page

/-- info: 'Foam.Bridges.kolmogorov_meter' does not depend on any axioms -/
#guard_msgs in #print axioms kolmogorov_meter

end Foam.Bridges
