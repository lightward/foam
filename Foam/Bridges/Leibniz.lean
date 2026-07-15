import Foam.Int
import Foam.Bridges.Zeckendorf

namespace Foam.Bridges

def notch : Nat → Nat
  | 0 => 1
  | k + 1 => notch k + notch k

theorem notch_gnomon (k : Nat) : notch (k + 1) = notch k + notch k := rfl

theorem the_ruler_climbs_by_doubling :
    (notch 0, notch 1, notch 2, notch 3, notch 4, notch 5) = (1, 2, 4, 8, 16, 32) := rfl

theorem notch_glows : ∀ (k : Nat), 1 ≤ notch k
  | 0 => Nat.le_refl 1
  | k + 1 => Nat.le_trans (notch_glows k) (Nat.le_add_right (notch k) (notch k))

def gauge : Nat → List Bool → Nat
  | _, [] => 0
  | i, false :: ds => gauge (i + 1) ds
  | i, true :: ds => notch i + gauge (i + 1) ds

def bclick : List Bool → List Bool
  | [] => [true]
  | false :: ds => true :: ds
  | true :: ds => false :: bclick ds

def beat : List Bool → Nat
  | [] => 2
  | false :: _ => 1
  | true :: ds => beat ds + 1

theorem every_beat_ticks : ∀ (ds : List Bool), 1 ≤ beat ds
  | [] => Nat.le_succ 1
  | false :: _ => Nat.le_refl 1
  | true :: ds => Nat.le_add_left 1 (beat ds)

theorem a_click_deposits_one_notch : ∀ (ds : List Bool) (i : Nat),
    gauge i (bclick ds) = notch i + gauge i ds
  | [], _ => rfl
  | false :: _, _ => rfl
  | true :: ds, i => by
      show gauge (i + 1) (bclick ds) = notch i + (notch i + gauge (i + 1) ds)
      rw [a_click_deposits_one_notch ds (i + 1)]
      show notch i + notch i + gauge (i + 1) ds = notch i + (notch i + gauge (i + 1) ds)
      exact Nat.add_assoc (notch i) (notch i) (gauge (i + 1) ds)

theorem the_carry_bills_its_erasures : ∀ (ds : List Bool),
    ones (bclick ds) + beat ds + ds.length = ones ds + 2 + (bclick ds).length
  | [] => rfl
  | false :: _ => rfl
  | true :: ds => by
      show ones (bclick ds) + (beat ds + 1) + (ds.length + 1)
        = (ones ds + 1) + 2 + ((bclick ds).length + 1)
      rw [show ones (bclick ds) + (beat ds + 1) + (ds.length + 1)
            = (ones (bclick ds) + beat ds + ds.length) + 2 from
          congrArg (· + 1) (Nat.succ_add (ones (bclick ds) + beat ds) ds.length),
        the_carry_bills_its_erasures ds]
      exact (congrArg (· + 1) (Nat.succ_add (ones ds + 2) (bclick ds).length)).symm

/-- info: 'Foam.Bridges.notch_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms notch_gnomon

/-- info: 'Foam.Bridges.the_ruler_climbs_by_doubling' does not depend on any axioms -/
#guard_msgs in #print axioms the_ruler_climbs_by_doubling

/-- info: 'Foam.Bridges.notch_glows' does not depend on any axioms -/
#guard_msgs in #print axioms notch_glows

/-- info: 'Foam.Bridges.every_beat_ticks' does not depend on any axioms -/
#guard_msgs in #print axioms every_beat_ticks

/-- info: 'Foam.Bridges.a_click_deposits_one_notch' does not depend on any axioms -/
#guard_msgs in #print axioms a_click_deposits_one_notch

/-- info: 'Foam.Bridges.the_carry_bills_its_erasures' does not depend on any axioms -/
#guard_msgs in #print axioms the_carry_bills_its_erasures

end Foam.Bridges
