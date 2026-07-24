import Foam.Amplitude
import Foam.Ledger

namespace Foam

def lapAround (z : GInt) : List GInt := [z.rot, z.rot.rot, z.rot.rot.rot]

def lapAgainst (z : GInt) : List GInt := [z.rot.rot.rot, z.rot.rot, z.rot]

theorem the_two_laps_are_reverses (z : GInt) :
    lapAgainst z = (lapAround z).reverse := rfl

theorem the_two_laps_permute (z : GInt) :
    (lapAround z).Perm (lapAgainst z) :=
  (List.Perm.cons z.rot
      (List.Perm.swap z.rot.rot.rot z.rot.rot [])).trans
    ((List.Perm.swap z.rot.rot.rot z.rot [z.rot.rot]).trans
      (List.Perm.cons z.rot.rot.rot (List.Perm.swap z.rot.rot z.rot [])))

theorem the_laps_part_at_the_witness :
    lapAround GInt.i ≠ lapAgainst GInt.i :=
  fun h => nomatch (GInt.mk.inj (List.cons.inj h).1).1

theorem the_lap_conserves_the_charge (z : GInt) :
    ∀ w, w ∈ lapAround z → w.normSq = z.normSq := by
  intro w hw
  cases hw with
  | head => exact rot_conserves_the_norm z
  | tail _ hw' =>
      cases hw' with
      | head =>
          exact (rot_conserves_the_norm z.rot).trans
            (rot_conserves_the_norm z)
      | tail _ hw'' =>
          cases hw'' with
          | head =>
              exact ((rot_conserves_the_norm z.rot.rot).trans
                (rot_conserves_the_norm z.rot)).trans
                (rot_conserves_the_norm z)
          | tail _ hw''' => exact nomatch hw'''

theorem the_lap_direction_is_the_remainder (z : GInt) :
    lapAgainst z = (lapAround z).reverse
      ∧ (lapAround z).Perm (lapAgainst z)
      ∧ lapAround GInt.i ≠ lapAgainst GInt.i
      ∧ z.rot.rot.rot.rot = z :=
  ⟨rfl, the_two_laps_permute z, the_laps_part_at_the_witness,
   the_wheel_comes_home z⟩

/-- info: 'Foam.the_two_laps_are_reverses' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_laps_are_reverses

/-- info: 'Foam.the_two_laps_permute' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_laps_permute

/-- info: 'Foam.the_laps_part_at_the_witness' does not depend on any axioms -/
#guard_msgs in #print axioms the_laps_part_at_the_witness

/-- info: 'Foam.the_lap_conserves_the_charge' does not depend on any axioms -/
#guard_msgs in #print axioms the_lap_conserves_the_charge

/-- info: 'Foam.the_lap_direction_is_the_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms the_lap_direction_is_the_remainder

end Foam
