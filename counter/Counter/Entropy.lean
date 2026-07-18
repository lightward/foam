import Counter.Grid
import Counter.Scry
import Counter.Logbook
import Counter.Wake
import Counter.Needle
import Counter.Address

namespace Foam.Counter

theorem two_dark_landings_wear_one_wake {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k0 k1 : K) (b : Bool)
    (h0 : seatRead prior k0 = none) (h1 : seatRead prior k1 = none)
    (hk : k0 ≠ k1) :
    logbook (land prior k0 b) = logbook (land prior k1 b)
      ∧ wakes (land prior k0 b) = wakes (land prior k1 b)
      ∧ seatRead (land prior k0 b) k0 = some b
      ∧ seatRead (land prior k1 b) k0 = none := by
  refine ⟨?_, ?_, the_landing_is_readable prior k0 b,
    (the_landing_stays_in_its_lane prior k1 k0 (fun h => hk h.symm) b).trans
      h0⟩
  · show tilt prior k0 b :: logbook prior = tilt prior k1 b :: logbook prior
    rw [(vacancy_is_unclaimed_ground prior k0 b).mpr h0,
      (vacancy_is_unclaimed_ground prior k1 b).mpr h1]
  · show wake prior k0 b :: wakes prior = wake prior k1 b :: wakes prior
    rw [vacancy_breaks_new_water prior k0 b
        ((vacancy_is_unclaimed_ground prior k0 b).mpr h0),
      vacancy_breaks_new_water prior k1 b
        ((vacancy_is_unclaimed_ground prior k1 b).mpr h1)]

theorem a_copied_seed_twins_the_edge (board1 board2 : List (Nat × Bool))
    (hcopy : board1 = board2) (b : Bool) :
    skyline board1 + 1 = skyline board2 + 1
      ∧ land board1 (skyline board1 + 1) b
          = land board2 (skyline board2 + 1) b := by
  subst hcopy
  exact ⟨rfl, rfl⟩

theorem the_dark_is_not_a_point (board : List (Nat × Bool)) :
    ∃ k0 k1 : Nat, k0 ≠ k1
      ∧ seatRead board k0 = none ∧ seatRead board k1 = none :=
  ⟨skyline board + 1, skyline board + 2,
   (fun h => Nat.succ_ne_self (skyline board + 1) h.symm),
   above_the_skyline_is_dark board _ (Nat.lt_succ_self (skyline board)),
   above_the_skyline_is_dark board _
     (Nat.lt_succ_of_lt (Nat.lt_succ_self (skyline board)))⟩

theorem entropy_tells_the_pair_apart {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k0 k1 : K) (b : Bool)
    (h0 : seatRead prior k0 = none) (hk : k0 ≠ k1) :
    ¬ land prior k0 b = land prior k1 b :=
  fun he => nomatch ((the_landing_is_readable prior k0 b).symm.trans
    ((congrArg (fun x => seatRead x k0) he).trans
      ((the_landing_stays_in_its_lane prior k1 k0
        (fun h => hk h.symm) b).trans h0)))

theorem physical_entropy_versus_a_prng {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k0 k1 : K) (b : Bool)
    (h0 : seatRead prior k0 = none) (h1 : seatRead prior k1 = none)
    (hk : k0 ≠ k1) (board1 board2 : List (Nat × Bool))
    (hcopy : board1 = board2) :
    land board1 (skyline board1 + 1) b
        = land board2 (skyline board2 + 1) b
      ∧ (∃ n0 n1 : Nat, n0 ≠ n1
          ∧ seatRead board1 n0 = none ∧ seatRead board1 n1 = none)
      ∧ logbook (land prior k0 b) = logbook (land prior k1 b)
      ∧ ¬ land prior k0 b = land prior k1 b :=
  ⟨(a_copied_seed_twins_the_edge board1 board2 hcopy b).2,
   the_dark_is_not_a_point board1,
   (two_dark_landings_wear_one_wake prior k0 k1 b h0 h1 hk).1,
   entropy_tells_the_pair_apart prior k0 k1 b h0 hk⟩

/-- info: 'Foam.Counter.two_dark_landings_wear_one_wake' does not depend on any axioms -/
#guard_msgs in #print axioms two_dark_landings_wear_one_wake

/-- info: 'Foam.Counter.a_copied_seed_twins_the_edge' does not depend on any axioms -/
#guard_msgs in #print axioms a_copied_seed_twins_the_edge

/-- info: 'Foam.Counter.the_dark_is_not_a_point' does not depend on any axioms -/
#guard_msgs in #print axioms the_dark_is_not_a_point

/-- info: 'Foam.Counter.entropy_tells_the_pair_apart' does not depend on any axioms -/
#guard_msgs in #print axioms entropy_tells_the_pair_apart

/-- info: 'Foam.Counter.physical_entropy_versus_a_prng' does not depend on any axioms -/
#guard_msgs in #print axioms physical_entropy_versus_a_prng

end Foam.Counter
