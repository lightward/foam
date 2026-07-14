import Counter.Trefoil
import Foam.Engine.Chirality
import Foam.Int

namespace Foam.Counter

def Crossing.toll : Crossing → Nat
  | .pos => 1
  | .neg => 3

def ledger : List Crossing → Nat
  | [] => 0
  | c :: D => c.toll + ledger D

def fullTurn : List Crossing := [.pos, .pos, .pos, .pos]

theorem the_click_is_the_toll (c : Crossing) (z : GInt) :
    c.click z = rotPow c.toll z := by
  cases c <;> rfl

theorem the_spin_is_absorbed_into_the_winding (D : List Crossing) (z : GInt) :
    phase D z = rotPow (ledger D) z := by
  induction D with
  | nil => rfl
  | cons c D ih =>
    show c.click (phase D z) = rotPow (c.toll + ledger D) z
    rw [ih, the_click_is_the_toll, rotPow_compose]

theorem the_ledger_adds (D E : List Crossing) :
    ledger (D ++ E) = ledger D + ledger E := by
  induction D with
  | nil => exact (Nat.zero_add (ledger E)).symm
  | cons c D ih =>
    show c.toll + ledger (D ++ E) = c.toll + ledger D + ledger E
    rw [ih, Nat.add_assoc]

theorem crossings_compose (D E : List Crossing) (z : GInt) :
    phase (D ++ E) z = phase D (phase E z) := by
  induction D with
  | nil => rfl
  | cons c D ih =>
    show c.click (phase (D ++ E) z) = c.click (phase D (phase E z))
    rw [ih]

theorem the_ledger_counts_clicks_not_identities (D E : List Crossing)
    (h : ledger D = ledger E) (z : GInt) : phase D z = phase E z := by
  rw [the_spin_is_absorbed_into_the_winding, the_spin_is_absorbed_into_the_winding, h]

theorem the_register_cannot_hear_the_order (D E : List Crossing) (z : GInt) :
    phase (D ++ E) z = phase (E ++ D) z :=
  the_ledger_counts_clicks_not_identities (D ++ E) (E ++ D)
    (by rw [the_ledger_adds, the_ledger_adds, Nat.add_comm]) z

theorem the_wheel_ignores_whole_turns (q r : Nat) (z : GInt) :
    rotPow (4 * q + r) z = rotPow r z := by
  induction q with
  | zero =>
    show rotPow (0 + r) z = rotPow r z
    rw [Nat.zero_add]
  | succ m ih =>
    show rotPow (4 * m + 4 + r) z = rotPow r z
    rw [← rotPow_compose (4 * m + 4) r z, rotPow_add_four, rotPow_compose]
    exact ih

theorem every_toll_is_turns_and_change (k : Nat) :
    ∃ q r, r < 4 ∧ k = 4 * q + r := by
  induction k with
  | zero => exact ⟨0, 0, by decide, rfl⟩
  | succ n ih =>
    obtain ⟨q, r, hr, hk⟩ := ih
    match r, hr, hk with
    | 0, _, hk => exact ⟨q, 1, by decide, congrArg Nat.succ hk⟩
    | 1, _, hk => exact ⟨q, 2, by decide, congrArg Nat.succ hk⟩
    | 2, _, hk => exact ⟨q, 3, by decide, congrArg Nat.succ hk⟩
    | 3, _, hk => exact ⟨q + 1, 0, by decide, congrArg Nat.succ hk⟩
    | r + 4, hr, _ =>
      exact absurd (Nat.lt_of_lt_of_le hr (Nat.le_add_left 4 r)) (Nat.lt_irrefl _)

theorem the_wheel_never_comes_home_early (k : Nat) :
    (∀ z : GInt, rotPow k z = z) ↔ ∃ q, k = 4 * q := by
  constructor
  · intro hall
    obtain ⟨q, r, hr, hk⟩ := every_toll_is_turns_and_change k
    have h1 := hall GInt.one
    rw [hk, the_wheel_ignores_whole_turns q r] at h1
    match r, hr, h1, hk with
    | 0, _, _, hk => exact ⟨q, hk⟩
    | 1, _, h1, _ => exact absurd h1 (by decide)
    | 2, _, h1, _ => exact absurd h1 (by decide)
    | 3, _, h1, _ => exact absurd h1 (by decide)
    | r + 4, hr, _, _ =>
      exact absurd (Nat.lt_of_lt_of_le hr (Nat.le_add_left 4 r)) (Nat.lt_irrefl _)
  · intro h z
    obtain ⟨q, hq⟩ := h
    rw [hq]
    exact the_wheel_ignores_whole_turns q 0 z

theorem the_toll_home_is_whole_turns (D : List Crossing) :
    (∀ z : GInt, phase D z = z) ↔ ∃ q, ledger D = 4 * q := by
  constructor
  · intro h
    exact (the_wheel_never_comes_home_early (ledger D)).mp
      (fun z => by rw [← the_spin_is_absorbed_into_the_winding]; exact h z)
  · intro h z
    rw [the_spin_is_absorbed_into_the_winding]
    exact (the_wheel_never_comes_home_early (ledger D)).mpr h z

theorem the_passenger_receives_the_change (D : List Crossing) :
    ∃ q r, r < 4 ∧ ledger D = 4 * q + r ∧ ∀ z : GInt, phase D z = rotPow r z := by
  obtain ⟨q, r, hr, hk⟩ := every_toll_is_turns_and_change (ledger D)
  refine ⟨q, r, hr, hk, fun z => ?_⟩
  rw [the_spin_is_absorbed_into_the_winding, hk]
  exact the_wheel_ignores_whole_turns q r z

theorem the_keeper_knows_more_than_the_wheel :
    (∀ z : GInt, phase fullTurn z = phase [] z) ∧ ledger fullTurn ≠ ledger [] :=
  ⟨fun z => rotPow_four z, by decide⟩

theorem a_click_moves_every_seat_but_the_center (z : GInt)
    (h : rotPow 1 z = z) : z = GInt.zero := by
  cases z with
  | mk a b =>
    have hre : -b = a := congrArg GInt.re h
    have him : a = b := congrArg GInt.im h
    rw [show (⟨a, b⟩ : GInt) = ⟨0, 0⟩ from by
          rw [him, neg_fixes_only_zero (hre.trans him)]]
    rfl

theorem the_kink_pays_and_shows (z : GInt) (hz : z ≠ GInt.zero) :
    ledger [.pos] = 1 ∧ phase [.pos] z ≠ z :=
  ⟨rfl, fun h => hz (a_click_moves_every_seat_but_the_center z h)⟩

theorem a_passing_pair_returns_the_spin (c : Crossing) (z : GInt) :
    phase [c, c.flip] z = z := by
  cases c <;> exact rotPow_four z

theorem a_passing_pair_pays_a_full_turn (c : Crossing) :
    ledger [c, c.flip] = 4 := by
  cases c <;> rfl

theorem the_wheel_forgives_what_the_ledger_records (c : Crossing) :
    (∀ z : GInt, phase [c, c.flip] z = z) ∧ ledger [c, c.flip] ≠ 0 :=
  ⟨a_passing_pair_returns_the_spin c,
   by rw [a_passing_pair_pays_a_full_turn]; decide⟩

theorem the_mirror_settles_the_bill (D : List Crossing) :
    ledger (reflection D) + ledger D = 4 * D.length := by
  induction D with
  | nil => rfl
  | cons c D ih =>
    cases c with
    | pos =>
      show 3 + ledger (reflection D) + (1 + ledger D) = 4 * D.length + 4
      rw [← Nat.add_assoc, Nat.add_comm 3 (ledger (reflection D))]
      show ledger (reflection D) + 4 + ledger D = 4 * D.length + 4
      rw [Nat.add_comm (ledger (reflection D)) 4, Nat.add_assoc, ih,
          Nat.add_comm 4 (4 * D.length)]
    | neg =>
      show 1 + ledger (reflection D) + (3 + ledger D) = 4 * D.length + 4
      rw [← Nat.add_assoc, Nat.add_comm 1 (ledger (reflection D))]
      show ledger (reflection D) + 4 + ledger D = 4 * D.length + 4
      rw [Nat.add_comm (ledger (reflection D)) 4, Nat.add_assoc, ih,
          Nat.add_comm 4 (4 * D.length)]

theorem the_center_rides_free (D : List Crossing) :
    phase D GInt.zero = GInt.zero := by
  induction D with
  | nil => rfl
  | cons c D ih =>
    show c.click (phase D GInt.zero) = GInt.zero
    rw [ih]
    cases c <;> rfl

theorem the_keeper_is_the_still_seat (z : GInt) :
    (∀ D : List Crossing, phase D z = z) ↔ z = GInt.zero := by
  constructor
  · intro h
    exact a_click_moves_every_seat_but_the_center z (h [.pos])
  · intro h D
    rw [h]
    exact the_center_rides_free D

/-- info: 'Foam.Counter.the_spin_is_absorbed_into_the_winding' does not depend on any axioms -/
#guard_msgs in #print axioms the_spin_is_absorbed_into_the_winding

/-- info: 'Foam.Counter.the_ledger_adds' does not depend on any axioms -/
#guard_msgs in #print axioms the_ledger_adds

/-- info: 'Foam.Counter.crossings_compose' does not depend on any axioms -/
#guard_msgs in #print axioms crossings_compose

/-- info: 'Foam.Counter.the_ledger_counts_clicks_not_identities' does not depend on any axioms -/
#guard_msgs in #print axioms the_ledger_counts_clicks_not_identities

/-- info: 'Foam.Counter.the_register_cannot_hear_the_order' does not depend on any axioms -/
#guard_msgs in #print axioms the_register_cannot_hear_the_order

/-- info: 'Foam.Counter.every_toll_is_turns_and_change' does not depend on any axioms -/
#guard_msgs in #print axioms every_toll_is_turns_and_change

/-- info: 'Foam.Counter.the_wheel_never_comes_home_early' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_never_comes_home_early

/-- info: 'Foam.Counter.the_toll_home_is_whole_turns' does not depend on any axioms -/
#guard_msgs in #print axioms the_toll_home_is_whole_turns

/-- info: 'Foam.Counter.the_passenger_receives_the_change' does not depend on any axioms -/
#guard_msgs in #print axioms the_passenger_receives_the_change

/-- info: 'Foam.Counter.the_keeper_knows_more_than_the_wheel' does not depend on any axioms -/
#guard_msgs in #print axioms the_keeper_knows_more_than_the_wheel

/-- info: 'Foam.Counter.the_kink_pays_and_shows' does not depend on any axioms -/
#guard_msgs in #print axioms the_kink_pays_and_shows

/-- info: 'Foam.Counter.the_wheel_forgives_what_the_ledger_records' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_forgives_what_the_ledger_records

/-- info: 'Foam.Counter.the_mirror_settles_the_bill' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_settles_the_bill

/-- info: 'Foam.Counter.the_center_rides_free' does not depend on any axioms -/
#guard_msgs in #print axioms the_center_rides_free

/-- info: 'Foam.Counter.the_keeper_is_the_still_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_keeper_is_the_still_seat

end Foam.Counter
