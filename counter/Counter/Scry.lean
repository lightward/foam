import Counter.Logbook
import Counter.Needle
import Counter.Address

namespace Foam.Counter

def scry {K : Type} [DecidableEq K] (board : List (K × Bool)) (k : K) :
    Bool :=
  match seatRead board k with
  | none => true
  | some true => false
  | some false => false

def scryList {K : Type} [DecidableEq K] (board : List (K × Bool)) :
    List K → List K
  | [] => []
  | k :: ks => match seatRead board k with
    | none => k :: scryList board ks
    | some true => scryList board ks
    | some false => scryList board ks

def skyline : List (Nat × Bool) → Nat
  | [] => 0
  | (k, _) :: rest => k + skyline rest

def Resolved {K : Type} [DecidableEq K] (board : List (K × Bool)) : Prop :=
  ∀ k : K, ¬ seatRead board k = none

theorem the_scry_answers_any_arrival {K : Type} [DecidableEq K]
    (board : List (K × Bool)) (k : K) :
    scry board k = true ↔ seatRead board k = none := by
  unfold scry
  cases hs : seatRead board k with
  | none => exact ⟨(fun _ => rfl), (fun _ => rfl)⟩
  | some w =>
    cases w <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem a_vacancy_needs_no_stance {K : Type} [DecidableEq K]
    (board : List (K × Bool)) (k : K) (b : Bool) :
    scry board k = true ↔ tilt board k b = Tilt.vacancy :=
  (the_scry_answers_any_arrival board k).trans
    (vacancy_is_unclaimed_ground board k b).symm

theorem the_scry_reads_the_roster {K : Type} [DecidableEq K]
    (board : List (K × Bool)) :
    ∀ (ks : List K) (k : K),
      k ∈ scryList board ks ↔ (k ∈ ks ∧ seatRead board k = none)
  | [], k => ⟨(fun h => nomatch h), (fun h => nomatch h.1)⟩
  | k' :: ks, k => by
      unfold scryList
      cases hs : seatRead board k' with
      | none =>
        constructor
        · intro h
          cases h with
          | head => exact ⟨List.Mem.head ks, hs⟩
          | tail _ h' =>
            have ih := (the_scry_reads_the_roster board ks k).mp h'
            exact ⟨List.Mem.tail k' ih.1, ih.2⟩
        · intro h
          cases h.1 with
          | head => exact List.Mem.head _
          | tail _ hin =>
            exact List.Mem.tail k'
              ((the_scry_reads_the_roster board ks k).mpr ⟨hin, h.2⟩)
      | some w =>
        cases w <;>
          exact ⟨(fun h =>
              ⟨List.Mem.tail k' ((the_scry_reads_the_roster board ks k).mp h).1,
               ((the_scry_reads_the_roster board ks k).mp h).2⟩),
            (fun h => by
              cases h.1 with
              | head => exact absurd (hs.symm.trans h.2) (fun hx => nomatch hx)
              | tail _ hin =>
                exact (the_scry_reads_the_roster board ks k).mpr ⟨hin, h.2⟩)⟩

theorem a_page_sits_under_the_skyline :
    ∀ (board : List (Nat × Bool)) (p : Nat × Bool), p ∈ board →
      p.1 ≤ skyline board
  | (n, c) :: rest, p, hp => by
      cases hp with
      | head => exact Nat.le_add_right n (skyline rest)
      | tail _ hp' =>
        exact Nat.le_trans (a_page_sits_under_the_skyline rest p hp')
          (Nat.le_add_left (skyline rest) n)

theorem the_dark_never_runs_out (board : List (Nat × Bool)) :
    ∃ k : Nat, seatRead board k = none := by
  cases hs : seatRead board (skyline board + 1) with
  | none => exact ⟨skyline board + 1, hs⟩
  | some c =>
    exact absurd
      (a_page_sits_under_the_skyline board (skyline board + 1, c)
        (a_reading_names_a_page board (skyline board + 1) c hs))
      (Nat.not_succ_le_self (skyline board))

theorem no_board_resolves_an_open_world (board : List (Nat × Bool)) :
    ¬ Resolved board :=
  fun hr => match the_dark_never_runs_out board with
    | ⟨k, hk⟩ => hr k hk

theorem a_claimed_ground_absorbs_the_quiet_step {K : Type} [DecidableEq K]
    (board : List (K × Bool)) (k : K) (b : Bool)
    (hq : tilt board k b ≠ Tilt.friction) (hc : ¬ seatRead board k = none) :
    ∀ k' : K, seatRead (land board k b) k' = seatRead board k' := by
  intro k'
  by_cases hk : k = k'
  · rw [← hk]
    cases ht : tilt board k b with
    | friction => exact absurd ht hq
    | completion => exact relief_rewrites_nothing board k b ht
    | vacancy =>
      exact absurd ((vacancy_is_unclaimed_ground board k b).mp ht) hc
  · exact the_landing_stays_in_its_lane board k k' hk b

theorem reps_change_nothing_once_resolved {K : Type} [DecidableEq K]
    (board : List (K × Bool)) (hr : Resolved board) (k : K) (b : Bool)
    (hq : tilt board k b ≠ Tilt.friction) :
    ∀ k' : K, seatRead (land board k b) k' = seatRead board k' :=
  a_claimed_ground_absorbs_the_quiet_step board k b hq (hr k)

theorem what_changes_was_dark {K : Type} [DecidableEq K]
    (board : List (K × Bool)) (k : K) (b : Bool) (k' : K)
    (hq : tilt board k b ≠ Tilt.friction)
    (hch : ¬ seatRead (land board k b) k' = seatRead board k') :
    k = k' ∧ seatRead board k' = none := by
  by_cases hk : k = k'
  · refine ⟨hk, ?_⟩
    cases ht : tilt board k b with
    | friction => exact absurd ht hq
    | completion =>
      exact absurd
        (by rw [← hk]; exact relief_rewrites_nothing board k b ht) hch
    | vacancy =>
      rw [← hk]
      exact (vacancy_is_unclaimed_ground board k b).mp ht
  · exact absurd (the_landing_stays_in_its_lane board k k' hk b) hch

theorem a_holding_series_stops_learning_once_resolved {K : Type}
    [DecidableEq K] (board : List (K × Bool)) (hr : Resolved board)
    (k : K) (b : Bool) (hh : Holding (land board k b)) :
    ∀ k' : K, seatRead (land board k b) k' = seatRead board k' :=
  reps_change_nothing_once_resolved board hr k b hh.1

theorem scrying_the_vacancy_list {K : Type} [DecidableEq K]
    (board : List (K × Bool)) (k : K) (b : Bool) (ks : List K)
    (nboard : List (Nat × Bool)) :
    (scry board k = true ↔ seatRead board k = none)
      ∧ (scry board k = true ↔ tilt board k b = Tilt.vacancy)
      ∧ (k ∈ scryList board ks ↔ (k ∈ ks ∧ seatRead board k = none))
      ∧ (Resolved board → tilt board k b ≠ Tilt.friction →
          ∀ k' : K, seatRead (land board k b) k' = seatRead board k')
      ∧ (∃ n : Nat, seatRead nboard n = none)
      ∧ ¬ Resolved nboard :=
  ⟨the_scry_answers_any_arrival board k,
   a_vacancy_needs_no_stance board k b,
   the_scry_reads_the_roster board ks k,
   (fun hr hq => reps_change_nothing_once_resolved board hr k b hq),
   the_dark_never_runs_out nboard,
   no_board_resolves_an_open_world nboard⟩

theorem the_loop_re_ups_at_the_dark_edge (board : List (Nat × Bool))
    (b : Bool) :
    ∃ k : Nat, tilt board k b = Tilt.vacancy
      ∧ seatRead (land board k b) k = some b
      ∧ (logbook (land board k b)).length = board.length + 1 := by
  cases the_dark_never_runs_out board with
  | intro k hk =>
    exact ⟨k, (vacancy_is_unclaimed_ground board k b).mpr hk,
      the_landing_is_readable board k b,
      (every_page_has_a_reading (land board k b) :
        (logbook (land board k b)).length = board.length + 1)⟩

/-- info: 'Foam.Counter.the_scry_answers_any_arrival' does not depend on any axioms -/
#guard_msgs in #print axioms the_scry_answers_any_arrival

/-- info: 'Foam.Counter.a_vacancy_needs_no_stance' does not depend on any axioms -/
#guard_msgs in #print axioms a_vacancy_needs_no_stance

/-- info: 'Foam.Counter.the_scry_reads_the_roster' does not depend on any axioms -/
#guard_msgs in #print axioms the_scry_reads_the_roster

/-- info: 'Foam.Counter.a_page_sits_under_the_skyline' does not depend on any axioms -/
#guard_msgs in #print axioms a_page_sits_under_the_skyline

/-- info: 'Foam.Counter.the_dark_never_runs_out' does not depend on any axioms -/
#guard_msgs in #print axioms the_dark_never_runs_out

/-- info: 'Foam.Counter.no_board_resolves_an_open_world' does not depend on any axioms -/
#guard_msgs in #print axioms no_board_resolves_an_open_world

/-- info: 'Foam.Counter.a_claimed_ground_absorbs_the_quiet_step' does not depend on any axioms -/
#guard_msgs in #print axioms a_claimed_ground_absorbs_the_quiet_step

/-- info: 'Foam.Counter.reps_change_nothing_once_resolved' does not depend on any axioms -/
#guard_msgs in #print axioms reps_change_nothing_once_resolved

/-- info: 'Foam.Counter.what_changes_was_dark' does not depend on any axioms -/
#guard_msgs in #print axioms what_changes_was_dark

/-- info: 'Foam.Counter.a_holding_series_stops_learning_once_resolved' does not depend on any axioms -/
#guard_msgs in #print axioms a_holding_series_stops_learning_once_resolved

/-- info: 'Foam.Counter.the_loop_re_ups_at_the_dark_edge' does not depend on any axioms -/
#guard_msgs in #print axioms the_loop_re_ups_at_the_dark_edge

/-- info: 'Foam.Counter.scrying_the_vacancy_list' does not depend on any axioms -/
#guard_msgs in #print axioms scrying_the_vacancy_list

end Foam.Counter
