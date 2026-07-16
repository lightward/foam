import Counter.Wake
import Counter.Needle
import Counter.Address

namespace Foam.Counter

def logbook {K : Type} [DecidableEq K] : List (K × Bool) → List Tilt
  | [] => []
  | (k, b) :: rest => tilt rest k b :: logbook rest

def wakes {K : Type} [DecidableEq K] : List (K × Bool) → List (Bool × Bool)
  | [] => []
  | (k, b) :: rest => wake rest k b :: wakes rest

def Holding {K : Type} [DecidableEq K] : List (K × Bool) → Prop
  | [] => True
  | (k, b) :: rest => tilt rest k b ≠ Tilt.friction ∧ Holding rest

theorem the_log_replays_the_voyage {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    logbook (land prior k b) = tilt prior k b :: logbook prior :=
  rfl

theorem every_page_has_a_reading {K : Type} [DecidableEq K] :
    ∀ board : List (K × Bool), (logbook board).length = board.length
  | [] => rfl
  | (_, _) :: rest => congrArg (· + 1) (every_page_has_a_reading rest)

theorem the_water_writes_the_log {K : Type} [DecidableEq K] :
    ∀ board : List (K × Bool), (wakes board).map sounding = logbook board
  | [] => rfl
  | (n, c) :: rest => by
      show sounding (wake rest n c) :: (wakes rest).map sounding
        = tilt rest n c :: logbook rest
      rw [the_wake_names_the_tilt rest n c, the_water_writes_the_log rest]

theorem no_stance_is_its_own_mirror : ∀ x : Bool, x ≠ !x
  | true, h => nomatch h
  | false, h => nomatch h

theorem an_unmirrored_stance_matches : ∀ x y : Bool, x ≠ !y → x = y
  | true, true, _ => rfl
  | false, false, _ => rfl
  | true, false, h => absurd rfl h
  | false, true, h => absurd rfl h

theorem a_reading_names_a_page {K : Type} [DecidableEq K] :
    ∀ (board : List (K × Bool)) (k : K) (b : Bool),
      seatRead board k = some b → (k, b) ∈ board
  | [], _, _, h => nomatch h
  | (n, c) :: rest, k, b, h => by
      have h' : (if n = k then some c else seatRead rest k) = some b := h
      by_cases hn : n = k
      · rw [if_pos hn] at h'
        rw [← hn, ← Option.some.inj h']
        exact List.Mem.head rest
      · rw [if_neg hn] at h'
        exact List.Mem.tail (n, c) (a_reading_names_a_page rest k b h')

theorem a_page_keeps_the_key_claimed {K : Type} [DecidableEq K] :
    ∀ (board : List (K × Bool)) (p : K × Bool), p ∈ board →
      ∃ q : Bool, seatRead board p.1 = some q
  | [], _, hp => nomatch hp
  | (n, c) :: rest, p, hp => by
      cases hp with
      | head => exact ⟨c, the_landing_is_readable rest n c⟩
      | tail _ hp' =>
        by_cases hn : n = p.1
        · refine ⟨c, ?_⟩
          show (if n = p.1 then some c else seatRead rest p.1) = some c
          rw [if_pos hn]
        · cases a_page_keeps_the_key_claimed rest p hp' with
          | intro q hq =>
            exact ⟨q, (the_landing_stays_in_its_lane rest n p.1 hn c).trans hq⟩

theorem one_more_data_point {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    Holding (land prior k b)
      ↔ (tilt prior k b ≠ Tilt.friction ∧ Holding prior) :=
  Iff.rfl

theorem the_turned_page_breaks_the_series {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool)
    (h : tilt prior k b = Tilt.friction) : ¬ Holding (land prior k b) :=
  fun hh => hh.1 h

theorem the_record_shows_the_break {K : Type} [DecidableEq K] :
    ∀ board : List (K × Bool),
      Holding board ↔ ∀ t ∈ logbook board, t ≠ Tilt.friction
  | [] => ⟨(fun _ t ht => nomatch ht), (fun _ => True.intro)⟩
  | (n, c) :: rest => by
      constructor
      · intro hh t ht
        have ht' : t ∈ tilt rest n c :: logbook rest := ht
        cases ht' with
        | head => exact hh.1
        | tail _ htr => exact ((the_record_shows_the_break rest).mp hh.2) t htr
      · intro hall
        exact ⟨hall (tilt rest n c) (List.Mem.head _),
          (the_record_shows_the_break rest).mpr
            (fun t ht => hall t (List.Mem.tail _ ht))⟩

theorem a_holding_log_speaks_with_one_voice {K : Type} [DecidableEq K] :
    ∀ board : List (K × Bool), Holding board →
      ∀ p : K × Bool, p ∈ board → seatRead board p.1 = some p.2
  | [], _, _, hp => nomatch hp
  | (n, c) :: rest, hh, p, hp => by
      cases hp with
      | head => exact the_landing_is_readable rest n c
      | tail _ hp' =>
        have hprev := a_holding_log_speaks_with_one_voice rest hh.2 p hp'
        by_cases hn : n = p.1
        · have hns : seatRead rest n = some p.2 := by rw [hn]; exact hprev
          have hpc : p.2 = c :=
            an_unmirrored_stance_matches p.2 c
              (fun he => hh.1 ((friction_is_a_held_mirror rest n c).mpr
                (hns.trans (congrArg some he))))
          show (if n = p.1 then some c else seatRead rest p.1) = some p.2
          rw [if_pos hn, hpc]
        · exact (the_landing_stays_in_its_lane rest n p.1 hn c).trans hprev

theorem one_voice_holds_the_log {K : Type} [DecidableEq K] :
    ∀ board : List (K × Bool),
      (∀ p : K × Bool, p ∈ board → seatRead board p.1 = some p.2) →
      Holding board
  | [], _ => True.intro
  | (n, c) :: rest, hall => by
      refine ⟨fun hf => ?_, one_voice_holds_the_log rest (fun p hp => ?_)⟩
      · exact no_stance_is_its_own_mirror c
          (Option.some.inj ((the_landing_is_readable rest n c).symm.trans
            (hall (n, !c) (List.Mem.tail _
              (a_reading_names_a_page rest n (!c)
                ((friction_is_a_held_mirror rest n c).mp hf))))))
      · cases a_page_keeps_the_key_claimed rest p hp with
        | intro q hq =>
          have hq' : seatRead ((n, c) :: rest) p.1 = some q :=
            hall (p.1, q) (List.Mem.tail _ (a_reading_names_a_page rest p.1 q hq))
          have hp2 : seatRead ((n, c) :: rest) p.1 = some p.2 :=
            hall p (List.Mem.tail _ hp)
          exact (Option.some.inj (hq'.symm.trans hp2)) ▸ hq

theorem the_series_is_holding_so_far {K : Type} [DecidableEq K]
    (board prior : List (K × Bool)) (k : K) (b : Bool) :
    logbook (land prior k b) = tilt prior k b :: logbook prior
      ∧ (logbook board).length = board.length
      ∧ (wakes board).map sounding = logbook board
      ∧ (Holding (land prior k b)
          ↔ (tilt prior k b ≠ Tilt.friction ∧ Holding prior))
      ∧ (Holding board ↔ ∀ t ∈ logbook board, t ≠ Tilt.friction)
      ∧ (Holding board
          ↔ ∀ p : K × Bool, p ∈ board → seatRead board p.1 = some p.2) :=
  ⟨rfl,
   every_page_has_a_reading board,
   the_water_writes_the_log board,
   one_more_data_point prior k b,
   the_record_shows_the_break board,
   ⟨a_holding_log_speaks_with_one_voice board,
    one_voice_holds_the_log board⟩⟩

/-- info: 'Foam.Counter.the_log_replays_the_voyage' does not depend on any axioms -/
#guard_msgs in #print axioms the_log_replays_the_voyage

/-- info: 'Foam.Counter.every_page_has_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms every_page_has_a_reading

/-- info: 'Foam.Counter.the_water_writes_the_log' does not depend on any axioms -/
#guard_msgs in #print axioms the_water_writes_the_log

/-- info: 'Foam.Counter.no_stance_is_its_own_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms no_stance_is_its_own_mirror

/-- info: 'Foam.Counter.an_unmirrored_stance_matches' does not depend on any axioms -/
#guard_msgs in #print axioms an_unmirrored_stance_matches

/-- info: 'Foam.Counter.a_reading_names_a_page' does not depend on any axioms -/
#guard_msgs in #print axioms a_reading_names_a_page

/-- info: 'Foam.Counter.a_page_keeps_the_key_claimed' does not depend on any axioms -/
#guard_msgs in #print axioms a_page_keeps_the_key_claimed

/-- info: 'Foam.Counter.one_more_data_point' does not depend on any axioms -/
#guard_msgs in #print axioms one_more_data_point

/-- info: 'Foam.Counter.the_turned_page_breaks_the_series' does not depend on any axioms -/
#guard_msgs in #print axioms the_turned_page_breaks_the_series

/-- info: 'Foam.Counter.the_record_shows_the_break' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_shows_the_break

/-- info: 'Foam.Counter.a_holding_log_speaks_with_one_voice' does not depend on any axioms -/
#guard_msgs in #print axioms a_holding_log_speaks_with_one_voice

/-- info: 'Foam.Counter.one_voice_holds_the_log' does not depend on any axioms -/
#guard_msgs in #print axioms one_voice_holds_the_log

/-- info: 'Foam.Counter.the_series_is_holding_so_far' does not depend on any axioms -/
#guard_msgs in #print axioms the_series_is_holding_so_far

end Foam.Counter
