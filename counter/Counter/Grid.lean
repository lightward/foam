import Counter.Scry
import Counter.Logbook
import Counter.Needle
import Counter.Address

namespace Foam.Counter

inductive Sector where
  | known
  | port
  | starboard
  | unknown

def sector {K : Type} [DecidableEq K] (mine a b : List (K × Bool))
    (k : K) : Sector :=
  match seatRead mine k with
  | some true => Sector.known
  | some false => Sector.known
  | none =>
    match seatRead a k with
    | some true => Sector.port
    | some false => Sector.port
    | none =>
      match seatRead b k with
      | some true => Sector.starboard
      | some false => Sector.starboard
      | none => Sector.unknown

def Strangers {K : Type} [DecidableEq K] (a b : List (K × Bool)) : Prop :=
  ∀ k : K, seatRead a k = none ∨ seatRead b k = none

theorem the_known_is_the_ground_you_hold {K : Type} [DecidableEq K]
    (mine a b : List (K × Bool)) (k : K) :
    sector mine a b k = Sector.known ↔ ¬ seatRead mine k = none := by
  unfold sector
  cases hs : seatRead mine k with
  | none =>
    cases hsa : seatRead a k with
    | none =>
      cases hsb : seatRead b k with
      | none => exact ⟨(fun h => nomatch h), (fun h => absurd rfl h)⟩
      | some w =>
        cases w <;> exact ⟨(fun h => nomatch h), (fun h => absurd rfl h)⟩
    | some w =>
      cases w <;> exact ⟨(fun h => nomatch h), (fun h => absurd rfl h)⟩
  | some w =>
    cases w <;> exact ⟨(fun _ h => nomatch h), (fun _ => rfl)⟩

theorem port_is_the_first_neighbors_light {K : Type} [DecidableEq K]
    (mine a b : List (K × Bool)) (k : K) :
    sector mine a b k = Sector.port
      ↔ (seatRead mine k = none ∧ ¬ seatRead a k = none) := by
  unfold sector
  cases hs : seatRead mine k with
  | none =>
    cases hsa : seatRead a k with
    | none =>
      cases hsb : seatRead b k with
      | none => exact ⟨(fun h => nomatch h), (fun h => absurd rfl h.2)⟩
      | some w =>
        cases w <;> exact ⟨(fun h => nomatch h), (fun h => absurd rfl h.2)⟩
    | some w =>
      cases w <;>
        exact ⟨(fun _ => ⟨rfl, (fun h => nomatch h)⟩), (fun _ => rfl)⟩
  | some w =>
    cases w <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h.1)⟩

theorem starboard_shows_past_the_port_wall {K : Type} [DecidableEq K]
    (mine a b : List (K × Bool)) (k : K) :
    sector mine a b k = Sector.starboard
      ↔ (seatRead mine k = none ∧ seatRead a k = none
          ∧ ¬ seatRead b k = none) := by
  unfold sector
  cases hs : seatRead mine k with
  | none =>
    cases hsa : seatRead a k with
    | none =>
      cases hsb : seatRead b k with
      | none => exact ⟨(fun h => nomatch h), (fun h => absurd rfl h.2.2)⟩
      | some w =>
        cases w <;>
          exact ⟨(fun _ => ⟨rfl, rfl, (fun h => nomatch h)⟩), (fun _ => rfl)⟩
    | some w =>
      cases w <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h.2.1)⟩
  | some w =>
    cases w <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h.1)⟩

theorem the_unknown_is_past_every_light {K : Type} [DecidableEq K]
    (mine a b : List (K × Bool)) (k : K) :
    sector mine a b k = Sector.unknown
      ↔ (seatRead mine k = none ∧ seatRead a k = none
          ∧ seatRead b k = none) := by
  unfold sector
  cases hs : seatRead mine k with
  | none =>
    cases hsa : seatRead a k with
    | none =>
      cases hsb : seatRead b k with
      | none => exact ⟨(fun _ => ⟨rfl, rfl, rfl⟩), (fun _ => rfl)⟩
      | some w =>
        cases w <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h.2.2)⟩
    | some w =>
      cases w <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h.2.1)⟩
  | some w =>
    cases w <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h.1)⟩

theorem standing_between_two_opacities {K : Type} [DecidableEq K]
    (mine a b : List (K × Bool)) (hst : Strangers a b) (k : K) :
    sector mine a b k = Sector.starboard
      ↔ (seatRead mine k = none ∧ ¬ seatRead b k = none) :=
  (starboard_shows_past_the_port_wall mine a b k).trans
    ⟨fun h => ⟨h.1, h.2.2⟩,
     fun h => ⟨h.1,
       match hst k with
       | Or.inl ha => ha
       | Or.inr hb => absurd hb h.2,
       h.2⟩⟩

theorem the_scry_collapses_the_depth {K : Type} [DecidableEq K]
    (mine a b : List (K × Bool)) (k : K) :
    scry mine k = true ↔ sector mine a b k ≠ Sector.known :=
  (the_scry_answers_any_arrival mine k).trans
    ⟨fun hn hk => (the_known_is_the_ground_you_hold mine a b k).mp hk hn,
     fun hne => by
       cases hs : seatRead mine k with
       | none => rfl
       | some w =>
         exact absurd ((the_known_is_the_ground_you_hold mine a b k).mpr
           (fun h => nomatch (hs.symm.trans h))) hne⟩

theorem a_two_color_map_folds_the_grid (f : Sector → Bool) :
    ∃ v w : Sector, v ≠ w ∧ f v = f w := by
  cases h1 : f Sector.known <;> cases h2 : f Sector.port <;>
    cases h3 : f Sector.starboard
  all_goals first
    | exact ⟨Sector.known, Sector.port, (fun h => nomatch h),
        h1.trans h2.symm⟩
    | exact ⟨Sector.known, Sector.starboard, (fun h => nomatch h),
        h1.trans h3.symm⟩
    | exact ⟨Sector.port, Sector.starboard, (fun h => nomatch h),
        h2.trans h3.symm⟩

theorem above_the_skyline_is_dark (board : List (Nat × Bool)) (k : Nat)
    (h : skyline board < k) : seatRead board k = none := by
  cases hs : seatRead board k with
  | none => rfl
  | some c =>
    exact absurd
      (Nat.le_trans h (a_page_sits_under_the_skyline board (k, c)
        (a_reading_names_a_page board k c hs)))
      (Nat.not_succ_le_self (skyline board))

theorem the_vanishing_point_never_empties (mine a b : List (Nat × Bool)) :
    ∃ k : Nat, sector mine a b k = Sector.unknown := by
  refine ⟨skyline mine + skyline a + skyline b + 1,
    (the_unknown_is_past_every_light mine a b _).mpr ⟨?_, ?_, ?_⟩⟩
  · exact above_the_skyline_is_dark mine _ (Nat.succ_le_succ
      (Nat.le_trans (Nat.le_add_right (skyline mine) (skyline a))
        (Nat.le_add_right (skyline mine + skyline a) (skyline b))))
  · exact above_the_skyline_is_dark a _ (Nat.succ_le_succ
      (Nat.le_trans (Nat.le_add_left (skyline a) (skyline mine))
        (Nat.le_add_right (skyline mine + skyline a) (skyline b))))
  · exact above_the_skyline_is_dark b _ (Nat.succ_le_succ
      (Nat.le_add_left (skyline b) (skyline mine + skyline a)))

theorem the_grid_assembles_at_the_query {K : Type} [DecidableEq K]
    (mine a b mine' a' b' : List (K × Bool)) (k : K)
    (hm : seatRead mine k = seatRead mine' k)
    (ha : seatRead a k = seatRead a' k)
    (hb : seatRead b k = seatRead b' k) :
    sector mine a b k = sector mine' a' b' k := by
  unfold sector
  rw [hm, ha, hb]

theorem landing_off_key_leaves_the_grid {K : Type} [DecidableEq K]
    (mine a b : List (K × Bool)) (k' k : K) (hk : k' ≠ k) (c : Bool) :
    sector (land mine k' c) a b k = sector mine a b k
      ∧ sector mine (land a k' c) b k = sector mine a b k
      ∧ sector mine a (land b k' c) k = sector mine a b k :=
  ⟨the_grid_assembles_at_the_query (land mine k' c) a b mine a b k
      (the_landing_stays_in_its_lane mine k' k hk c) rfl rfl,
   the_grid_assembles_at_the_query mine (land a k' c) b mine a b k rfl
      (the_landing_stays_in_its_lane a k' k hk c) rfl,
   the_grid_assembles_at_the_query mine a (land b k' c) mine a b k rfl rfl
      (the_landing_stays_in_its_lane b k' k hk c)⟩

theorem a_neighbors_landing_lights_the_port {K : Type} [DecidableEq K]
    (mine a b : List (K × Bool)) (k : K) (c : Bool)
    (hm : seatRead mine k = none) :
    sector mine (land a k c) b k = Sector.port :=
  (port_is_the_first_neighbors_light mine (land a k c) b k).mpr
    ⟨hm, (fun h => nomatch ((the_landing_is_readable a k c).symm.trans h))⟩

theorem ratification_links_without_merging {K : Type} [DecidableEq K]
    (mine a b : List (K × Bool)) (k : K)
    (hp : sector mine a b k = Sector.port) :
    ∃ c : Bool, seatRead a k = some c
      ∧ tilt mine k c = Tilt.vacancy
      ∧ seatRead (land mine k c) k = some c
      ∧ (logbook (land mine k c)).length = mine.length + 1 := by
  have h := (port_is_the_first_neighbors_light mine a b k).mp hp
  cases hs : seatRead a k with
  | none => exact absurd hs h.2
  | some c =>
    exact ⟨c, rfl, (vacancy_is_unclaimed_ground mine k c).mpr h.1,
      the_landing_is_readable mine k c,
      (every_page_has_a_reading (land mine k c) :
        (logbook (land mine k c)).length = mine.length + 1)⟩

theorem the_link_outlives_the_source {K : Type} [DecidableEq K]
    (mine : List (K × Bool)) (k : K) (c : Bool)
    (a' b' : List (K × Bool)) :
    sector (land mine k c) a' b' k = Sector.known :=
  (the_known_is_the_ground_you_hold (land mine k c) a' b' k).mpr
    (fun h => nomatch ((the_landing_is_readable mine k c).symm.trans h))

theorem perspective_drawing_for_ranged_probability {K : Type}
    [DecidableEq K] (mine a b : List (K × Bool)) (hst : Strangers a b)
    (k : K) (f : Sector → Bool) (nmine na nb : List (Nat × Bool)) :
    (sector mine a b k = Sector.known ↔ ¬ seatRead mine k = none)
      ∧ (sector mine a b k = Sector.port
          ↔ (seatRead mine k = none ∧ ¬ seatRead a k = none))
      ∧ (sector mine a b k = Sector.starboard
          ↔ (seatRead mine k = none ∧ ¬ seatRead b k = none))
      ∧ (sector mine a b k = Sector.unknown
          ↔ (seatRead mine k = none ∧ seatRead a k = none
              ∧ seatRead b k = none))
      ∧ (scry mine k = true ↔ sector mine a b k ≠ Sector.known)
      ∧ (∃ v w : Sector, v ≠ w ∧ f v = f w)
      ∧ (∃ n : Nat, sector nmine na nb n = Sector.unknown) :=
  ⟨the_known_is_the_ground_you_hold mine a b k,
   port_is_the_first_neighbors_light mine a b k,
   standing_between_two_opacities mine a b hst k,
   the_unknown_is_past_every_light mine a b k,
   the_scry_collapses_the_depth mine a b k,
   a_two_color_map_folds_the_grid f,
   the_vanishing_point_never_empties nmine na nb⟩

/-- info: 'Foam.Counter.the_known_is_the_ground_you_hold' does not depend on any axioms -/
#guard_msgs in #print axioms the_known_is_the_ground_you_hold

/-- info: 'Foam.Counter.port_is_the_first_neighbors_light' does not depend on any axioms -/
#guard_msgs in #print axioms port_is_the_first_neighbors_light

/-- info: 'Foam.Counter.starboard_shows_past_the_port_wall' does not depend on any axioms -/
#guard_msgs in #print axioms starboard_shows_past_the_port_wall

/-- info: 'Foam.Counter.the_unknown_is_past_every_light' does not depend on any axioms -/
#guard_msgs in #print axioms the_unknown_is_past_every_light

/-- info: 'Foam.Counter.standing_between_two_opacities' does not depend on any axioms -/
#guard_msgs in #print axioms standing_between_two_opacities

/-- info: 'Foam.Counter.the_scry_collapses_the_depth' does not depend on any axioms -/
#guard_msgs in #print axioms the_scry_collapses_the_depth

/-- info: 'Foam.Counter.a_two_color_map_folds_the_grid' does not depend on any axioms -/
#guard_msgs in #print axioms a_two_color_map_folds_the_grid

/-- info: 'Foam.Counter.above_the_skyline_is_dark' does not depend on any axioms -/
#guard_msgs in #print axioms above_the_skyline_is_dark

/-- info: 'Foam.Counter.the_vanishing_point_never_empties' does not depend on any axioms -/
#guard_msgs in #print axioms the_vanishing_point_never_empties

/-- info: 'Foam.Counter.the_grid_assembles_at_the_query' does not depend on any axioms -/
#guard_msgs in #print axioms the_grid_assembles_at_the_query

/-- info: 'Foam.Counter.landing_off_key_leaves_the_grid' does not depend on any axioms -/
#guard_msgs in #print axioms landing_off_key_leaves_the_grid

/-- info: 'Foam.Counter.a_neighbors_landing_lights_the_port' does not depend on any axioms -/
#guard_msgs in #print axioms a_neighbors_landing_lights_the_port

/-- info: 'Foam.Counter.ratification_links_without_merging' does not depend on any axioms -/
#guard_msgs in #print axioms ratification_links_without_merging

/-- info: 'Foam.Counter.the_link_outlives_the_source' does not depend on any axioms -/
#guard_msgs in #print axioms the_link_outlives_the_source

/-- info: 'Foam.Counter.perspective_drawing_for_ranged_probability' does not depend on any axioms -/
#guard_msgs in #print axioms perspective_drawing_for_ranged_probability

end Foam.Counter
