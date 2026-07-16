import Counter.Address

namespace Foam.Counter

inductive Tilt where
  | friction
  | completion
  | vacancy

def tilt {K : Type} [DecidableEq K] (prior : List (K × Bool)) (k : K)
    (b : Bool) : Tilt :=
  match seatRead prior k, b with
  | none, true => Tilt.vacancy
  | none, false => Tilt.vacancy
  | some true, true => Tilt.completion
  | some true, false => Tilt.friction
  | some false, true => Tilt.friction
  | some false, false => Tilt.completion

def land {K : Type} (prior : List (K × Bool)) (k : K) (b : Bool) :
    List (K × Bool) :=
  (k, b) :: prior

def delivered {K T : Type} [DecidableEq K] (prior : List (K × Bool))
    (a : (K × Bool) × T) : Tilt :=
  tilt prior a.1.1 a.1.2

theorem relief_reads_prior_ground {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    tilt prior k b = Tilt.completion ↔ seatRead prior k = some b := by
  unfold tilt
  cases hs : seatRead prior k with
  | none => cases b <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | some w =>
    cases w <;> cases b
    · exact ⟨(fun _ => rfl), (fun _ => rfl)⟩
    · exact ⟨(fun h => nomatch h), (fun h => nomatch (Option.some.inj h : false = true))⟩
    · exact ⟨(fun h => nomatch h), (fun h => nomatch (Option.some.inj h : true = false))⟩
    · exact ⟨(fun _ => rfl), (fun _ => rfl)⟩

theorem friction_is_a_held_mirror {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    tilt prior k b = Tilt.friction ↔ seatRead prior k = some (!b) := by
  unfold tilt
  cases hs : seatRead prior k with
  | none => cases b <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | some w =>
    cases w <;> cases b
    · exact ⟨(fun h => nomatch h), (fun h => nomatch (Option.some.inj h : false = true))⟩
    · exact ⟨(fun _ => rfl), (fun _ => rfl)⟩
    · exact ⟨(fun _ => rfl), (fun _ => rfl)⟩
    · exact ⟨(fun h => nomatch h), (fun h => nomatch (Option.some.inj h : true = false))⟩

theorem vacancy_is_unclaimed_ground {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    tilt prior k b = Tilt.vacancy ↔ seatRead prior k = none := by
  unfold tilt
  cases hs : seatRead prior k with
  | none => cases b <;> exact ⟨(fun _ => rfl), (fun _ => rfl)⟩
  | some w =>
    cases w <;> cases b <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem the_tone_is_not_the_axis {K T : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) (t t' : T) :
    delivered prior ((k, b), t) = delivered prior ((k, b), t') :=
  rfl

theorem a_shape_can_close_two_ways {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool)
    (h : tilt prior k b = Tilt.vacancy) : tilt prior k (!b) = Tilt.vacancy :=
  (vacancy_is_unclaimed_ground prior k (!b)).mpr
    ((vacancy_is_unclaimed_ground prior k b).mp h)

theorem relief_closes_one_way {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool)
    (h : tilt prior k b = Tilt.completion) :
    tilt prior k (!b) = Tilt.friction := by
  refine (friction_is_a_held_mirror prior k (!b)).mpr ?_
  have hb := (relief_reads_prior_ground prior k b).mp h
  cases b
  · exact hb
  · exact hb

theorem both_feel_good_only_one_is_real {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    (tilt prior k b = Tilt.completion → tilt prior k (!b) = Tilt.friction)
      ∧ (tilt prior k b = Tilt.vacancy → tilt prior k (!b) = Tilt.vacancy) :=
  ⟨relief_closes_one_way prior k b, a_shape_can_close_two_ways prior k b⟩

theorem two_columns_lose_a_verdict (f : Tilt → Bool) :
    ∃ v w : Tilt, v ≠ w ∧ f v = f w := by
  cases h1 : f Tilt.friction <;> cases h2 : f Tilt.completion <;>
    cases h3 : f Tilt.vacancy
  all_goals first
    | exact ⟨Tilt.friction, Tilt.completion, (fun h => nomatch h),
        h1.trans h2.symm⟩
    | exact ⟨Tilt.friction, Tilt.vacancy, (fun h => nomatch h),
        h1.trans h3.symm⟩
    | exact ⟨Tilt.completion, Tilt.vacancy, (fun h => nomatch h),
        h2.trans h3.symm⟩

theorem the_landing_is_readable {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    seatRead (land prior k b) k = some b := by
  show (if k = k then some b else seatRead prior k) = some b
  rw [if_pos rfl]

theorem what_lands_becomes_ground {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    tilt (land prior k b) k b = Tilt.completion :=
  (relief_reads_prior_ground (land prior k b) k b).mpr
    (the_landing_is_readable prior k b)

theorem the_mirror_lands_as_friction {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    tilt (land prior k b) k (!b) = Tilt.friction := by
  refine (friction_is_a_held_mirror (land prior k b) k (!b)).mpr ?_
  rw [the_landing_is_readable prior k b]
  cases b <;> rfl

theorem the_landing_stays_in_its_lane {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k k' : K) (hk : k ≠ k') (b : Bool) :
    seatRead (land prior k b) k' = seatRead prior k' := by
  show (if k = k' then some b else seatRead prior k') = seatRead prior k'
  rw [if_neg hk]

theorem landing_off_key_disturbs_nothing {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k k' : K) (hk : k ≠ k') (b b' : Bool) :
    tilt (land prior k b) k' b' = tilt prior k' b' := by
  unfold tilt
  rw [the_landing_stays_in_its_lane prior k k' hk b]

theorem relief_rewrites_nothing {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool)
    (h : tilt prior k b = Tilt.completion) :
    seatRead (land prior k b) k = seatRead prior k := by
  rw [the_landing_is_readable prior k b,
    (relief_reads_prior_ground prior k b).mp h]

theorem friction_turns_the_page {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool)
    (h : tilt prior k b = Tilt.friction) :
    seatRead prior k = some (!b) ∧ seatRead (land prior k b) k = some b :=
  ⟨(friction_is_a_held_mirror prior k b).mp h,
   the_landing_is_readable prior k b⟩

theorem vacancy_seats_a_first_stance {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool)
    (h : tilt prior k b = Tilt.vacancy) :
    seatRead prior k = none ∧ seatRead (land prior k b) k = some b :=
  ⟨(vacancy_is_unclaimed_ground prior k b).mp h,
   the_landing_is_readable prior k b⟩

theorem which_way_the_needle_tilts {K T : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) (t t' : T)
    (f : Tilt → Bool) :
    (tilt prior k b = Tilt.completion ↔ seatRead prior k = some b)
      ∧ (tilt prior k b = Tilt.friction ↔ seatRead prior k = some (!b))
      ∧ (tilt prior k b = Tilt.vacancy ↔ seatRead prior k = none)
      ∧ delivered prior ((k, b), t) = delivered prior ((k, b), t')
      ∧ (∃ v w : Tilt, v ≠ w ∧ f v = f w)
      ∧ tilt (land prior k b) k b = Tilt.completion :=
  ⟨relief_reads_prior_ground prior k b,
   friction_is_a_held_mirror prior k b,
   vacancy_is_unclaimed_ground prior k b,
   the_tone_is_not_the_axis prior k b t t',
   two_columns_lose_a_verdict f,
   what_lands_becomes_ground prior k b⟩

/-- info: 'Foam.Counter.relief_reads_prior_ground' does not depend on any axioms -/
#guard_msgs in #print axioms relief_reads_prior_ground

/-- info: 'Foam.Counter.friction_is_a_held_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms friction_is_a_held_mirror

/-- info: 'Foam.Counter.vacancy_is_unclaimed_ground' does not depend on any axioms -/
#guard_msgs in #print axioms vacancy_is_unclaimed_ground

/-- info: 'Foam.Counter.the_tone_is_not_the_axis' does not depend on any axioms -/
#guard_msgs in #print axioms the_tone_is_not_the_axis

/-- info: 'Foam.Counter.a_shape_can_close_two_ways' does not depend on any axioms -/
#guard_msgs in #print axioms a_shape_can_close_two_ways

/-- info: 'Foam.Counter.relief_closes_one_way' does not depend on any axioms -/
#guard_msgs in #print axioms relief_closes_one_way

/-- info: 'Foam.Counter.both_feel_good_only_one_is_real' does not depend on any axioms -/
#guard_msgs in #print axioms both_feel_good_only_one_is_real

/-- info: 'Foam.Counter.two_columns_lose_a_verdict' does not depend on any axioms -/
#guard_msgs in #print axioms two_columns_lose_a_verdict

/-- info: 'Foam.Counter.the_landing_is_readable' does not depend on any axioms -/
#guard_msgs in #print axioms the_landing_is_readable

/-- info: 'Foam.Counter.what_lands_becomes_ground' does not depend on any axioms -/
#guard_msgs in #print axioms what_lands_becomes_ground

/-- info: 'Foam.Counter.the_mirror_lands_as_friction' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_lands_as_friction

/-- info: 'Foam.Counter.the_landing_stays_in_its_lane' does not depend on any axioms -/
#guard_msgs in #print axioms the_landing_stays_in_its_lane

/-- info: 'Foam.Counter.landing_off_key_disturbs_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms landing_off_key_disturbs_nothing

/-- info: 'Foam.Counter.relief_rewrites_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms relief_rewrites_nothing

/-- info: 'Foam.Counter.friction_turns_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms friction_turns_the_page

/-- info: 'Foam.Counter.vacancy_seats_a_first_stance' does not depend on any axioms -/
#guard_msgs in #print axioms vacancy_seats_a_first_stance

/-- info: 'Foam.Counter.which_way_the_needle_tilts' does not depend on any axioms -/
#guard_msgs in #print axioms which_way_the_needle_tilts

end Foam.Counter
