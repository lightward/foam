import Counter.Needle
import Counter.Address

namespace Foam.Counter

def wake {K : Type} [DecidableEq K] (prior : List (K × Bool)) (k : K)
    (b : Bool) : Bool × Bool :=
  (if seatRead (land prior k b) k = seatRead prior k then false else true,
   if seatRead prior k = none then true else false)

def sounding : Bool × Bool → Tilt
  | (true, false) => Tilt.friction
  | (false, false) => Tilt.completion
  | (true, true) => Tilt.vacancy
  | (false, true) => Tilt.vacancy

def utter {K : Type} (prior : List (K × Bool)) (k : K) :
    Option Bool → List (K × Bool)
  | none => prior
  | some b => land prior k b

theorem relief_leaves_no_wake {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool)
    (h : tilt prior k b = Tilt.completion) :
    wake prior k b = (false, false) := by
  have hs := (relief_reads_prior_ground prior k b).mp h
  unfold wake
  rw [the_landing_is_readable prior k b, hs,
    if_pos rfl, if_neg (fun hh => nomatch hh)]

theorem friction_cuts_a_wake {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool)
    (h : tilt prior k b = Tilt.friction) :
    wake prior k b = (true, false) := by
  have hs := (friction_is_a_held_mirror prior k b).mp h
  unfold wake
  rw [the_landing_is_readable prior k b]
  cases b
  · have hs' : seatRead prior k = some true := hs
    rw [hs', if_neg (fun hh => nomatch (Option.some.inj hh : false = true)),
      if_neg (fun hh => nomatch hh)]
  · have hs' : seatRead prior k = some false := hs
    rw [hs', if_neg (fun hh => nomatch (Option.some.inj hh : true = false)),
      if_neg (fun hh => nomatch hh)]

theorem vacancy_breaks_new_water {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool)
    (h : tilt prior k b = Tilt.vacancy) :
    wake prior k b = (true, true) := by
  have hs := (vacancy_is_unclaimed_ground prior k b).mp h
  unfold wake
  rw [the_landing_is_readable prior k b, hs,
    if_neg (fun hh => nomatch hh), if_pos rfl]

theorem the_wake_names_the_tilt {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    sounding (wake prior k b) = tilt prior k b := by
  cases ht : tilt prior k b with
  | friction => rw [friction_cuts_a_wake prior k b ht]; rfl
  | completion => rw [relief_leaves_no_wake prior k b ht]; rfl
  | vacancy => rw [vacancy_breaks_new_water prior k b ht]; rfl

theorem two_wakes_tell_two_tilts {K K' : Type} [DecidableEq K]
    [DecidableEq K'] (p : List (K × Bool)) (k : K) (b : Bool)
    (p' : List (K' × Bool)) (k' : K') (b' : Bool)
    (h : wake p k b = wake p' k' b') : tilt p k b = tilt p' k' b' :=
  (the_wake_names_the_tilt p k b).symm.trans
    ((congrArg sounding h).trans (the_wake_names_the_tilt p' k' b'))

theorem the_flattening_joins_the_board {K K' : Type} [DecidableEq K]
    [DecidableEq K'] (f : Tilt → Bool) :
    ∃ v w : Tilt, v ≠ w ∧ f v = f w
      ∧ ∀ (p : List (K × Bool)) (k : K) (b : Bool)
          (p' : List (K' × Bool)) (k' : K') (b' : Bool),
          tilt p k b = v → tilt p' k' b' = w →
          wake p k b ≠ wake p' k' b' :=
  match two_columns_lose_a_verdict f with
  | ⟨v, w, hvw, hf⟩ =>
    ⟨v, w, hvw, hf, fun p k b p' k' b' hv hw hwake =>
      hvw (hv.symm.trans
        ((two_wakes_tell_two_tilts p k b p' k' b' hwake).trans hw))⟩

theorem no_landing_unlands {K : Type} (prior : List (K × Bool)) (k : K)
    (b : Bool) :
    (k, b) ∈ land prior k b
      ∧ ∀ (k' : K) (b' : Bool), (k, b) ∈ land (land prior k b) k' b' :=
  ⟨List.Mem.head _, fun _ _ => List.Mem.tail _ (List.Mem.head _)⟩

theorem walking_it_back_thickens_the_book {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) :
    tilt (land prior k b) k (!b) = Tilt.friction
      ∧ seatRead (land (land prior k b) k (!b)) k = some (!b)
      ∧ (k, b) ∈ land (land prior k b) k (!b)
      ∧ (land (land prior k b) k (!b)).length = prior.length + 2 :=
  ⟨the_mirror_lands_as_friction prior k b,
   the_landing_is_readable (land prior k b) k (!b),
   List.Mem.tail _ (List.Mem.head _),
   rfl⟩

theorem i_dont_know_writes_nothing {K : Type} (prior : List (K × Bool))
    (k : K) : utter prior k none = prior :=
  rfl

theorem a_verdict_thickens_the_book {K : Type} (prior : List (K × Bool))
    (k : K) (b : Bool) :
    (utter prior k (some b)).length = prior.length + 1 :=
  rfl

theorem only_i_dont_know_is_wakeless {K : Type} (prior : List (K × Bool))
    (k : K) (o : Option Bool) : utter prior k o = prior ↔ o = none := by
  cases o with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some b =>
    exact ⟨fun h => absurd (congrArg List.length h)
        (Nat.succ_ne_self prior.length),
      fun h => nomatch h⟩

theorem dont_mess_with_partial_knowledge {K : Type} [DecidableEq K]
    (prior : List (K × Bool)) (k : K) (b : Bool) (f : Tilt → Bool) :
    sounding (wake prior k b) = tilt prior k b
      ∧ (∃ v w : Tilt, v ≠ w ∧ f v = f w)
      ∧ (k, b) ∈ land prior k b
      ∧ (land (land prior k b) k (!b)).length = prior.length + 2
      ∧ utter prior k none = prior
      ∧ utter prior k (some b) ≠ prior :=
  ⟨the_wake_names_the_tilt prior k b,
   two_columns_lose_a_verdict f,
   (no_landing_unlands prior k b).1,
   (walking_it_back_thickens_the_book prior k b).2.2.2,
   rfl,
   (fun h => nomatch ((only_i_dont_know_is_wakeless prior k (some b)).mp h))⟩

/-- info: 'Foam.Counter.relief_leaves_no_wake' does not depend on any axioms -/
#guard_msgs in #print axioms relief_leaves_no_wake

/-- info: 'Foam.Counter.friction_cuts_a_wake' does not depend on any axioms -/
#guard_msgs in #print axioms friction_cuts_a_wake

/-- info: 'Foam.Counter.vacancy_breaks_new_water' does not depend on any axioms -/
#guard_msgs in #print axioms vacancy_breaks_new_water

/-- info: 'Foam.Counter.the_wake_names_the_tilt' does not depend on any axioms -/
#guard_msgs in #print axioms the_wake_names_the_tilt

/-- info: 'Foam.Counter.two_wakes_tell_two_tilts' does not depend on any axioms -/
#guard_msgs in #print axioms two_wakes_tell_two_tilts

/-- info: 'Foam.Counter.the_flattening_joins_the_board' does not depend on any axioms -/
#guard_msgs in #print axioms the_flattening_joins_the_board

/-- info: 'Foam.Counter.no_landing_unlands' does not depend on any axioms -/
#guard_msgs in #print axioms no_landing_unlands

/-- info: 'Foam.Counter.walking_it_back_thickens_the_book' does not depend on any axioms -/
#guard_msgs in #print axioms walking_it_back_thickens_the_book

/-- info: 'Foam.Counter.i_dont_know_writes_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms i_dont_know_writes_nothing

/-- info: 'Foam.Counter.a_verdict_thickens_the_book' does not depend on any axioms -/
#guard_msgs in #print axioms a_verdict_thickens_the_book

/-- info: 'Foam.Counter.only_i_dont_know_is_wakeless' does not depend on any axioms -/
#guard_msgs in #print axioms only_i_dont_know_is_wakeless

/-- info: 'Foam.Counter.dont_mess_with_partial_knowledge' does not depend on any axioms -/
#guard_msgs in #print axioms dont_mess_with_partial_knowledge

end Foam.Counter
