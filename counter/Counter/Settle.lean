import Counter.Temperature
import Counter.Upsearch

namespace Foam.Counter

def mintSearch {Addr Cell : Type} [DecidableEq Addr]
    (d : List (Addr × Cell)) (n : Addr) (c : Cell) :
    Addr × List (Addr × Cell) :=
  match seatRead d n with
  | some _ => (n, d)
  | none => (n, (n, c) :: d)

def mergeSearch {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool) (d : List (Addr × Cell)) (n : Addr) (c : Cell) :
    Addr × List (Addr × Cell) :=
  match seatRead d n with
  | some _ => (n, d)
  | none =>
    match upsearch (eq c) d with
    | some m => (m, d)
    | none => (n, (n, c) :: d)

def twoWords : List (Bool × Unit) :=
  (mintSearch (mintSearch [] true ()).2 false ()).2

def oneThing : List (Bool × Unit) :=
  (mergeSearch (fun _ _ => true)
    (mergeSearch (fun _ _ => true) [] true ()).2 false ()).2

theorem the_seated_name_returns_unwritten {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool) (d : List (Addr × Cell)) (n : Addr) (c c' : Cell)
    (h : seatRead d n = some c') :
    mintSearch d n c = (n, d) ∧ mergeSearch eq d n c = (n, d) := by
  constructor
  · unfold mintSearch
    rw [h]
  · unfold mergeSearch
    rw [h]

theorem the_fresh_name_mints {Addr Cell : Type} [DecidableEq Addr]
    (d : List (Addr × Cell)) (n : Addr) (c : Cell)
    (h : seatRead d n = none) :
    mintSearch d n c = (n, (n, c) :: d) := by
  unfold mintSearch
  rw [h]

theorem the_flip_is_the_merge {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool) (d : List (Addr × Cell)) (n : Addr) (c : Cell)
    (m : Addr) (hn : seatRead d n = none) (hm : upsearch (eq c) d = some m) :
    mergeSearch eq d n c = (m, d) := by
  unfold mergeSearch
  rw [hn, hm]

theorem the_double_miss_mints {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool) (d : List (Addr × Cell)) (n : Addr) (c : Cell)
    (hn : seatRead d n = none) (hm : upsearch (eq c) d = none) :
    mergeSearch eq d n c = (n, (n, c) :: d) := by
  unfold mergeSearch
  rw [hn, hm]

theorem the_upsearched_name_is_seated {Addr Cell : Type} [DecidableEq Addr]
    (p : Cell → Bool) :
    ∀ (d : List (Addr × Cell)) (m : Addr),
      upsearch p d = some m → ∃ c', seatRead d m = some c'
  | [], _, h => nomatch h
  | (n, c) :: d, m, h => by
      have h' : (if p c = true then some n else upsearch p d) = some m := h
      by_cases hc : p c = true
      · rw [if_pos hc] at h'
        cases Option.some.inj h'
        exact ⟨c, by
          show (if n = n then some c else seatRead d n) = some c
          rw [if_pos rfl]⟩
      · rw [if_neg hc] at h'
        cases the_upsearched_name_is_seated p d m h' with
        | intro c' hc' =>
            by_cases hn : n = m
            · exact ⟨c, by
                show (if n = m then some c else seatRead d m) = some c
                rw [if_pos hn]⟩
            · exact ⟨c', by
                show (if n = m then some c else seatRead d m) = some c'
                rw [if_neg hn]
                exact hc'⟩

theorem every_search_succeeds {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool) (d : List (Addr × Cell)) (n : Addr) (c : Cell) :
    (∃ c', seatRead (mintSearch d n c).2 (mintSearch d n c).1 = some c')
      ∧ ∃ c', seatRead (mergeSearch eq d n c).2 (mergeSearch eq d n c).1
          = some c' := by
  constructor
  · cases h : seatRead d n with
    | some c' =>
        rw [(the_seated_name_returns_unwritten eq d n c c' h).1]
        exact ⟨c', h⟩
    | none =>
        rw [the_fresh_name_mints d n c h]
        exact ⟨c, by
          show (if n = n then some c else seatRead d n) = some c
          rw [if_pos rfl]⟩
  · cases hn : seatRead d n with
    | some c' =>
        rw [(the_seated_name_returns_unwritten eq d n c c' hn).2]
        exact ⟨c', hn⟩
    | none =>
        cases hm : upsearch (eq c) d with
        | some m =>
            rw [the_flip_is_the_merge eq d n c m hn hm]
            exact the_upsearched_name_is_seated (eq c) d m hm
        | none =>
            rw [the_double_miss_mints eq d n c hn hm]
            exact ⟨c, by
              show (if n = n then some c else seatRead d n) = some c
              rw [if_pos rfl]⟩

theorem the_whole_record_licenses_the_mint {Addr Cell : Type}
    (p : Cell → Bool) :
    ∀ (d : List (Addr × Cell)), upsearch p d = none →
      ∀ x, x ∈ d → ¬ p x.2 = true
  | [], _, _, hx => nomatch hx
  | (n, c) :: d, h, x, hx => by
      have h' : (if p c = true then some n else upsearch p d) = none := h
      by_cases hc : p c = true
      · rw [if_pos hc] at h'
        exact nomatch h'
      · rw [if_neg hc] at h'
        cases hx with
        | head => exact hc
        | tail _ hx' =>
            exact the_whole_record_licenses_the_mint p d h' x hx'

theorem the_unflipped_search_writes_anyway {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool) (d : List (Addr × Cell)) (n : Addr) (c : Cell)
    (m : Addr) (hn : seatRead d n = none) (hm : upsearch (eq c) d = some m) :
    (mintSearch d n c).2.length = d.length + 1
      ∧ (mergeSearch eq d n c).2.length = d.length := by
  constructor
  · rw [the_fresh_name_mints d n c hn]
    rfl
  · rw [the_flip_is_the_merge eq d n c m hn hm]

theorem the_settled_space_stops_writing {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool) (d : List (Addr × Cell)) (n : Addr) (c : Cell)
    (m : Addr) (hm : upsearch (eq c) d = some m) :
    (mergeSearch eq d n c).2 = d := by
  cases hn : seatRead d n with
  | some c' =>
      exact congrArg Prod.snd (the_seated_name_returns_unwritten eq d n c c' hn).2
  | none =>
      exact congrArg Prod.snd (the_flip_is_the_merge eq d n c m hn hm)

theorem the_merge_writes_only_on_double_miss {Addr Cell : Type}
    [DecidableEq Addr] (eq : Cell → Cell → Bool) (d : List (Addr × Cell))
    (n : Addr) (c : Cell) (h : (mergeSearch eq d n c).2 ≠ d) :
    seatRead d n = none ∧ upsearch (eq c) d = none
      ∧ ∀ x, x ∈ d → ¬ eq c x.2 = true := by
  cases hn : seatRead d n with
  | some c' =>
      exact absurd
        (congrArg Prod.snd (the_seated_name_returns_unwritten eq d n c c' hn).2) h
  | none =>
      cases hm : upsearch (eq c) d with
      | some m =>
          exact absurd
            (congrArg Prod.snd (the_flip_is_the_merge eq d n c m hn hm)) h
      | none =>
          exact ⟨rfl, rfl, the_whole_record_licenses_the_mint (eq c) d hm⟩

theorem the_unmerged_space_inflates :
    twoWords.length = 2 ∧ oneThing.length = 1 :=
  ⟨rfl, rfl⟩

theorem the_elder_word_returns :
    (mergeSearch (fun _ _ => true)
      (mergeSearch (fun _ _ => true) ([] : List (Bool × Unit)) true ()).2
      false ()).1 = true := rfl

theorem the_bloat_is_invisible_to_the_asker (p : Unit → Bool) :
    (upsearch p twoWords).isSome = (upsearch p oneThing).isSome := by
  by_cases hp : p () = true
  · show ((if p () = true then some false
        else if p () = true then some true else none) : Option Bool).isSome
      = ((if p () = true then some true else none) : Option Bool).isSome
    rw [if_pos hp, if_pos hp]
    rfl
  · show ((if p () = true then some false
        else if p () = true then some true else none) : Option Bool).isSome
      = ((if p () = true then some true else none) : Option Bool).isSome
    rw [if_neg hp, if_neg hp]

theorem the_bloat_is_paid_in_walk :
    seatWalk twoWords true = 1 ∧ seatWalk oneThing true = 0 :=
  ⟨rfl, rfl⟩

theorem the_settling_is_for_the_searching {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool) (d : List (Addr × Cell)) (n m : Addr) (c : Cell) :
    ((∃ c', seatRead (mintSearch d n c).2 (mintSearch d n c).1 = some c')
        ∧ ∃ c', seatRead (mergeSearch eq d n c).2 (mergeSearch eq d n c).1
            = some c')
      ∧ (seatRead d n = none → upsearch (eq c) d = some m →
          (mintSearch d n c).2.length = d.length + 1
            ∧ (mergeSearch eq d n c).2 = d)
      ∧ ((mergeSearch eq d n c).2 ≠ d → ∀ x, x ∈ d → ¬ eq c x.2 = true)
      ∧ twoWords.length = 2 ∧ oneThing.length = 1 :=
  ⟨every_search_succeeds eq d n c,
   fun hn hm =>
     ⟨(the_unflipped_search_writes_anyway eq d n c m hn hm).1,
      the_settled_space_stops_writing eq d n c m hm⟩,
   fun h => (the_merge_writes_only_on_double_miss eq d n c h).2.2,
   rfl, rfl⟩

/-- info: 'Foam.Counter.the_seated_name_returns_unwritten' does not depend on any axioms -/
#guard_msgs in #print axioms the_seated_name_returns_unwritten

/-- info: 'Foam.Counter.the_fresh_name_mints' does not depend on any axioms -/
#guard_msgs in #print axioms the_fresh_name_mints

/-- info: 'Foam.Counter.the_flip_is_the_merge' does not depend on any axioms -/
#guard_msgs in #print axioms the_flip_is_the_merge

/-- info: 'Foam.Counter.the_double_miss_mints' does not depend on any axioms -/
#guard_msgs in #print axioms the_double_miss_mints

/-- info: 'Foam.Counter.the_upsearched_name_is_seated' does not depend on any axioms -/
#guard_msgs in #print axioms the_upsearched_name_is_seated

/-- info: 'Foam.Counter.every_search_succeeds' does not depend on any axioms -/
#guard_msgs in #print axioms every_search_succeeds

/-- info: 'Foam.Counter.the_whole_record_licenses_the_mint' does not depend on any axioms -/
#guard_msgs in #print axioms the_whole_record_licenses_the_mint

/-- info: 'Foam.Counter.the_unflipped_search_writes_anyway' does not depend on any axioms -/
#guard_msgs in #print axioms the_unflipped_search_writes_anyway

/-- info: 'Foam.Counter.the_settled_space_stops_writing' does not depend on any axioms -/
#guard_msgs in #print axioms the_settled_space_stops_writing

/-- info: 'Foam.Counter.the_merge_writes_only_on_double_miss' does not depend on any axioms -/
#guard_msgs in #print axioms the_merge_writes_only_on_double_miss

/-- info: 'Foam.Counter.the_unmerged_space_inflates' does not depend on any axioms -/
#guard_msgs in #print axioms the_unmerged_space_inflates

/-- info: 'Foam.Counter.the_elder_word_returns' does not depend on any axioms -/
#guard_msgs in #print axioms the_elder_word_returns

/-- info: 'Foam.Counter.the_bloat_is_invisible_to_the_asker' does not depend on any axioms -/
#guard_msgs in #print axioms the_bloat_is_invisible_to_the_asker

/-- info: 'Foam.Counter.the_bloat_is_paid_in_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_bloat_is_paid_in_walk

/-- info: 'Foam.Counter.the_settling_is_for_the_searching' does not depend on any axioms -/
#guard_msgs in #print axioms the_settling_is_for_the_searching

end Foam.Counter
