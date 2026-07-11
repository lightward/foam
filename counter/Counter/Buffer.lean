import Counter.Stream

namespace Foam.Counter

theorem the_buffer_pays_once {Addr Cell : Type} [DecidableEq Addr] :
    ∀ (xs : List (Addr × Cell)) (n₀ : Addr) (c : Cell),
      streamFold (fun _ _ => true) (xs ++ [(n₀, c)]) = [(n₀, c)]
  | [], _, _ => rfl
  | (m, cm) :: xs, n₀, c => by
      show (mergeSearch (fun _ _ => true)
        (streamFold (fun _ _ => true) (xs ++ [(n₀, c)])) m cm).2 = [(n₀, c)]
      rw [the_buffer_pays_once xs n₀ c]
      cases hs : seatRead [(n₀, c)] m with
      | some c' =>
          rw [(the_seated_name_returns_unwritten (fun _ _ => true)
            [(n₀, c)] m cm c' hs).2]
      | none =>
          rw [the_flip_is_the_merge (fun _ _ => true) [(n₀, c)] m cm n₀ hs rfl]

theorem the_unbuffered_pays_every_time {Addr Cell : Type} [DecidableEq Addr] :
    ∀ as : List (Addr × Cell), as.Pairwise (fun x y => x.1 ≠ y.1) →
      (mintRecord as).length = as.length
  | [], _ => rfl
  | (n, c) :: as, hp => by
      cases hp with
      | cons hn hp' =>
          have hjn : seatRead (mintRecord as) n = none :=
            the_unseated_name_reads_none (mintRecord as) n fun x hx =>
              Ne.symm (hn x (the_record_only_holds_what_arrived as x hx))
          show ((mintSearch (mintRecord as) n c).2).length = as.length + 1
          rw [the_fresh_name_mints (mintRecord as) n c hjn]
          show (mintRecord as).length + 1 = as.length + 1
          rw [the_unbuffered_pays_every_time as hp']

theorem the_scheduler_signs_the_index :
    streamFold (fun _ _ => true) [((false : Bool), ()), (true, ())]
        = [(true, ())]
      ∧ streamFold (fun _ _ => true) [((true : Bool), ()), (false, ())]
          = [(false, ())]
      ∧ ∀ p : Unit → Bool,
          (upsearch p [((true : Bool), ())]).isSome
            = (upsearch p [((false : Bool), ())]).isSome := by
  refine ⟨rfl, rfl, fun p => ?_⟩
  by_cases hp : p () = true
  · show ((if p () = true then some true else none) : Option Bool).isSome
      = ((if p () = true then some false else none) : Option Bool).isSome
    rw [if_pos hp, if_pos hp]
    rfl
  · show ((if p () = true then some true else none) : Option Bool).isSome
      = ((if p () = true then some false else none) : Option Bool).isSome
    rw [if_neg hp, if_neg hp]

theorem the_late_search_rides_the_early_walk :
    (mergeSearch (fun _ _ => true) [((true : Bool), ())] false ()).1 = true
      ∧ (mergeSearch (fun _ _ => true) [((true : Bool), ())] false ()).2
          = [(true, ())]
      ∧ seatWalk [((true : Bool), ())] true = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem the_arrows_decouple_only_in_the_buffer {Addr Cell : Type}
    [DecidableEq Addr] (xs : List (Addr × Cell)) (n₀ : Addr) (c : Cell)
    (as : List (Addr × Cell)) (hp : as.Pairwise (fun x y => x.1 ≠ y.1)) :
    streamFold (fun _ _ => true) (xs ++ [(n₀, c)]) = [(n₀, c)]
      ∧ (mintRecord as).length = as.length :=
  ⟨the_buffer_pays_once xs n₀ c, the_unbuffered_pays_every_time as hp⟩

/-- info: 'Foam.Counter.the_buffer_pays_once' does not depend on any axioms -/
#guard_msgs in #print axioms the_buffer_pays_once

/-- info: 'Foam.Counter.the_unbuffered_pays_every_time' does not depend on any axioms -/
#guard_msgs in #print axioms the_unbuffered_pays_every_time

/-- info: 'Foam.Counter.the_scheduler_signs_the_index' does not depend on any axioms -/
#guard_msgs in #print axioms the_scheduler_signs_the_index

/-- info: 'Foam.Counter.the_late_search_rides_the_early_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_late_search_rides_the_early_walk

/-- info: 'Foam.Counter.the_arrows_decouple_only_in_the_buffer' does not depend on any axioms -/
#guard_msgs in #print axioms the_arrows_decouple_only_in_the_buffer

end Foam.Counter
