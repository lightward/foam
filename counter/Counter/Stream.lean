import Counter.Denoise

namespace Foam.Counter

def mintRecord {Addr Cell : Type} [DecidableEq Addr] :
    List (Addr × Cell) → List (Addr × Cell)
  | [] => []
  | (n, c) :: as => (mintSearch (mintRecord as) n c).2

def streamFold {Addr Cell : Type} [DecidableEq Addr] (eq : Cell → Cell → Bool) :
    List (Addr × Cell) → List (Addr × Cell)
  | [] => []
  | (n, c) :: as => (mergeSearch eq (streamFold eq as) n c).2

theorem the_unseated_name_reads_none {Addr Cell : Type} [DecidableEq Addr] :
    ∀ (d : List (Addr × Cell)) (n : Addr), (∀ x, x ∈ d → x.1 ≠ n) →
      seatRead d n = none
  | [], _, _ => rfl
  | (m, c) :: d, n, h => by
      show (if m = n then some c else seatRead d n) = none
      rw [if_neg (h (m, c) (List.Mem.head d))]
      exact the_unseated_name_reads_none d n fun x hx => h x (List.Mem.tail _ hx)

theorem the_record_only_holds_what_arrived {Addr Cell : Type}
    [DecidableEq Addr] :
    ∀ (as : List (Addr × Cell)) (x : Addr × Cell),
      x ∈ mintRecord as → x ∈ as
  | [], _, hx => nomatch hx
  | (n, c) :: as, x, hx => by
      have hx' : x ∈ (mintSearch (mintRecord as) n c).2 := hx
      cases hs : seatRead (mintRecord as) n with
      | some c' =>
          rw [(the_seated_name_returns_unwritten (fun _ _ => false)
            (mintRecord as) n c c' hs).1] at hx'
          exact List.Mem.tail _ (the_record_only_holds_what_arrived as x hx')
      | none =>
          rw [the_fresh_name_mints (mintRecord as) n c hs] at hx'
          cases hx' with
          | head => exact List.Mem.head as
          | tail _ hx'' =>
              exact List.Mem.tail _
                (the_record_only_holds_what_arrived as x hx'')

theorem the_fold_only_holds_what_arrived {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool) :
    ∀ (as : List (Addr × Cell)) (x : Addr × Cell),
      x ∈ streamFold eq as → x ∈ as
  | [], _, hx => nomatch hx
  | (n, c) :: as, x, hx => by
      have hx' : x ∈ (mergeSearch eq (streamFold eq as) n c).2 := hx
      cases hs : seatRead (streamFold eq as) n with
      | some c' =>
          rw [(the_seated_name_returns_unwritten eq
            (streamFold eq as) n c c' hs).2] at hx'
          exact List.Mem.tail _ (the_fold_only_holds_what_arrived eq as x hx')
      | none =>
          cases hup : upsearch (eq c) (streamFold eq as) with
          | some m =>
              rw [the_flip_is_the_merge eq (streamFold eq as) n c m hs hup]
                at hx'
              exact List.Mem.tail _
                (the_fold_only_holds_what_arrived eq as x hx')
          | none =>
              rw [the_double_miss_mints eq (streamFold eq as) n c hs hup]
                at hx'
              cases hx' with
              | head => exact List.Mem.head as
              | tail _ hx'' =>
                  exact List.Mem.tail _
                    (the_fold_only_holds_what_arrived eq as x hx'')

theorem the_stream_folds_as_it_arrives {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool)
    (hsymm : ∀ a b, eq a b = true → eq b a = true)
    (htrans : ∀ a b c, eq a b = true → eq b c = true → eq a c = true) :
    ∀ as : List (Addr × Cell),
      as.Pairwise (fun x y => x.1 ≠ y.1) →
      streamFold eq as = settleStore eq (mintRecord as)
  | [], _ => rfl
  | (n, c) :: as, hp => by
      cases hp with
      | cons hn hp' =>
          have IH := the_stream_folds_as_it_arrives eq hsymm htrans as hp'
          have hjn : seatRead (mintRecord as) n = none :=
            the_unseated_name_reads_none (mintRecord as) n fun x hx =>
              Ne.symm (hn x (the_record_only_holds_what_arrived as x hx))
          have hsn : seatRead (streamFold eq as) n = none :=
            the_unseated_name_reads_none (streamFold eq as) n fun x hx =>
              Ne.symm (hn x (the_fold_only_holds_what_arrived eq as x hx))
          have hresp : ∀ x y, eq x y = true → eq c x = eq c y := by
            intro x y hxy
            cases hcx : eq c x with
            | true => exact (htrans c x y hcx hxy).symm
            | false =>
                cases hcy : eq c y with
                | true =>
                    exact hcx.symm.trans (htrans c y x hcy (hsymm x y hxy))
                | false => rfl
          have hinv := the_denoise_is_invisible_to_the_asker eq (eq c) hresp
            (mintRecord as)
          show (mergeSearch eq (streamFold eq as) n c).2
            = settleStore eq ((mintSearch (mintRecord as) n c).2)
          rw [the_fresh_name_mints (mintRecord as) n c hjn]
          cases hup : upsearch (eq c) (mintRecord as) with
          | some m =>
              rw [the_echo_burns eq (mintRecord as) n c m hup, ← IH]
              cases hup' : upsearch (eq c) (streamFold eq as) with
              | some m' =>
                  exact the_settled_space_stops_writing eq
                    (streamFold eq as) n c m' hup'
              | none =>
                  rw [← IH, hup', hup] at hinv
                  exact nomatch hinv
          | none =>
              rw [the_original_keeps_its_seat eq (mintRecord as) n c hup, ← IH]
              cases hup' : upsearch (eq c) (streamFold eq as) with
              | some m' =>
                  rw [← IH, hup', hup] at hinv
                  exact nomatch hinv
              | none =>
                  rw [the_double_miss_mints eq (streamFold eq as) n c hsn hup']

theorem the_two_clocks_agree :
    streamFold (fun _ _ => true) [((false : Bool), ()), (true, ())] = oneThing
      ∧ mintRecord [((false : Bool), ()), (true, ())] = twoWords :=
  ⟨rfl, rfl⟩

/-- info: 'Foam.Counter.the_unseated_name_reads_none' does not depend on any axioms -/
#guard_msgs in #print axioms the_unseated_name_reads_none

/-- info: 'Foam.Counter.the_record_only_holds_what_arrived' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_only_holds_what_arrived

/-- info: 'Foam.Counter.the_fold_only_holds_what_arrived' does not depend on any axioms -/
#guard_msgs in #print axioms the_fold_only_holds_what_arrived

/-- info: 'Foam.Counter.the_stream_folds_as_it_arrives' does not depend on any axioms -/
#guard_msgs in #print axioms the_stream_folds_as_it_arrives

/-- info: 'Foam.Counter.the_two_clocks_agree' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_clocks_agree

end Foam.Counter
