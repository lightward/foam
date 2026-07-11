import Counter.Address

namespace Foam.Counter

def seatWalk {Addr Cell : Type} [DecidableEq Addr] :
    List (Addr × Cell) → Addr → Nat
  | [], _ => 0
  | (n, _) :: d, a => if n = a then 0 else seatWalk d a + 1

theorem the_answer_ignores_the_walk {Addr Cell : Type} [DecidableEq Addr]
    (all all' : List Addr) (hall : ∀ a, a ∈ all) (hall' : ∀ a, a ∈ all')
    (f : Addr → Cell) :
    ∀ a, seatRead (directory all f) a = seatRead (directory all' f) a :=
  fun a => (the_seat_reads_the_name f all a (hall a)).trans
    (the_seat_reads_the_name f all' a (hall' a)).symm

theorem the_warm_seat_answers_at_the_door {Addr Cell : Type} [DecidableEq Addr]
    (a : Addr) (rest : List Addr) (f : Addr → Cell) :
    seatWalk (directory (a :: rest) f) a = 0 := by
  show (if a = a then 0 else seatWalk (directory rest f) a + 1) = 0
  rw [if_pos rfl]

theorem the_cold_seat_answers_at_the_far_wall {Addr Cell : Type}
    [DecidableEq Addr] (f : Addr → Cell) :
    ∀ (before : List Addr) (a : Addr), ¬ a ∈ before →
      seatWalk (directory (before ++ [a]) f) a = before.length
  | [], a, _ => by
      show (if a = a then 0
        else seatWalk (directory ([] : List Addr) f) a + 1) = 0
      rw [if_pos rfl]
  | x :: before, a, h => by
      show (if x = a then 0
        else seatWalk (directory (before ++ [a]) f) a + 1)
        = before.length + 1
      have hx : ¬ x = a := fun hxa => h (hxa ▸ List.Mem.head before)
      rw [if_neg hx,
        the_cold_seat_answers_at_the_far_wall f before a
          (fun h' => h (List.Mem.tail x h'))]

theorem every_guest_is_found_inside_the_walls {Addr Cell : Type}
    [DecidableEq Addr] (f : Addr → Cell) :
    ∀ (all : List Addr) (a : Addr), a ∈ all →
      seatWalk (directory all f) a < all.length
  | [], _, h => nomatch h
  | x :: all, a, h => by
      show (if x = a then 0 else seatWalk (directory all f) a + 1)
        < all.length + 1
      by_cases hx : x = a
      · rw [if_pos hx]
        exact Nat.zero_lt_succ _
      · rw [if_neg hx]
        refine Nat.succ_lt_succ ?_
        cases h with
        | head => exact absurd rfl hx
        | tail _ h' => exact every_guest_is_found_inside_the_walls f all a h'

theorem two_hotels_one_guestbook {Cell : Type} (f : Bool → Cell) :
    (∀ a, seatRead (directory [true, false] f) a
        = seatRead (directory [false, true] f) a)
      ∧ seatWalk (directory [true, false] f) true = 0
      ∧ seatWalk (directory [false, true] f) true = 1 :=
  ⟨the_answer_ignores_the_walk [true, false] [false, true]
      (fun b => match b with
        | true => List.Mem.head _
        | false => List.Mem.tail _ (List.Mem.head _))
      (fun b => match b with
        | true => List.Mem.tail _ (List.Mem.head _)
        | false => List.Mem.head _) f,
   rfl, rfl⟩

theorem temperature_is_the_only_tell {Addr Cell Cell' : Type}
    [DecidableEq Addr] (all all' : List Addr)
    (hall : ∀ a, a ∈ all) (hall' : ∀ a, a ∈ all')
    (f : Addr → Cell) (g : Bool → Cell') :
    (∀ a, seatRead (directory all f) a = seatRead (directory all' f) a)
      ∧ (∀ a, a ∈ all → seatWalk (directory all f) a < all.length)
      ∧ seatWalk (directory [true, false] g) true = 0
      ∧ seatWalk (directory [false, true] g) true = 1 :=
  ⟨the_answer_ignores_the_walk all all' hall hall' f,
   fun a ha => every_guest_is_found_inside_the_walls f all a ha,
   (two_hotels_one_guestbook g).2.1,
   (two_hotels_one_guestbook g).2.2⟩

/-- info: 'Foam.Counter.the_answer_ignores_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_answer_ignores_the_walk

/-- info: 'Foam.Counter.the_warm_seat_answers_at_the_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_warm_seat_answers_at_the_door

/-- info: 'Foam.Counter.the_cold_seat_answers_at_the_far_wall' does not depend on any axioms -/
#guard_msgs in #print axioms the_cold_seat_answers_at_the_far_wall

/-- info: 'Foam.Counter.every_guest_is_found_inside_the_walls' does not depend on any axioms -/
#guard_msgs in #print axioms every_guest_is_found_inside_the_walls

/-- info: 'Foam.Counter.two_hotels_one_guestbook' does not depend on any axioms -/
#guard_msgs in #print axioms two_hotels_one_guestbook

/-- info: 'Foam.Counter.temperature_is_the_only_tell' does not depend on any axioms -/
#guard_msgs in #print axioms temperature_is_the_only_tell

end Foam.Counter
