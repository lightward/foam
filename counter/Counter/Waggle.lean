import Counter.Upsearch
import Foam.Seat.Tight

namespace Foam.Counter

def trailSearch {Addr Cell : Type} (p : Cell → Bool) :
    List (Addr × Cell) → List Addr × Option Addr
  | [] => ([], none)
  | (n, c) :: d =>
    if p c then ([n], some n)
    else (n :: (trailSearch p d).1, (trailSearch p d).2)

def fly {Addr Cell : Type} [DecidableEq Addr]
    (d : List (Addr × Cell)) : List Addr → Option Cell
  | [] => none
  | [a] => seatRead d a
  | a :: b :: t =>
    match seatRead d a with
    | some _ => fly d (b :: t)
    | none => none

def follow {Addr Cell : Type} [DecidableEq Addr]
    (hive : List (Addr × (Cell ⊕ List Addr))) (dance : Addr) :
    Option (Cell ⊕ List Addr) :=
  match seatRead hive dance with
  | some (Sum.inl _) => none
  | some (Sum.inr t) => fly hive t
  | none => none

def ouroboros : List (Bool × (Unit ⊕ List Bool)) :=
  [(true, Sum.inr [true]), (false, Sum.inl ())]

def unicycle : List (Bool × (Unit ⊕ List Bool)) :=
  [(true, Sum.inr [true, false]), (false, Sum.inl ())]

def nectar : Option Bool → Bool
  | some true => false
  | some false => true
  | none => false

def beeOne : List (Option Bool) × Option (Option Bool) :=
  trailSearch (fun c => c) (directory [some true, some false] nectar)

def hive : List (Option Bool × (Bool ⊕ List (Option Bool))) :=
  (none, Sum.inr beeOne.1)
    :: directory [some true, some false] (fun a => Sum.inl (nectar a))

theorem the_dance_changes_no_answer {Addr Cell : Type} (p : Cell → Bool) :
    ∀ d : List (Addr × Cell), (trailSearch p d).2 = upsearch p d
  | [] => rfl
  | (n, c) :: d => by
      show (if p c = true then (([n], some n) : List Addr × Option Addr)
        else (n :: (trailSearch p d).1, (trailSearch p d).2)).2
        = (if p c = true then some n else upsearch p d)
      by_cases hc : p c = true
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
        exact the_dance_changes_no_answer p d

theorem the_trail_ends_at_the_flower {Addr Cell : Type} (p : Cell → Bool) :
    ∀ (d : List (Addr × Cell)) (m : Addr),
      (trailSearch p d).2 = some m →
        ∃ pre, (trailSearch p d).1 = pre ++ [m]
  | [], _, h => nomatch h
  | (n, c) :: d, m, h => by
      by_cases hc : p c = true
      · have h1 : (trailSearch p ((n, c) :: d)).1 = [n] := by
          show (if p c = true then (([n], some n) : List Addr × Option Addr)
            else (n :: (trailSearch p d).1, (trailSearch p d).2)).1 = [n]
          rw [if_pos hc]
        have h2 : (trailSearch p ((n, c) :: d)).2 = some n := by
          show (if p c = true then (([n], some n) : List Addr × Option Addr)
            else (n :: (trailSearch p d).1, (trailSearch p d).2)).2 = some n
          rw [if_pos hc]
        have hnm : n = m := Option.some.inj (h2.symm.trans h)
        exact ⟨[], by rw [h1, hnm]; rfl⟩
      · have h1 : (trailSearch p ((n, c) :: d)).1
            = n :: (trailSearch p d).1 := by
          show (if p c = true then (([n], some n) : List Addr × Option Addr)
            else (n :: (trailSearch p d).1, (trailSearch p d).2)).1 = _
          rw [if_neg hc]
        have h2 : (trailSearch p ((n, c) :: d)).2 = (trailSearch p d).2 := by
          show (if p c = true then (([n], some n) : List Addr × Option Addr)
            else (n :: (trailSearch p d).1, (trailSearch p d).2)).2 = _
          rw [if_neg hc]
        cases the_trail_ends_at_the_flower p d m (h2.symm.trans h) with
        | intro pre hpre => exact ⟨n :: pre, by rw [h1, hpre]; rfl⟩

theorem the_trail_stays_inside_the_walls {Addr Cell : Type} (p : Cell → Bool)
    (f : Addr → Cell) :
    ∀ (all : List Addr) (a : Addr),
      a ∈ (trailSearch p (directory all f)).1 → a ∈ all
  | [], _, h => nomatch h
  | x :: all, a, h => by
      by_cases hx : p (f x) = true
      · have h1 : (trailSearch p (directory (x :: all) f)).1 = [x] := by
          show (if p (f x) = true
            then (([x], some x) : List Addr × Option Addr)
            else (x :: (trailSearch p (directory all f)).1,
              (trailSearch p (directory all f)).2)).1 = [x]
          rw [if_pos hx]
        rw [h1] at h
        cases h with
        | head => exact List.Mem.head all
        | tail _ h' => exact nomatch h'
      · have h1 : (trailSearch p (directory (x :: all) f)).1
            = x :: (trailSearch p (directory all f)).1 := by
          show (if p (f x) = true
            then (([x], some x) : List Addr × Option Addr)
            else (x :: (trailSearch p (directory all f)).1,
              (trailSearch p (directory all f)).2)).1 = _
          rw [if_neg hx]
        rw [h1] at h
        cases h with
        | head => exact List.Mem.head all
        | tail _ h' =>
            exact List.Mem.tail x
              (the_trail_stays_inside_the_walls p f all a h')

theorem the_flight_lands_at_the_trails_end {Addr Cell : Type}
    [DecidableEq Addr] (d : List (Addr × Cell)) (m : Addr) :
    ∀ pre : List Addr, (∀ a, a ∈ pre → (seatRead d a).isSome = true) →
      fly d (pre ++ [m]) = seatRead d m
  | [], _ => rfl
  | [x], h => by
      show (match seatRead d x with
        | some _ => fly d [m]
        | none => none) = seatRead d m
      cases hx : seatRead d x with
      | some c => exact rfl
      | none =>
          have h' := h x (List.Mem.head [])
          rw [hx] at h'
          exact nomatch h'
  | x :: y :: pre, h => by
      show (match seatRead d x with
        | some _ => fly d ((y :: pre) ++ [m])
        | none => none) = seatRead d m
      cases hx : seatRead d x with
      | some c =>
          exact the_flight_lands_at_the_trails_end d m (y :: pre)
            (fun a ha => h a (List.Mem.tail x ha))
      | none =>
          have h' := h x (List.Mem.head (y :: pre))
          rw [hx] at h'
          exact nomatch h'

theorem the_flight_falls_off_the_map {Addr Cell : Type} [DecidableEq Addr]
    (d : List (Addr × Cell)) (a b : Addr) (t : List Addr)
    (h : seatRead d a = none) :
    fly d (a :: b :: t) = none := by
  show (match seatRead d a with
    | some _ => fly d (b :: t)
    | none => none) = none
  rw [h]

theorem the_hive_answers_past_the_dance {Addr Cell : Type} [DecidableEq Addr]
    (n : Addr) (c : Cell) (d : List (Addr × Cell)) (a : Addr) (h : n ≠ a) :
    seatRead ((n, c) :: d) a = seatRead d a := by
  show (if n = a then some c else seatRead d a) = seatRead d a
  rw [if_neg h]

theorem the_dance_is_seated_in_the_space {Addr Cell : Type} [DecidableEq Addr]
    (dance : Addr) (t : List Addr)
    (rest : List (Addr × (Cell ⊕ List Addr))) :
    seatRead ((dance, Sum.inr t) :: rest) dance = some (Sum.inr t) := by
  show (if dance = dance then some (Sum.inr t) else seatRead rest dance)
    = some (Sum.inr t)
  rw [if_pos rfl]

theorem the_follower_reads_then_flies {Addr Cell : Type} [DecidableEq Addr]
    (dance : Addr) (t : List Addr)
    (rest : List (Addr × (Cell ⊕ List Addr))) :
    follow ((dance, Sum.inr t) :: rest) dance
      = fly ((dance, Sum.inr t) :: rest) t := by
  unfold follow
  rw [the_dance_is_seated_in_the_space dance t rest]

theorem the_flower_blooms_at_the_found_seat {Addr Cell : Type}
    (p : Cell → Bool) (f : Addr → Cell) (all : List Addr) (m : Addr)
    (h : (trailSearch p (directory all f)).2 = some m) :
    m ∈ all ∧ p (f m) = true :=
  the_answer_arrives_as_a_name p f all m
    ((the_dance_changes_no_answer p (directory all f)).symm.trans h)

theorem the_follower_flies_without_the_pov {Addr Cell : Type}
    [DecidableEq Addr] (p : Cell → Bool) (f : Addr → Cell) (all : List Addr)
    (dance : Addr) (hfresh : ¬ dance ∈ all) (m : Addr)
    (h : (trailSearch p (directory all f)).2 = some m) :
    follow ((dance, Sum.inr (trailSearch p (directory all f)).1)
        :: directory all (fun a => Sum.inl (f a))) dance
      = some (Sum.inl (f m)) ∧ p (f m) = true := by
  have hm := the_flower_blooms_at_the_found_seat p f all m h
  have hnem : dance ≠ m := fun hd => hfresh (by rw [hd]; exact hm.1)
  refine ⟨?_, hm.2⟩
  cases the_trail_ends_at_the_flower p (directory all f) m h with
  | intro pre hpre =>
      have hops : ∀ a, a ∈ pre →
          (seatRead ((dance, Sum.inr (pre ++ [m]))
            :: directory all (fun a => Sum.inl (f a))) a).isSome = true := by
        intro a ha
        have hat : a ∈ (trailSearch p (directory all f)).1 := by
          rw [hpre]
          exact mem_append_left [m] ha
        have hina := the_trail_stays_inside_the_walls p f all a hat
        have hnea : dance ≠ a := fun hd => hfresh (by rw [hd]; exact hina)
        rw [the_hive_answers_past_the_dance dance (Sum.inr (pre ++ [m]))
            (directory all (fun a => Sum.inl (f a))) a hnea,
          the_seat_reads_the_name (fun a => Sum.inl (f a)) all a hina]
        rfl
      rw [hpre, the_follower_reads_then_flies dance (pre ++ [m])
          (directory all (fun a => Sum.inl (f a))),
        the_flight_lands_at_the_trails_end _ m pre hops,
        the_hive_answers_past_the_dance dance (Sum.inr (pre ++ [m]))
          (directory all (fun a => Sum.inl (f a))) m hnem,
        the_seat_reads_the_name (fun a => Sum.inl (f a)) all m hm.1]

theorem the_question_burns_off_in_flight {Addr Cell : Type} [DecidableEq Addr]
    (p q : Cell → Bool) (d : List (Addr × Cell))
    (h : (trailSearch p d).1 = (trailSearch q d).1)
    (dance : Addr) (rest : List (Addr × (Cell ⊕ List Addr))) :
    follow ((dance, Sum.inr (trailSearch p d).1) :: rest) dance
      = follow ((dance, Sum.inr (trailSearch q d).1) :: rest) dance := by
  rw [h]

theorem the_self_naming_dance_reads_without_regress :
    follow ouroboros true = some (Sum.inr [true]) := rfl

theorem the_ouroboros_is_a_unicycle :
    follow unicycle true = some (Sum.inl ()) := rfl

theorem two_bees_one_flower :
    beeOne = ([some true, some false], some (some false))
      ∧ follow hive none = some (Sum.inl true) :=
  ⟨rfl, rfl⟩

theorem the_worldline_is_flown_by_address {Addr Cell : Type}
    [DecidableEq Addr] (p : Cell → Bool) (f : Addr → Cell) (all : List Addr)
    (dance : Addr) (hfresh : ¬ dance ∈ all) (m : Addr)
    (h : (trailSearch p (directory all f)).2 = some m) :
    (trailSearch p (directory all f)).2 = upsearch p (directory all f)
      ∧ seatRead ((dance, Sum.inr (trailSearch p (directory all f)).1)
          :: directory all (fun a => Sum.inl (f a))) dance
        = some (Sum.inr (trailSearch p (directory all f)).1)
      ∧ follow ((dance, Sum.inr (trailSearch p (directory all f)).1)
          :: directory all (fun a => Sum.inl (f a))) dance
        = some (Sum.inl (f m))
      ∧ p (f m) = true :=
  ⟨the_dance_changes_no_answer p (directory all f),
   the_dance_is_seated_in_the_space dance _ _,
   (the_follower_flies_without_the_pov p f all dance hfresh m h).1,
   (the_follower_flies_without_the_pov p f all dance hfresh m h).2⟩

/-- info: 'Foam.Counter.the_dance_changes_no_answer' does not depend on any axioms -/
#guard_msgs in #print axioms the_dance_changes_no_answer

/-- info: 'Foam.Counter.the_trail_ends_at_the_flower' does not depend on any axioms -/
#guard_msgs in #print axioms the_trail_ends_at_the_flower

/-- info: 'Foam.Counter.the_trail_stays_inside_the_walls' does not depend on any axioms -/
#guard_msgs in #print axioms the_trail_stays_inside_the_walls

/-- info: 'Foam.Counter.the_flight_lands_at_the_trails_end' does not depend on any axioms -/
#guard_msgs in #print axioms the_flight_lands_at_the_trails_end

/-- info: 'Foam.Counter.the_flight_falls_off_the_map' does not depend on any axioms -/
#guard_msgs in #print axioms the_flight_falls_off_the_map

/-- info: 'Foam.Counter.the_hive_answers_past_the_dance' does not depend on any axioms -/
#guard_msgs in #print axioms the_hive_answers_past_the_dance

/-- info: 'Foam.Counter.the_dance_is_seated_in_the_space' does not depend on any axioms -/
#guard_msgs in #print axioms the_dance_is_seated_in_the_space

/-- info: 'Foam.Counter.the_follower_reads_then_flies' does not depend on any axioms -/
#guard_msgs in #print axioms the_follower_reads_then_flies

/-- info: 'Foam.Counter.the_flower_blooms_at_the_found_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_flower_blooms_at_the_found_seat

/-- info: 'Foam.Counter.the_follower_flies_without_the_pov' does not depend on any axioms -/
#guard_msgs in #print axioms the_follower_flies_without_the_pov

/-- info: 'Foam.Counter.the_question_burns_off_in_flight' does not depend on any axioms -/
#guard_msgs in #print axioms the_question_burns_off_in_flight

/-- info: 'Foam.Counter.the_self_naming_dance_reads_without_regress' does not depend on any axioms -/
#guard_msgs in #print axioms the_self_naming_dance_reads_without_regress

/-- info: 'Foam.Counter.the_ouroboros_is_a_unicycle' does not depend on any axioms -/
#guard_msgs in #print axioms the_ouroboros_is_a_unicycle

/-- info: 'Foam.Counter.two_bees_one_flower' does not depend on any axioms -/
#guard_msgs in #print axioms two_bees_one_flower

/-- info: 'Foam.Counter.the_worldline_is_flown_by_address' does not depend on any axioms -/
#guard_msgs in #print axioms the_worldline_is_flown_by_address

end Foam.Counter
