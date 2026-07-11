import Counter.Address

namespace Foam.Counter

def upsearch {Addr Cell : Type} (p : Cell → Bool) :
    List (Addr × Cell) → Option Addr
  | [] => none
  | (n, c) :: d => if p c then some n else upsearch p d

theorem the_answer_arrives_as_a_name {Addr Cell : Type} (p : Cell → Bool)
    (f : Addr → Cell) :
    ∀ (all : List Addr) (n : Addr),
      upsearch p (directory all f) = some n → n ∈ all ∧ p (f n) = true
  | [], _, h => nomatch h
  | x :: all, n, h => by
      have h' : (if p (f x) = true then some x
          else upsearch p (directory all f)) = some n := h
      by_cases hx : p (f x) = true
      · rw [if_pos hx] at h'
        cases Option.some.inj h'
        exact ⟨List.Mem.head all, hx⟩
      · rw [if_neg hx] at h'
        have hall := the_answer_arrives_as_a_name p f all n h'
        exact ⟨List.Mem.tail x hall.1, hall.2⟩

theorem what_is_there_can_be_found {Addr Cell : Type} (p : Cell → Bool)
    (f : Addr → Cell) :
    ∀ (all : List Addr), (∃ a, a ∈ all ∧ p (f a) = true) →
      ∃ n, upsearch p (directory all f) = some n
  | [], ⟨_, ha, _⟩ => nomatch ha
  | x :: all, ⟨a, ha, hp⟩ => by
      have h' : upsearch p (directory (x :: all) f)
          = (if p (f x) = true then some x
              else upsearch p (directory all f)) := rfl
      by_cases hx : p (f x) = true
      · exact ⟨x, h'.trans (if_pos hx)⟩
      · cases ha with
        | head => exact absurd hp hx
        | tail _ ha' =>
            cases what_is_there_can_be_found p f all ⟨a, ha', hp⟩ with
            | intro n hn => exact ⟨n, h'.trans ((if_neg hx).trans hn)⟩

theorem the_found_carries_its_rejections {Addr Cell : Type} (p : Cell → Bool)
    (f : Addr → Cell) :
    ∀ (all : List Addr) (n : Addr),
      upsearch p (directory all f) = some n →
        ∃ before after, all = before ++ n :: after
          ∧ ∀ a, a ∈ before → ¬ p (f a) = true
  | [], _, h => nomatch h
  | x :: all, n, h => by
      have h' : (if p (f x) = true then some x
          else upsearch p (directory all f)) = some n := h
      by_cases hx : p (f x) = true
      · rw [if_pos hx] at h'
        cases Option.some.inj h'
        exact ⟨[], all, rfl, fun a ha => nomatch ha⟩
      · rw [if_neg hx] at h'
        cases the_found_carries_its_rejections p f all n h' with
        | intro before rest =>
            cases rest with
            | intro after hba =>
                refine ⟨x :: before, after, ?_, ?_⟩
                · rw [hba.1]
                  rfl
                · intro a ha
                  cases ha with
                  | head => exact hx
                  | tail _ ha' => exact hba.2 a ha'

theorem the_empty_hand_holds_every_rejection {Addr Cell : Type}
    (p : Cell → Bool) (f : Addr → Cell) :
    ∀ (all : List Addr), upsearch p (directory all f) = none →
      ∀ a, a ∈ all → ¬ p (f a) = true
  | [], _, _, ha => nomatch ha
  | x :: all, h, a, ha => by
      have h' : (if p (f x) = true then some x
          else upsearch p (directory all f)) = none := h
      by_cases hx : p (f x) = true
      · rw [if_pos hx] at h'
        exact nomatch h'
      · rw [if_neg hx] at h'
        cases ha with
        | head => exact hx
        | tail _ ha' =>
            exact the_empty_hand_holds_every_rejection p f all h' a ha'

theorem the_index_chooses_the_word :
    upsearch (fun _ => true) (directory [true, false] (fun _ => ())) = some true
      ∧ upsearch (fun _ => true) (directory [false, true] (fun _ => ()))
        = some false :=
  ⟨rfl, rfl⟩

theorem the_new_word_reads_back {Addr Cell : Type} [DecidableEq Addr]
    (p : Cell → Bool) (f : Addr → Cell) (all : List Addr) (n : Addr)
    (h : upsearch p (directory all f) = some n) :
    seatRead (directory all f) n = some (f n) ∧ p (f n) = true :=
  ⟨the_seat_reads_the_name f all n (the_answer_arrives_as_a_name p f all n h).1,
   (the_answer_arrives_as_a_name p f all n h).2⟩

theorem the_search_registers_flip {Addr Cell : Type} [DecidableEq Addr]
    (p : Cell → Bool) (f : Addr → Cell) (all : List Addr)
    (a b : Addr) (hab : a ≠ b) (hf : f a = f b) :
    (¬ ∃ name : Cell → Addr, ∀ x, name (f x) = x)
      ∧ ((∃ c, c ∈ all ∧ p (f c) = true) →
          ∃ n, upsearch p (directory all f) = some n)
      ∧ (∀ n, upsearch p (directory all f) = some n →
          n ∈ all ∧ p (f n) = true
            ∧ seatRead (directory all f) n = some (f n)) :=
  ⟨the_cell_never_says_its_own_name f a b hab hf,
   what_is_there_can_be_found p f all,
   fun n h =>
     ⟨(the_answer_arrives_as_a_name p f all n h).1,
      (the_answer_arrives_as_a_name p f all n h).2,
      (the_new_word_reads_back p f all n h).1⟩⟩

/-- info: 'Foam.Counter.the_answer_arrives_as_a_name' does not depend on any axioms -/
#guard_msgs in #print axioms the_answer_arrives_as_a_name

/-- info: 'Foam.Counter.what_is_there_can_be_found' does not depend on any axioms -/
#guard_msgs in #print axioms what_is_there_can_be_found

/-- info: 'Foam.Counter.the_found_carries_its_rejections' does not depend on any axioms -/
#guard_msgs in #print axioms the_found_carries_its_rejections

/-- info: 'Foam.Counter.the_empty_hand_holds_every_rejection' does not depend on any axioms -/
#guard_msgs in #print axioms the_empty_hand_holds_every_rejection

/-- info: 'Foam.Counter.the_index_chooses_the_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_index_chooses_the_word

/-- info: 'Foam.Counter.the_new_word_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_new_word_reads_back

/-- info: 'Foam.Counter.the_search_registers_flip' does not depend on any axioms -/
#guard_msgs in #print axioms the_search_registers_flip

end Foam.Counter
