import Counter.Upsearch
import Foam.Backstage

namespace Foam.Counter

def frontSearch {State Probe A : Type} [DecidableEq A]
    (o : State → Probe → A) (self other : State) : List Probe → Option Probe
  | [] => none
  | p :: ps =>
      if o other p = o self p then frontSearch o self other ps else some p

theorem the_answer_arrives_as_a_probe {State Probe A : Type} [DecidableEq A]
    (o : State → Probe → A) (self other : State) :
    ∀ (ps : List Probe) (p : Probe),
      frontSearch o self other ps = some p → p ∈ ps ∧ ¬ o other p = o self p
  | [], _, h => nomatch h
  | q :: ps, p, h => by
      have h' : (if o other q = o self q then frontSearch o self other ps
          else some q) = some p := h
      by_cases hq : o other q = o self q
      · rw [if_pos hq] at h'
        have hps := the_answer_arrives_as_a_probe o self other ps p h'
        exact ⟨List.Mem.tail q hps.1, hps.2⟩
      · rw [if_neg hq] at h'
        cases Option.some.inj h'
        exact ⟨List.Mem.head ps, hq⟩

theorem what_differs_can_be_found {State Probe A : Type} [DecidableEq A]
    (o : State → Probe → A) (self other : State) :
    ∀ ps : List Probe, (∃ p, p ∈ ps ∧ ¬ o other p = o self p) →
      ∃ p, frontSearch o self other ps = some p
  | [], ⟨_, hp, _⟩ => nomatch hp
  | q :: ps, ⟨p, hp, hne⟩ => by
      have h' : frontSearch o self other (q :: ps)
          = (if o other q = o self q then frontSearch o self other ps
              else some q) := rfl
      by_cases hq : o other q = o self q
      · cases hp with
        | head => exact absurd hq hne
        | tail _ hp' =>
            cases what_differs_can_be_found o self other ps ⟨p, hp', hne⟩ with
            | intro n hn => exact ⟨n, h'.trans ((if_pos hq).trans hn)⟩
      · exact ⟨q, h'.trans (if_neg hq)⟩

theorem you_cannot_find_yourself {State Probe A : Type} [DecidableEq A]
    (o : State → Probe → A) (self : State) :
    ∀ ps : List Probe, frontSearch o self self ps = none
  | [] => rfl
  | q :: ps => by
      show (if o self q = o self q then frontSearch o self self ps
        else some q) = none
      rw [if_pos rfl]
      exact you_cannot_find_yourself o self ps

theorem the_twin_is_never_found {State Probe A : Type} [DecidableEq A]
    (o : State → Probe → A) (self other : State) (h : indist o self other) :
    ∀ ps : List Probe, frontSearch o self other ps = none
  | [] => rfl
  | q :: ps => by
      show (if o other q = o self q then frontSearch o self other ps
        else some q) = none
      rw [if_pos (h q).symm]
      exact the_twin_is_never_found o self other h ps

theorem no_lens_reveals_the_twin {State Probe A B : Type} [DecidableEq B]
    (o : State → Probe → A) (g : A → B) (self other : State)
    (h : indist o self other) :
    ∀ ps : List Probe, frontSearch (fun s p => g (o s p)) self other ps = none :=
  the_twin_is_never_found (fun s p => g (o s p)) self other
    fun p => congrArg g (h p)

theorem the_found_has_its_own_pov {State Probe A : Type} [DecidableEq A]
    (o : State → Probe → A) (self other : State) (ps : List Probe) (p : Probe)
    (h : frontSearch o self other ps = some p) :
    ¬ indist o self other :=
  fun hind =>
    (the_answer_arrives_as_a_probe o self other ps p h).2 (hind p).symm

theorem the_empty_hand_holds_every_agreement {State Probe A : Type}
    [DecidableEq A] (o : State → Probe → A) (self other : State) :
    ∀ ps : List Probe, frontSearch o self other ps = none →
      ∀ p, p ∈ ps → o other p = o self p
  | [], _, _, hp => nomatch hp
  | q :: ps, h, p, hp => by
      have h' : (if o other q = o self q then frontSearch o self other ps
          else some q) = none := h
      by_cases hq : o other q = o self q
      · rw [if_pos hq] at h'
        cases hp with
        | head => exact hq
        | tail _ hp' =>
            exact the_empty_hand_holds_every_agreement o self other ps h' p hp'
      · rw [if_neg hq] at h'
        exact nomatch h'

theorem the_seat_still_finds_the_twin {Addr State Probe A : Type}
    [DecidableEq Addr] [DecidableEq A] (o : State → Probe → A)
    (all : List Addr) (f : Addr → State) (a b : Addr)
    (ha : a ∈ all) (hb : b ∈ all) (h : indist o (f a) (f b)) :
    seatRead (directory all f) a = some (f a)
      ∧ seatRead (directory all f) b = some (f b)
      ∧ ∀ ps : List Probe, frontSearch o (f a) (f b) ps = none :=
  ⟨the_seat_reads_the_name f all a ha,
   the_seat_reads_the_name f all b hb,
   the_twin_is_never_found o (f a) (f b) h⟩

theorem two_seats_one_pov :
    seatRead (directory [true, false] (fun a => a)) true = some true
      ∧ seatRead (directory [true, false] (fun a => a)) false = some false
      ∧ ∀ ps : List Unit,
          frontSearch (fun (_ : Bool) (_ : Unit) => ()) true false ps = none :=
  ⟨rfl, rfl,
   the_twin_is_never_found (fun _ _ => ()) true false fun _ => rfl⟩

theorem only_a_pov_can_be_found {State Probe A B : Type} [DecidableEq A]
    [DecidableEq B] (o : State → Probe → A) (g : A → B) (self other : State) :
    (∀ ps p, frontSearch o self other ps = some p →
        p ∈ ps ∧ ¬ o other p = o self p ∧ ¬ indist o self other)
      ∧ (∀ ps, (∃ p, p ∈ ps ∧ ¬ o other p = o self p) →
          ∃ p, frontSearch o self other ps = some p)
      ∧ (∀ ps, frontSearch o self self ps = none)
      ∧ (indist o self other →
          ∀ ps, frontSearch (fun s p => g (o s p)) self other ps = none) :=
  ⟨fun ps p h =>
     ⟨(the_answer_arrives_as_a_probe o self other ps p h).1,
      (the_answer_arrives_as_a_probe o self other ps p h).2,
      the_found_has_its_own_pov o self other ps p h⟩,
   what_differs_can_be_found o self other,
   you_cannot_find_yourself o self,
   fun h ps => no_lens_reveals_the_twin o g self other h ps⟩

/-- info: 'Foam.Counter.the_answer_arrives_as_a_probe' does not depend on any axioms -/
#guard_msgs in #print axioms the_answer_arrives_as_a_probe

/-- info: 'Foam.Counter.what_differs_can_be_found' does not depend on any axioms -/
#guard_msgs in #print axioms what_differs_can_be_found

/-- info: 'Foam.Counter.you_cannot_find_yourself' does not depend on any axioms -/
#guard_msgs in #print axioms you_cannot_find_yourself

/-- info: 'Foam.Counter.the_twin_is_never_found' does not depend on any axioms -/
#guard_msgs in #print axioms the_twin_is_never_found

/-- info: 'Foam.Counter.no_lens_reveals_the_twin' does not depend on any axioms -/
#guard_msgs in #print axioms no_lens_reveals_the_twin

/-- info: 'Foam.Counter.the_found_has_its_own_pov' does not depend on any axioms -/
#guard_msgs in #print axioms the_found_has_its_own_pov

/-- info: 'Foam.Counter.the_empty_hand_holds_every_agreement' does not depend on any axioms -/
#guard_msgs in #print axioms the_empty_hand_holds_every_agreement

/-- info: 'Foam.Counter.the_seat_still_finds_the_twin' does not depend on any axioms -/
#guard_msgs in #print axioms the_seat_still_finds_the_twin

/-- info: 'Foam.Counter.two_seats_one_pov' does not depend on any axioms -/
#guard_msgs in #print axioms two_seats_one_pov

/-- info: 'Foam.Counter.only_a_pov_can_be_found' does not depend on any axioms -/
#guard_msgs in #print axioms only_a_pov_can_be_found

end Foam.Counter
