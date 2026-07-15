import Counter.Cursor
import Foam.Int

namespace Foam.Counter

def hand (c : Cursor) : List (Option Cursor) :=
  [Tool.ascend.use c, Tool.enter.use c, Tool.advance.use c]

theorem the_hand_holds_three (c : Cursor) : (hand c).length = 3 := rfl

theorem a_new_hand_means_a_move (c c' : Cursor) (h : hand c ≠ hand c') : c ≠ c' :=
  fun hc => h (congrArg hand hc)

theorem no_card_stays_seated :
    ∀ (t : Tool) (c : Cursor), t.use c ≠ some c
  | .ascend, ⟨f, .intoKids sibs :: cs⟩ => by
      intro h
      have h : (some ⟨.click f sibs, cs⟩ : Option Cursor) = some ⟨f, .intoKids sibs :: cs⟩ := h
      injection h with h
      injection h with _ ht
      exact Nat.succ_ne_self cs.length (congrArg List.length ht).symm
  | .ascend, ⟨f, .intoSibs kids :: cs⟩ => by
      intro h
      have h : (some ⟨.click kids f, cs⟩ : Option Cursor) = some ⟨f, .intoSibs kids :: cs⟩ := h
      injection h with h
      injection h with _ ht
      exact Nat.succ_ne_self cs.length (congrArg List.length ht).symm
  | .ascend, ⟨_, []⟩ => fun h => nomatch h
  | .enter, ⟨.click kids sibs, cs⟩ => by
      intro h
      have h : (some ⟨kids, .intoKids sibs :: cs⟩ : Option Cursor) = some ⟨.click kids sibs, cs⟩ := h
      injection h with h
      injection h with _ ht
      exact Nat.succ_ne_self cs.length (congrArg List.length ht)
  | .enter, ⟨.blank, _⟩ => fun h => nomatch h
  | .advance, ⟨.click kids sibs, cs⟩ => by
      intro h
      have h : (some ⟨sibs, .intoSibs kids :: cs⟩ : Option Cursor) = some ⟨.click kids sibs, cs⟩ := h
      injection h with h
      injection h with _ ht
      exact Nat.succ_ne_self cs.length (congrArg List.length ht)
  | .advance, ⟨.blank, _⟩ => fun h => nomatch h

theorem every_use_mints_a_card_it_never_held (t : Tool) (c c' : Cursor)
    (h : t.use c = some c') :
    (∃ t' : Tool, t'.use c' = some c) ∧ ∀ t₀ : Tool, t₀.use c ≠ some c := by
  refine ⟨?_, fun t₀ => no_card_stays_seated t₀ c⟩
  cases t with
  | ascend => exact the_trail_remembers_the_way_down c c' h
  | enter => exact ⟨.ascend, every_entrance_writes_its_exit c c' h⟩
  | advance => exact ⟨.ascend, every_advance_writes_its_exit c c' h⟩

theorem the_two_vacancies_hold_one_hand :
    ∃ c₁ c₂ : Cursor, c₁ ≠ c₂ ∧ c₁.page = c₂.page ∧ hand c₁ = hand c₂ := by
  refine ⟨⟨.blank, [.intoKids .blank]⟩, ⟨.blank, [.intoSibs .blank]⟩, ?_, rfl, rfl⟩
  intro h
  have ht : ([.intoKids .blank] : List Crumb) = [.intoSibs .blank] :=
    congrArg Cursor.trail h
  injection ht with hh _
  exact nomatch hh

theorem only_vacancies_share_hands :
    ∀ (c₁ c₂ : Cursor), hand c₁ = hand c₂ →
      c₁ = c₂ ∨ (c₁.focus = .blank ∧ c₂.focus = .blank)
  | ⟨.click k₁ s₁, cs₁⟩, ⟨.click k₂ s₂, cs₂⟩, h => by
      have h : [Tool.ascend.use ⟨.click k₁ s₁, cs₁⟩,
                (some ⟨k₁, .intoKids s₁ :: cs₁⟩ : Option Cursor),
                some ⟨s₁, .intoSibs k₁ :: cs₁⟩]
             = [Tool.ascend.use ⟨.click k₂ s₂, cs₂⟩,
                some ⟨k₂, .intoKids s₂ :: cs₂⟩,
                some ⟨s₂, .intoSibs k₂ :: cs₂⟩] := h
      injection h with _ h
      injection h with h _
      injection h with h
      injection h with hf ht
      injection ht with hc ht
      injection hc with hs
      subst hf
      subst hs
      subst ht
      exact Or.inl rfl
  | ⟨.click k₁ s₁, cs₁⟩, ⟨.blank, cs₂⟩, h => by
      have h : [Tool.ascend.use ⟨.click k₁ s₁, cs₁⟩,
                (some ⟨k₁, .intoKids s₁ :: cs₁⟩ : Option Cursor),
                some ⟨s₁, .intoSibs k₁ :: cs₁⟩]
             = [Tool.ascend.use ⟨.blank, cs₂⟩, none, none] := h
      injection h with _ h
      injection h with h _
      exact nomatch h
  | ⟨.blank, cs₁⟩, ⟨.click k₂ s₂, cs₂⟩, h => by
      have h : [Tool.ascend.use ⟨.blank, cs₁⟩, (none : Option Cursor), none]
             = [Tool.ascend.use ⟨.click k₂ s₂, cs₂⟩,
                some ⟨k₂, .intoKids s₂ :: cs₂⟩,
                some ⟨s₂, .intoSibs k₂ :: cs₂⟩] := h
      injection h with _ h
      injection h with h _
      exact nomatch h
  | ⟨.blank, _⟩, ⟨.blank, _⟩, _ => Or.inr ⟨rfl, rfl⟩

theorem the_blank_entry_deals_no_card :
    hand (Page.blank.entry) = [none, none, none] := rfl

theorem the_blank_page_can_only_be_met :
    ∀ (ts : List Tool) (c : Cursor),
      steps ts Page.blank.entry = some c → ts = [] ∧ c = Page.blank.entry
  | [], c, h => by
      have h : (some (Page.blank.entry) : Option Cursor) = some c := h
      injection h with h
      exact ⟨rfl, h.symm⟩
  | .ascend :: _, _, h => nomatch h
  | .enter :: _, _, h => nomatch h
  | .advance :: _, _, h => nomatch h

theorem succ_add_ne : ∀ (a b : Nat), (b + a) + 1 ≠ a
  | 0, _, h => nomatch h
  | a + 1, b, h => by
      have h : ((b + a) + 1) + 1 = a + 1 := h
      injection h with h
      exact succ_add_ne a b h

theorem one_add_add_ne_left (a b : Nat) : (1 + a) + b ≠ a := by
  intro h
  have h' : b + (1 + a) = a := by
    rw [Nat.add_comm b (1 + a)]
    exact h
  have h'' : b + (a + 1) = a := by
    rw [← Nat.add_comm 1 a]
    exact h'
  exact succ_add_ne a b h''

theorem one_add_add_ne_right : ∀ (b a : Nat), (1 + a) + b ≠ b
  | 0, a, h => by
      have h' : a + 1 = 0 := by
        rw [← Nat.add_comm 1 a]
        exact h
      exact nomatch h'
  | b + 1, a, h => by
      have h : ((1 + a) + b) + 1 = b + 1 := h
      injection h with h
      exact one_add_add_ne_right b a h

theorem no_page_swallows_itself (kids sibs : Page) :
    Page.click kids sibs ≠ kids ∧ Page.click kids sibs ≠ sibs := by
  constructor
  · intro h
    have hc : (1 + kids.census) + sibs.census = kids.census := congrArg Page.census h
    exact one_add_add_ne_left kids.census sibs.census hc
  · intro h
    have hc : (1 + kids.census) + sibs.census = sibs.census := congrArg Page.census h
    exact one_add_add_ne_right sibs.census kids.census hc

theorem a_costless_trail_is_no_trail :
    ∀ (cs : List Crumb), trailCensus cs = 0 → cs = []
  | [], _ => rfl
  | .intoKids sibs :: cs, h => by
      have h : (1 + sibs.census) + trailCensus cs = 0 := h
      rw [Nat.add_comm (1 + sibs.census) (trailCensus cs),
          Nat.add_comm 1 sibs.census] at h
      exact nomatch h
  | .intoSibs kids :: cs, h => by
      have h : (1 + kids.census) + trailCensus cs = 0 := h
      rw [Nat.add_comm (1 + kids.census) (trailCensus cs),
          Nat.add_comm 1 kids.census] at h
      exact nomatch h

theorem add_right_cancel_nat : ∀ (n m k : Nat), m + n = k + n → m = k
  | 0, _, _, h => h
  | n + 1, m, k, h => by
      have h : (m + n) + 1 = (k + n) + 1 := h
      injection h with h
      exact add_right_cancel_nat n m k h

theorem the_whole_shows_only_at_the_entry (c : Cursor) :
    c.focus = c.page ↔ c.trail = [] := by
  obtain ⟨f, tr⟩ := c
  constructor
  · intro h
    have hc : f.census = (plug f tr).census := congrArg Page.census h
    rw [the_census_splits_at_the_seat] at hc
    have h0 : 0 + f.census = trailCensus tr + f.census := by
      rw [Nat.zero_add, Nat.add_comm (trailCensus tr) f.census]
      exact hc
    exact a_costless_trail_is_no_trail tr
      (add_right_cancel_nat f.census 0 (trailCensus tr) h0).symm
  · intro h
    have h : tr = [] := h
    subst h
    rfl

theorem the_regress_grounds_at_the_seat (c : Cursor) (h : c.trail ≠ []) :
    c.focus ≠ c.page ∧ plug c.focus c.trail = c.page :=
  ⟨fun hf => h ((the_whole_shows_only_at_the_entry c).mp hf), rfl⟩

/-- info: 'Foam.Counter.the_hand_holds_three' does not depend on any axioms -/
#guard_msgs in #print axioms the_hand_holds_three

/-- info: 'Foam.Counter.a_new_hand_means_a_move' does not depend on any axioms -/
#guard_msgs in #print axioms a_new_hand_means_a_move

/-- info: 'Foam.Counter.no_card_stays_seated' does not depend on any axioms -/
#guard_msgs in #print axioms no_card_stays_seated

/-- info: 'Foam.Counter.every_use_mints_a_card_it_never_held' does not depend on any axioms -/
#guard_msgs in #print axioms every_use_mints_a_card_it_never_held

/-- info: 'Foam.Counter.the_two_vacancies_hold_one_hand' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_vacancies_hold_one_hand

/-- info: 'Foam.Counter.only_vacancies_share_hands' does not depend on any axioms -/
#guard_msgs in #print axioms only_vacancies_share_hands

/-- info: 'Foam.Counter.the_blank_entry_deals_no_card' does not depend on any axioms -/
#guard_msgs in #print axioms the_blank_entry_deals_no_card

/-- info: 'Foam.Counter.the_blank_page_can_only_be_met' does not depend on any axioms -/
#guard_msgs in #print axioms the_blank_page_can_only_be_met

/-- info: 'Foam.Counter.succ_add_ne' does not depend on any axioms -/
#guard_msgs in #print axioms succ_add_ne

/-- info: 'Foam.Counter.one_add_add_ne_left' does not depend on any axioms -/
#guard_msgs in #print axioms one_add_add_ne_left

/-- info: 'Foam.Counter.one_add_add_ne_right' does not depend on any axioms -/
#guard_msgs in #print axioms one_add_add_ne_right

/-- info: 'Foam.Counter.no_page_swallows_itself' does not depend on any axioms -/
#guard_msgs in #print axioms no_page_swallows_itself

/-- info: 'Foam.Counter.a_costless_trail_is_no_trail' does not depend on any axioms -/
#guard_msgs in #print axioms a_costless_trail_is_no_trail

/-- info: 'Foam.Counter.add_right_cancel_nat' does not depend on any axioms -/
#guard_msgs in #print axioms add_right_cancel_nat

/-- info: 'Foam.Counter.the_whole_shows_only_at_the_entry' does not depend on any axioms -/
#guard_msgs in #print axioms the_whole_shows_only_at_the_entry

/-- info: 'Foam.Counter.the_regress_grounds_at_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_regress_grounds_at_the_seat

end Foam.Counter
