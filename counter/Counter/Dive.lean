import Counter.Cursor
import Counter.Hand
import Counter.Toll
import Counter.Trefoil
import Foam.Int

namespace Foam.Counter

theorem the_model_survives_the_dive (p : Page) : p.entry.page = p := rfl

theorem the_dive_returns_you_to_the_door (c : Cursor) :
    c.page.entry = c ↔ c.trail = [] := by
  constructor
  · intro h
    exact (congrArg Cursor.trail h).symm
  · intro h
    obtain ⟨f, tr⟩ := c
    have h : tr = [] := h
    subst h
    rfl

theorem the_surfacing_forgets_the_seat :
    ∃ c : Cursor, c.page.entry ≠ c := by
  refine ⟨⟨.blank, [.intoKids .blank]⟩, ?_⟩
  intro h
  exact nomatch (congrArg Cursor.trail h)

def parity : Nat → Bool
  | 0 => false
  | n + 1 => !(parity n)

theorem flip_flip (b : Bool) : (!(!b)) = b := by
  cases b <;> rfl

theorem even_of_parity_false : ∀ (n : Nat), parity n = false → ∃ k, n = 2 * k
  | 0, _ => ⟨0, rfl⟩
  | 1, h => nomatch h
  | n + 2, h => by
      have h : (!(!(parity n))) = false := h
      rw [flip_flip] at h
      obtain ⟨k, hk⟩ := even_of_parity_false n h
      exact ⟨k + 1, by rw [hk]; rfl⟩

theorem a_descent_lengthens_the_trail :
    ∀ (t : Tool) (c c' : Cursor), t ≠ Tool.ascend → t.use c = some c' →
      c'.trail.length = c.trail.length + 1
  | .ascend, _, _, hne, _ => absurd rfl hne
  | .enter, ⟨.click kids sibs, cs⟩, c', _, h => by
      have h : (some ⟨kids, .intoKids sibs :: cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | .enter, ⟨.blank, _⟩, _, _, h => nomatch h
  | .advance, ⟨.click kids sibs, cs⟩, c', _, h => by
      have h : (some ⟨sibs, .intoSibs kids :: cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | .advance, ⟨.blank, _⟩, _, _, h => nomatch h

theorem an_ascent_shortens_the_trail :
    ∀ (c c' : Cursor), Tool.ascend.use c = some c' →
      c.trail.length = c'.trail.length + 1
  | ⟨f, .intoKids sibs :: cs⟩, c', h => by
      have h : (some ⟨.click f sibs, cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | ⟨f, .intoSibs kids :: cs⟩, c', h => by
      have h : (some ⟨.click kids f, cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | ⟨_, []⟩, _, h => nomatch h

theorem the_walk_flips_the_parity :
    ∀ (ts : List Tool) (c c' : Cursor), steps ts c = some c' →
      parity (c.trail.length + ts.length) = parity c'.trail.length
  | [], c, c', h => by
      have h : (some c : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | t :: ts, c, c', h => by
      have h' : (t.use c).bind (steps ts) = some c' := h
      cases ht : t.use c with
      | none =>
        rw [ht] at h'
        exact nomatch h'
      | some c₁ =>
        rw [ht] at h'
        have ih := the_walk_flips_the_parity ts c₁ c' h'
        cases t with
        | ascend =>
          have hlen := an_ascent_shortens_the_trail c c₁ ht
          show parity ((c.trail.length + ts.length) + 1) = parity c'.trail.length
          rw [hlen, Nat.succ_add c₁.trail.length ts.length]
          show (!(!(parity (c₁.trail.length + ts.length)))) = parity c'.trail.length
          rw [flip_flip]
          exact ih
        | enter =>
          have hlen := a_descent_lengthens_the_trail .enter c c₁ (fun h => nomatch h) ht
          rw [hlen, Nat.succ_add c.trail.length ts.length] at ih
          show parity ((c.trail.length + ts.length) + 1) = parity c'.trail.length
          exact ih
        | advance =>
          have hlen := a_descent_lengthens_the_trail .advance c c₁ (fun h => nomatch h) ht
          rw [hlen, Nat.succ_add c.trail.length ts.length] at ih
          show parity ((c.trail.length + ts.length) + 1) = parity c'.trail.length
          exact ih

theorem parity_cancel : ∀ (n a : Nat), parity (a + n) = parity a → parity n = false
  | 0, _, _ => rfl
  | 1, a, h => by
      have h : (!(parity a)) = parity a := h
      cases hp : parity a with
      | false =>
        rw [hp] at h
        exact nomatch h
      | true =>
        rw [hp] at h
        exact nomatch h
  | n + 2, a, h => by
      have h : (!(!(parity (a + n)))) = parity a := h
      rw [flip_flip] at h
      have hn := parity_cancel n a h
      show (!(!(parity n))) = false
      rw [flip_flip]
      exact hn

theorem every_return_is_even (ts : List Tool) (c : Cursor)
    (h : steps ts c = some c) : ∃ k, ts.length = 2 * k :=
  even_of_parity_false ts.length
    (parity_cancel ts.length c.trail.length (the_walk_flips_the_parity ts c c h))

theorem a_windless_walk_grows :
    ∀ (ts : List Tool) (c c' : Cursor), (∀ t, t ∈ ts → t ≠ Tool.ascend) →
      steps ts c = some c' → c.trail.length + ts.length = c'.trail.length
  | [], c, c', _, h => by
      have h : (some c : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | t :: ts, c, c', hna, h => by
      have h' : (t.use c).bind (steps ts) = some c' := h
      cases ht : t.use c with
      | none =>
        rw [ht] at h'
        exact nomatch h'
      | some c₁ =>
        rw [ht] at h'
        have hlen := a_descent_lengthens_the_trail t c c₁ (hna t (.head _)) ht
        have ih := a_windless_walk_grows ts c₁ c' (fun t' ht' => hna t' (.tail _ ht')) h'
        rw [hlen, Nat.succ_add c.trail.length ts.length] at ih
        show (c.trail.length + ts.length) + 1 = c'.trail.length
        exact ih

theorem the_tree_cannot_wind (ts : List Tool) (c : Cursor)
    (hne : ts ≠ []) (hna : ∀ t, t ∈ ts → t ≠ Tool.ascend) :
    steps ts c ≠ some c := by
  intro h
  have hg := a_windless_walk_grows ts c c hna h
  have h0 : ts.length + c.trail.length = 0 + c.trail.length := by
    rw [Nat.zero_add, Nat.add_comm ts.length c.trail.length]
    exact hg
  have hz := add_right_cancel_nat c.trail.length ts.length 0 h0
  cases hts : ts with
  | nil => exact hne hts
  | cons t ts' =>
    rw [hts] at hz
    exact nomatch hz

theorem the_wheel_winds_where_the_tree_cannot :
    (∀ z, phase fullTurn z = phase [] z) ∧
      ∀ c : Cursor,
        steps [Tool.enter, Tool.enter, Tool.enter, Tool.enter] c ≠ some c := by
  refine ⟨fun z => the_keeper_knows_more_than_the_wheel.1 z, fun c => ?_⟩
  refine the_tree_cannot_wind _ c (fun h => nomatch h) ?_
  intro t ht
  cases ht with
  | head => exact fun h => nomatch h
  | tail _ ht =>
    cases ht with
    | head => exact fun h => nomatch h
    | tail _ ht =>
      cases ht with
      | head => exact fun h => nomatch h
      | tail _ ht =>
        cases ht with
        | head => exact fun h => nomatch h
        | tail _ ht => exact nomatch ht

/-- info: 'Foam.Counter.the_model_survives_the_dive' does not depend on any axioms -/
#guard_msgs in #print axioms the_model_survives_the_dive

/-- info: 'Foam.Counter.the_dive_returns_you_to_the_door' does not depend on any axioms -/
#guard_msgs in #print axioms the_dive_returns_you_to_the_door

/-- info: 'Foam.Counter.the_surfacing_forgets_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_surfacing_forgets_the_seat

/-- info: 'Foam.Counter.flip_flip' does not depend on any axioms -/
#guard_msgs in #print axioms flip_flip

/-- info: 'Foam.Counter.even_of_parity_false' does not depend on any axioms -/
#guard_msgs in #print axioms even_of_parity_false

/-- info: 'Foam.Counter.a_descent_lengthens_the_trail' does not depend on any axioms -/
#guard_msgs in #print axioms a_descent_lengthens_the_trail

/-- info: 'Foam.Counter.an_ascent_shortens_the_trail' does not depend on any axioms -/
#guard_msgs in #print axioms an_ascent_shortens_the_trail

/-- info: 'Foam.Counter.the_walk_flips_the_parity' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_flips_the_parity

/-- info: 'Foam.Counter.parity_cancel' does not depend on any axioms -/
#guard_msgs in #print axioms parity_cancel

/-- info: 'Foam.Counter.every_return_is_even' does not depend on any axioms -/
#guard_msgs in #print axioms every_return_is_even

/-- info: 'Foam.Counter.a_windless_walk_grows' does not depend on any axioms -/
#guard_msgs in #print axioms a_windless_walk_grows

/-- info: 'Foam.Counter.the_tree_cannot_wind' does not depend on any axioms -/
#guard_msgs in #print axioms the_tree_cannot_wind

/-- info: 'Foam.Counter.the_wheel_winds_where_the_tree_cannot' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_winds_where_the_tree_cannot

end Foam.Counter
