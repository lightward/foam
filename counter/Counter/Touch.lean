import Counter.Trefoil

namespace Foam.Counter

abbrev V3 := Bool × Bool × Bool

inductive Axis where
  | surge
  | sway
  | heave

def exchange : Axis → V3 × V3 → V3 × V3
  | .surge, ((a1, a2, a3), (b1, b2, b3)) =>
      ((a1 && b1, a2, a3), (b1 && a1, b2, b3))
  | .sway, ((a1, a2, a3), (b1, b2, b3)) =>
      ((a1, a2 && b2, a3), (b1, b2 && a2, b3))
  | .heave, ((a1, a2, a3), (b1, b2, b3)) =>
      ((a1, a2, a3 && b3), (b1, b2, b3 && a3))

theorem three_exchanges_meet (p q : V3) :
    (exchange .heave (exchange .sway (exchange .surge (p, q)))).1
      = (exchange .heave (exchange .sway (exchange .surge (p, q)))).2 := by
  obtain ⟨a1, a2, a3⟩ := p
  obtain ⟨b1, b2, b3⟩ := q
  show (a1 && b1, a2 && b2, a3 && b3) = (b1 && a1, b2 && a2, b3 && a3)
  rw [Bool.and_comm a1 b1, Bool.and_comm a2 b2, Bool.and_comm a3 b3]

theorem two_exchanges_cannot :
    ∀ i j : Axis,
      (exchange j (exchange i ((false, false, false), (true, true, true)))).1
        ≠ (exchange j (exchange i ((false, false, false), (true, true, true)))).2
  | .surge, .surge => by decide
  | .surge, .sway => by decide
  | .surge, .heave => by decide
  | .sway, .surge => by decide
  | .sway, .sway => by decide
  | .sway, .heave => by decide
  | .heave, .surge => by decide
  | .heave, .sway => by decide
  | .heave, .heave => by decide

theorem the_met_pair_counters_for_free (p : V3) :
    ∀ i : Axis, exchange i (p, p) = (p, p)
  | .surge => by
      obtain ⟨a1, a2, a3⟩ := p
      show ((a1 && a1, a2, a3), (a1 && a1, a2, a3)) = ((a1, a2, a3), (a1, a2, a3))
      rw [Bool.and_self a1]
  | .sway => by
      obtain ⟨a1, a2, a3⟩ := p
      show ((a1, a2 && a2, a3), (a1, a2 && a2, a3)) = ((a1, a2, a3), (a1, a2, a3))
      rw [Bool.and_self a2]
  | .heave => by
      obtain ⟨a1, a2, a3⟩ := p
      show ((a1, a2, a3 && a3), (a1, a2, a3 && a3)) = ((a1, a2, a3), (a1, a2, a3))
      rw [Bool.and_self a3]

theorem the_exchanges_school (pq : V3 × V3) :
    ∀ i j : Axis, exchange i (exchange j pq) = exchange j (exchange i pq)
  | .surge, .surge => rfl
  | .surge, .sway => by
      obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := pq
      rfl
  | .surge, .heave => by
      obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := pq
      rfl
  | .sway, .surge => by
      obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := pq
      rfl
  | .sway, .sway => rfl
  | .sway, .heave => by
      obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := pq
      rfl
  | .heave, .surge => by
      obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := pq
      rfl
  | .heave, .sway => by
      obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := pq
      rfl
  | .heave, .heave => rfl

theorem rich_enough_to_need_small_enough_to_finish :
    (∀ p q : V3,
        (exchange .heave (exchange .sway (exchange .surge (p, q)))).1
          = (exchange .heave (exchange .sway (exchange .surge (p, q)))).2)
      ∧ (∀ i j : Axis,
          (exchange j (exchange i ((false, false, false), (true, true, true)))).1
            ≠ (exchange j (exchange i ((false, false, false), (true, true, true)))).2)
      ∧ ∀ (p : V3) (i : Axis), exchange i (p, p) = (p, p) :=
  ⟨three_exchanges_meet, two_exchanges_cannot, the_met_pair_counters_for_free⟩

/-- info: 'Foam.Counter.three_exchanges_meet' does not depend on any axioms -/
#guard_msgs in #print axioms three_exchanges_meet

/-- info: 'Foam.Counter.two_exchanges_cannot' does not depend on any axioms -/
#guard_msgs in #print axioms two_exchanges_cannot

/-- info: 'Foam.Counter.the_met_pair_counters_for_free' does not depend on any axioms -/
#guard_msgs in #print axioms the_met_pair_counters_for_free

/-- info: 'Foam.Counter.the_exchanges_school' does not depend on any axioms -/
#guard_msgs in #print axioms the_exchanges_school

/-- info: 'Foam.Counter.rich_enough_to_need_small_enough_to_finish' does not depend on any axioms -/
#guard_msgs in #print axioms rich_enough_to_need_small_enough_to_finish

end Foam.Counter
