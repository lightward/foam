import Counter.Health

namespace Foam.Counter

def maxRank {H : Type} (r : H → Nat) : Quiver H → Nat
  | [] => 0
  | e :: es => nmax (r e.2) (maxRank r es)

theorem le_maxRank {H : Type} (r : H → Nat) :
    ∀ (q : Quiver H), ∀ e ∈ q, r e.2 ≤ maxRank r q
  | [], _, h => nomatch h
  | f :: es, e, h => by
      cases h with
      | head => exact le_nmax_left _ _
      | tail _ h' => exact Nat.le_trans (le_maxRank r es e h') (le_nmax_right _ _)

theorem nmax_zero_right (x : Nat) : nmax x 0 = x := by
  show (if x ≤ 0 then 0 else x) = x
  by_cases h : x ≤ 0
  · rw [if_pos h]
    cases x with
    | zero => rfl
    | succ k => exact absurd h (Nat.not_succ_le_zero k)
  · rw [if_neg h]

theorem maxRank_attained {H : Type} (r : H → Nat) :
    ∀ q : Quiver H, q ≠ [] → ∃ e, e ∈ q ∧ r e.2 = maxRank r q
  | [], h => absurd rfl h
  | f :: es, _ => by
      show ∃ e, e ∈ f :: es ∧ r e.2 = nmax (r f.2) (maxRank r es)
      cases es with
      | nil =>
          refine ⟨f, List.Mem.head _, ?_⟩
          rw [show maxRank r [] = 0 from rfl, nmax_zero_right]
      | cons g gs =>
          cases nmax_cases (r f.2) (maxRank r (g :: gs)) with
          | inl hm => exact ⟨f, List.Mem.head _, hm.symm⟩
          | inr hm =>
              obtain ⟨e, he, hre⟩ := maxRank_attained r (g :: gs) (List.cons_ne_nil g gs)
              exact ⟨e, List.Mem.tail f he, by rw [hre, hm]⟩

theorem every_sorted_world_has_a_stuck_seat {H : Type} {q : Quiver H} {r : H → Nat}
    (hs : sortedBy r q) (hne : q ≠ []) :
    ∃ a, (∃ e, e ∈ q ∧ e.2 = a) ∧ stuck q a := by
  obtain ⟨e, he, hmax⟩ := maxRank_attained r q hne
  refine ⟨e.2, ⟨e, he, rfl⟩, ?_⟩
  intro b hb
  have h1 : maxRank r q < r b := by
    rw [← hmax]
    exact hs (e.2, b) hb
  exact absurd (Nat.lt_of_lt_of_le h1 (le_maxRank r q (e.2, b) hb))
    (Nat.lt_irrefl _)

theorem no_seat_on_the_cycle_is_stuck {H : Type} {q : Quiver H} {a : H}
    (p : Path q a a) :
    ∀ e ∈ p.edges, ¬ stuck q e.1 := by
  intro e he hstuck
  exact hstuck e.2 (reach_within_quiver p e he)

theorem the_ring_holds_its_own_debt {H : Type} {q : Quiver H} {a : H}
    (p : Path q a a) (hp : p.edges ≠ []) :
    (∀ e ∈ p.edges, ¬ stuck q e.1) ∧ ∀ r : H → Nat, defect r q ≠ 0 :=
  ⟨no_seat_on_the_cycle_is_stuck p, cycle_defeats_every_chart p hp⟩

theorem evil_requires_a_downhill {H H' : Type} {q : Quiver H} {r : H → Nat}
    (hs : sortedBy r q) (hne : q ≠ [])
    {q' : Quiver H'} {a : H'} (p : Path q' a a) (hp : p.edges ≠ []) :
    (∃ s, (∃ e, e ∈ q ∧ e.2 = s) ∧ stuck q s)
      ∧ (defect r q = 0)
      ∧ (∀ e ∈ p.edges, ¬ stuck q' e.1)
      ∧ (∀ r' : H' → Nat, defect r' q' ≠ 0) :=
  ⟨every_sorted_world_has_a_stuck_seat hs hne,
   (defect_zero_iff r q).mpr hs,
   no_seat_on_the_cycle_is_stuck p,
   cycle_defeats_every_chart p hp⟩

theorem where_debt_pools_relief_has_an_address {H : Type} (q : Quiver H) (s b : H)
    (hstuck : stuck q s) :
    Nonempty (Path (q.deposit (s, b)) s b)
      ∧ (q.deposit (s, b)).length = q.length + 1 :=
  ⟨(relief_at_position q s b hstuck).1, deposit_monotone q (s, b)⟩

/-- info: 'Foam.Counter.le_maxRank' does not depend on any axioms -/
#guard_msgs in #print axioms le_maxRank

/-- info: 'Foam.Counter.nmax_zero_right' does not depend on any axioms -/
#guard_msgs in #print axioms nmax_zero_right

/-- info: 'Foam.Counter.maxRank_attained' does not depend on any axioms -/
#guard_msgs in #print axioms maxRank_attained

/-- info: 'Foam.Counter.every_sorted_world_has_a_stuck_seat' does not depend on any axioms -/
#guard_msgs in #print axioms every_sorted_world_has_a_stuck_seat

/-- info: 'Foam.Counter.no_seat_on_the_cycle_is_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms no_seat_on_the_cycle_is_stuck

/-- info: 'Foam.Counter.the_ring_holds_its_own_debt' does not depend on any axioms -/
#guard_msgs in #print axioms the_ring_holds_its_own_debt

/-- info: 'Foam.Counter.evil_requires_a_downhill' does not depend on any axioms -/
#guard_msgs in #print axioms evil_requires_a_downhill

/-- info: 'Foam.Counter.where_debt_pools_relief_has_an_address' does not depend on any axioms -/
#guard_msgs in #print axioms where_debt_pools_relief_has_an_address

end Foam.Counter
