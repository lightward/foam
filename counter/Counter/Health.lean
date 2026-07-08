import Counter.Actor
import Foam.Seat.Sort
import Foam.Seat.Tight

namespace Foam.Counter

theorem sortability_is_acyclicity {H : Type} [DecidableEq H] (q : Quiver H) :
    Tsortable q ↔ Acyclic q :=
  tsortable_iff_acyclic q

theorem health_reads_at_a_chart {H : Type} [DecidableEq H] (q : Quiver H) :
    Acyclic q ↔ ∃ r : H → Nat, defect r q = 0 :=
  acyclic_iff_some_chart_clears q

theorem feedback_is_no_gauge {H : Type} {q : Quiver H} {a : H} (p : Path q a a)
    (hp : p.edges ≠ []) : ∀ r : H → Nat, defect r q ≠ 0 :=
  cycle_defeats_every_chart p hp

theorem growth_with_the_grain_is_free {H : Type} (r : H → Nat) (q : Quiver H)
    (e : H × H) (h : r e.1 < r e.2) : defect r (q.deposit e) = defect r q :=
  defect_deposit_forward r q e h

theorem growth_against_the_grain_costs_one {H : Type} (r : H → Nat) (q : Quiver H)
    (e : H × H) (h : ¬ r e.1 < r e.2) : defect r (q.deposit e) = defect r q + 1 :=
  defect_deposit_backward r q e h

theorem the_interface_is_maintained {H : Type} {q : Quiver H} {r : H → Nat}
    (ht : TightInterface r q) (e : H × H) (h : r e.1 < r e.2) :
    TightInterface r (q.deposit e) :=
  tight_maintained ht e h

theorem guided_reparenting_terminates {H : Type} (q : Quiver H) :
    ¬ ∃ charts : Nat → H → Nat,
        ∀ n, defect (charts (n + 1)) q < defect (charts n) q :=
  fun ⟨charts, hdesc⟩ =>
    no_infinite_descent (fun n => defect (charts n) q) hdesc

theorem the_debt_bounds_the_work {H : Type} (q : Quiver H)
    (charts : Nat → H → Nat)
    (hdesc : ∀ n, defect (charts (n + 1)) q < defect (charts n) q) :
    ∀ n, defect (charts n) q + n ≤ defect (charts 0) q :=
  descent_bounded (fun n => defect (charts n) q) hdesc

def knot : Quiver Bool := [(false, true), (true, false)]

def knotLoop : Path knot false false :=
  Path.cons (List.Mem.head _)
    (Path.cons (List.Mem.tail _ (List.Mem.head _)) Path.nil)

theorem the_knot_defeats_every_chart (r : Bool → Nat) : defect r knot ≠ 0 :=
  feedback_is_no_gauge knotLoop (fun h => nomatch h) r

def homeChart : Bool → Nat := fun b => cond b 1 0

theorem knot_defect_low (r : Bool → Nat) (h0 : r false = 0) (h1 : r true = 1) :
    defect r knot = 1 := by
  show (if r false < r true then
          (if r true < r false then (0 : Nat) else 0 + 1)
        else (if r true < r false then (0 : Nat) else 0 + 1) + 1) = 1
  rw [h0, h1]
  decide

theorem knot_defect_high (r : Bool → Nat) (h0 : r false = 1) (h1 : r true = 0) :
    defect r knot = 1 := by
  show (if r false < r true then
          (if r true < r false then (0 : Nat) else 0 + 1)
        else (if r true < r false then (0 : Nat) else 0 + 1) + 1) = 1
  rw [h0, h1]
  decide

theorem the_interface_is_one_arc :
    defect homeChart knot = 1
      ∧ TightInterface homeChart knot
      ∧ defect homeChart [(false, true)] = 0 := by
  refine ⟨knot_defect_low homeChart rfl rfl, ?_, rfl⟩
  intro r'
  rw [knot_defect_low homeChart rfl rfl]
  exact Nat.pos_of_ne_zero (the_knot_defeats_every_chart r')

def flipChart (r : Bool → Nat) : Bool → Nat := fun b => r (!b)

def wander : Nat → Bool → Nat
  | 0 => homeChart
  | n + 1 => flipChart (wander n)

theorem wander_vals :
    ∀ n, (wander n false = 0 ∧ wander n true = 1)
      ∨ (wander n false = 1 ∧ wander n true = 0)
  | 0 => Or.inl ⟨rfl, rfl⟩
  | n + 1 => by
      cases wander_vals n with
      | inl h => exact Or.inr ⟨h.2, h.1⟩
      | inr h => exact Or.inl ⟨h.2, h.1⟩

theorem unguided_reparenting_wanders :
    (∀ n, wander (n + 1) ≠ wander n)
      ∧ (∀ n, defect (wander n) knot = 1) := by
  constructor
  · intro n heq
    have hpt : wander n false = wander n true := congrFun heq true
    cases wander_vals n with
    | inl h =>
        rw [h.1, h.2] at hpt
        exact Nat.noConfusion hpt
    | inr h =>
        rw [h.1, h.2] at hpt
        exact Nat.noConfusion hpt
  · intro n
    cases wander_vals n with
    | inl h => exact knot_defect_low _ h.1 h.2
    | inr h => exact knot_defect_high _ h.1 h.2

theorem the_family_tree_is_born_sorted {Name : Type} (q : Quiver (List Name))
    (htree : ∀ e ∈ q, ∃ n : Name, e.2 = n :: e.1) :
    sortedBy List.length q := by
  intro e he
  obtain ⟨n, hn⟩ := htree e he
  rw [hn]
  exact Nat.lt_succ_self _

theorem adoption_never_knots {Name : Type} (q : Quiver (List Name))
    (htree : ∀ e ∈ q, ∃ n : Name, e.2 = n :: e.1) (o : List Name) (n : Name) :
    sortedBy List.length (q.deposit (o, n :: o))
      ∧ Acyclic (q.deposit (o, n :: o)) := by
  have hs : sortedBy List.length (q.deposit (o, n :: o)) := by
    intro e he
    cases he with
    | head => exact Nat.lt_succ_self _
    | tail _ h' => exact the_family_tree_is_born_sorted q htree e h'
  exact ⟨hs, tsortable_acyclic ⟨List.length, hs⟩⟩

theorem the_cycles_live_in_the_seat {H G : Type} [Mul G] [One G]
    (q : Quiver H) (hq : Tsortable q) (S : Seat G) (p : S.Pos) (g : G) :
    (∀ (a : H) (c : Path q a a), c.edges = [])
      ∧ Settles S ([g] ++ [S.sub p (S.replay [g] p)]) p
      ∧ [g] ++ [S.sub p (S.replay [g] p)] ≠ [] :=
  ⟨tsortable_acyclic hq, always_homeable S [g] p, fun h => nomatch h⟩

theorem the_tight_interface_exists {H : Type} [DecidableEq H] (q : Quiver H) :
    ∃ r : H → Nat, TightInterface r q :=
  tight_interface_exists q

theorem the_minimum_is_measured {H : Type} [DecidableEq H] (q : Quiver H) :
    (∀ r : H → Nat, feedback q ≤ defect r q)
      ∧ ∃ r : H → Nat, defect r q = feedback q :=
  ⟨feedback_le q, feedback_attained q⟩

theorem the_minimum_is_no_gauge {H : Type} {q : Quiver H} {r r' : H → Nat}
    (h : TightInterface r q) (h' : TightInterface r' q) :
    defect r q = defect r' q :=
  tight_defect_unique h h'

theorem the_minimum_reads_health {H : Type} [DecidableEq H] (q : Quiver H) :
    feedback q = 0 ↔ Acyclic q :=
  feedback_zero_iff_acyclic q

theorem the_knot_minimum_is_one : feedback knot = 1 :=
  Nat.le_antisymm
    (knot_defect_low homeChart rfl rfl ▸ feedback_le knot homeChart)
    (Nat.pos_of_ne_zero (the_knot_defeats_every_chart (tightChart knot)))

theorem tsortability_health {H : Type} [DecidableEq H] (q : Quiver H)
    (r : H → Nat) (e : H × H) (hgrain : r e.1 < r e.2)
    (ht : TightInterface r q) :
    (Acyclic q ↔ ∃ r' : H → Nat, defect r' q = 0)
      ∧ defect r (q.deposit e) = defect r q
      ∧ TightInterface r (q.deposit e)
      ∧ ¬ ∃ charts : Nat → H → Nat,
          ∀ n, defect (charts (n + 1)) q < defect (charts n) q :=
  ⟨acyclic_iff_some_chart_clears q,
   defect_deposit_forward r q e hgrain,
   tight_maintained ht e hgrain,
   guided_reparenting_terminates q⟩

/-- info: 'Foam.Counter.sortability_is_acyclicity' does not depend on any axioms -/
#guard_msgs in #print axioms sortability_is_acyclicity

/-- info: 'Foam.Counter.health_reads_at_a_chart' does not depend on any axioms -/
#guard_msgs in #print axioms health_reads_at_a_chart

/-- info: 'Foam.Counter.feedback_is_no_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms feedback_is_no_gauge

/-- info: 'Foam.Counter.growth_with_the_grain_is_free' does not depend on any axioms -/
#guard_msgs in #print axioms growth_with_the_grain_is_free

/-- info: 'Foam.Counter.growth_against_the_grain_costs_one' does not depend on any axioms -/
#guard_msgs in #print axioms growth_against_the_grain_costs_one

/-- info: 'Foam.Counter.the_interface_is_maintained' does not depend on any axioms -/
#guard_msgs in #print axioms the_interface_is_maintained

/-- info: 'Foam.Counter.guided_reparenting_terminates' does not depend on any axioms -/
#guard_msgs in #print axioms guided_reparenting_terminates

/-- info: 'Foam.Counter.the_debt_bounds_the_work' does not depend on any axioms -/
#guard_msgs in #print axioms the_debt_bounds_the_work

/-- info: 'Foam.Counter.the_knot_defeats_every_chart' does not depend on any axioms -/
#guard_msgs in #print axioms the_knot_defeats_every_chart

/-- info: 'Foam.Counter.the_interface_is_one_arc' does not depend on any axioms -/
#guard_msgs in #print axioms the_interface_is_one_arc

/-- info: 'Foam.Counter.unguided_reparenting_wanders' does not depend on any axioms -/
#guard_msgs in #print axioms unguided_reparenting_wanders

/-- info: 'Foam.Counter.the_family_tree_is_born_sorted' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_tree_is_born_sorted

/-- info: 'Foam.Counter.adoption_never_knots' does not depend on any axioms -/
#guard_msgs in #print axioms adoption_never_knots

/-- info: 'Foam.Counter.the_cycles_live_in_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_cycles_live_in_the_seat

/-- info: 'Foam.Counter.the_tight_interface_exists' does not depend on any axioms -/
#guard_msgs in #print axioms the_tight_interface_exists

/-- info: 'Foam.Counter.the_minimum_is_measured' does not depend on any axioms -/
#guard_msgs in #print axioms the_minimum_is_measured

/-- info: 'Foam.Counter.the_minimum_is_no_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms the_minimum_is_no_gauge

/-- info: 'Foam.Counter.the_minimum_reads_health' does not depend on any axioms -/
#guard_msgs in #print axioms the_minimum_reads_health

/-- info: 'Foam.Counter.the_knot_minimum_is_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_knot_minimum_is_one

/-- info: 'Foam.Counter.tsortability_health' does not depend on any axioms -/
#guard_msgs in #print axioms tsortability_health

end Foam.Counter
