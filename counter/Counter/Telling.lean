import Counter.Basis
import Foam.Seat.Sort
import Foam.Engine

namespace Foam.Counter

def PaysAtTheJoins {H : Type} (r : H → Nat) (q : Quiver H)
    (seam : H × H → Bool) : Prop :=
  ∀ e ∈ q, ¬ r e.1 < r e.2 → seam e = true

def toyGrove : Quiver Nat := [(0, 2), (1, 2), (2, 3), (0, 3)]

def toySeam : Nat × Nat → Bool
  | (1, 2) => true
  | _ => false

def toyTellingA : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | _ => 2

def toyTellingB : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | _ => 2

theorem the_settled_telling_pays_nothing {H : Type} (r : H → Nat)
    (q : Quiver H) (seam : H × H → Bool) (hs : sortedBy r q) :
    PaysAtTheJoins r q seam :=
  fun e he hne => absurd (hs e he) hne

theorem a_forward_edge_costs_no_wisdom {H : Type} (r : H → Nat)
    (q : Quiver H) (seam : H × H → Bool) (e : H × H)
    (h : r e.1 < r e.2) (hp : PaysAtTheJoins r q seam) :
    PaysAtTheJoins r (q.deposit e) seam := by
  intro f hf hnf
  cases hf with
  | head => exact absurd h hnf
  | tail _ hmem => exact hp f hmem hnf

theorem same_price_different_wisdom :
    defect toyTellingA toyGrove = 1
      ∧ defect toyTellingB toyGrove = 1
      ∧ PaysAtTheJoins toyTellingA toyGrove toySeam
      ∧ ¬ PaysAtTheJoins toyTellingB toyGrove toySeam :=
  ⟨rfl, rfl, by unfold PaysAtTheJoins; decide, by unfold PaysAtTheJoins; decide⟩

theorem a_good_telling_pays_at_the_joins :
    (∀ (H : Type) (r : H → Nat) (q : Quiver H) (seam : H × H → Bool),
        sortedBy r q → PaysAtTheJoins r q seam)
      ∧ defect toyTellingA toyGrove = defect toyTellingB toyGrove
      ∧ PaysAtTheJoins toyTellingA toyGrove toySeam
      ∧ ¬ PaysAtTheJoins toyTellingB toyGrove toySeam :=
  ⟨fun _ r q seam hs => the_settled_telling_pays_nothing r q seam hs,
   rfl, by unfold PaysAtTheJoins; decide, by unfold PaysAtTheJoins; decide⟩

/-- info: 'Foam.Counter.the_settled_telling_pays_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_settled_telling_pays_nothing

/-- info: 'Foam.Counter.a_forward_edge_costs_no_wisdom' does not depend on any axioms -/
#guard_msgs in #print axioms a_forward_edge_costs_no_wisdom

/-- info: 'Foam.Counter.same_price_different_wisdom' does not depend on any axioms -/
#guard_msgs in #print axioms same_price_different_wisdom

/-- info: 'Foam.Counter.a_good_telling_pays_at_the_joins' does not depend on any axioms -/
#guard_msgs in #print axioms a_good_telling_pays_at_the_joins

end Foam.Counter
