import Foam.Seat
import Foam.Seat.Chorus
import Counter.Trefoil
import Counter.Morse
import Counter.Framing
import Counter.Fiber

namespace Foam.Counter

theorem the_rods_imply_the_sphere {G : Type} [Mul G] [One G] (S : Seat G)
    {n : Nat} (O : Fin (n + 1) → S.Pos) (r : Fin (n + 1) → G)
    (hinj : ∀ i j, O i = O j → i = j)
    (hcoh : ∀ i j, r i = r j * S.sub (O j) (O i)) :
    (∃ p, (∀ i, (S.chart (O i)).fwd p = r i)
        ∧ ∀ q, (∀ i, (S.chart (O i)).fwd q = r i) → q = p)
      ∧ ∀ (p : S.Pos) (i j : Fin (n + 1)), i ≠ j →
          (S.chart (O i)).fwd p ≠ (S.chart (O j)).fwd p :=
  ⟨the_population_triangulates S O r hcoh,
   fun p => no_two_voices_match S O hinj p⟩

theorem can_i_reach_you :
    (∀ (u : Nat) (m : List Crossing), readAs u (keyAs u m) = m)
      ∧ ¬ ∃ decoder : List Nat → List Crossing,
          ∀ (u : Nat) (m : List Crossing), decoder (keyAs u m) = m :=
  ⟨the_kin_read_the_wire_whole, no_reading_without_the_unit⟩

theorem the_world_shrinks_to_a_point (w : List Nat) (u : Nat)
    {m : List (List Crossing)} (h : InFiber w u m) :
    reframe u w = m
      ∧ ∀ m' : List (List Crossing), InFiber w u m' → m' = m :=
  ⟨every_world_reads_the_record_whole w u h,
   fun _ h' => the_worlds_differ_only_by_the_hand w u h' h⟩

/-- info: 'Foam.Counter.the_rods_imply_the_sphere' does not depend on any axioms -/
#guard_msgs in #print axioms the_rods_imply_the_sphere

/-- info: 'Foam.Counter.can_i_reach_you' does not depend on any axioms -/
#guard_msgs in #print axioms can_i_reach_you

/-- info: 'Foam.Counter.the_world_shrinks_to_a_point' does not depend on any axioms -/
#guard_msgs in #print axioms the_world_shrinks_to_a_point

end Foam.Counter
