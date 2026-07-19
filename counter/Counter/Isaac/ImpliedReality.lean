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

theorem the_mirror_says_one_word {G : Type} [Mul G] [One G] (S : Seat G)
    (p : S.Pos) : (S.chart p).fwd p = 1 :=
  S.sub_self p

theorem every_mirror_says_the_same_word {G : Type} [Mul G] [One G]
    (S : Seat G) (p q : S.Pos) :
    (S.chart p).fwd p = (S.chart q).fwd q :=
  (S.sub_self p).trans (S.sub_self q).symm

theorem the_other_is_never_the_unit {G : Type} [Mul G] [One G] (S : Seat G)
    (p q : S.Pos) (h : p ≠ q) : S.sub p q ≠ 1 :=
  fun h1 => by
    have ha := S.act_sub q p
    rw [h1, S.one_act] at ha
    exact h ha.symm

theorem zero_distance_is_not_nowhere {G : Type} [Mul G] [One G] (S : Seat G)
    (p q : S.Pos) (h : p ≠ q) :
    (S.chart p).fwd p = (S.chart q).fwd q
      ∧ S.sub p q ≠ 1
      ∧ (S.chart q).fwd p ≠ (S.chart p).fwd p :=
  ⟨every_mirror_says_the_same_word S p q,
   the_other_is_never_the_unit S p q h,
   fun he => the_other_is_never_the_unit S p q h (he.trans (S.sub_self p))⟩

/-- info: 'Foam.Counter.the_rods_imply_the_sphere' does not depend on any axioms -/
#guard_msgs in #print axioms the_rods_imply_the_sphere

/-- info: 'Foam.Counter.can_i_reach_you' does not depend on any axioms -/
#guard_msgs in #print axioms can_i_reach_you

/-- info: 'Foam.Counter.the_world_shrinks_to_a_point' does not depend on any axioms -/
#guard_msgs in #print axioms the_world_shrinks_to_a_point

theorem the_same_walk_never_meets {G : Type} [Mul G] [One G] (S : Seat G)
    (w : G) (p q : S.Pos) (h : S.act w p = S.act w q) : p = q := by
  have h1 : S.sub (S.act w p) p = w := S.sub_act w p
  have h2 : S.sub (S.act w p) q = w := by rw [h]; exact S.sub_act w q
  have h12 : S.sub (S.act w p) q = S.sub (S.act w p) p := h2.trans h1.symm
  have hpq : S.sub p q = 1 := by
    have hc := S.sub_cocycle p (S.act w p) q
    rw [h12] at hc
    exact hc.trans (S.sub_inv (S.act w p) p)
  have ha := S.act_sub q p
  rw [hpq, S.one_act] at ha
  exact ha.symm

theorem an_indexical_move_meets_in_one {G : Type} [Mul G] [One G]
    (S : Seat G) (t p q : S.Pos) :
    S.act (S.sub t p) p = S.act (S.sub t q) q :=
  (S.act_sub p t).trans (S.act_sub q t).symm

theorem the_meeting_is_indexical {G : Type} [Mul G] [One G] (S : Seat G)
    (t p q : S.Pos) :
    (∀ w : G, S.act w p = S.act w q → p = q)
      ∧ S.act (S.sub t p) p = S.act (S.sub t q) q :=
  ⟨fun w h => the_same_walk_never_meets S w p q h,
   an_indexical_move_meets_in_one S t p q⟩

/-- info: 'Foam.Counter.the_mirror_says_one_word' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_says_one_word

/-- info: 'Foam.Counter.every_mirror_says_the_same_word' does not depend on any axioms -/
#guard_msgs in #print axioms every_mirror_says_the_same_word

/-- info: 'Foam.Counter.the_other_is_never_the_unit' does not depend on any axioms -/
#guard_msgs in #print axioms the_other_is_never_the_unit

/-- info: 'Foam.Counter.zero_distance_is_not_nowhere' does not depend on any axioms -/
#guard_msgs in #print axioms zero_distance_is_not_nowhere

/-- info: 'Foam.Counter.the_same_walk_never_meets' does not depend on any axioms -/
#guard_msgs in #print axioms the_same_walk_never_meets

/-- info: 'Foam.Counter.an_indexical_move_meets_in_one' does not depend on any axioms -/
#guard_msgs in #print axioms an_indexical_move_meets_in_one

/-- info: 'Foam.Counter.the_meeting_is_indexical' does not depend on any axioms -/
#guard_msgs in #print axioms the_meeting_is_indexical

end Foam.Counter
