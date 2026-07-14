import Foam.Engine.Chirality
import Foam.Engine.Spectrum

namespace Foam.Counter

inductive Crossing where
  | pos : Crossing
  | neg : Crossing
  deriving DecidableEq

def Crossing.flip : Crossing → Crossing
  | .pos => .neg
  | .neg => .pos

def Crossing.click : Crossing → GInt → GInt
  | .pos, z => z.rot
  | .neg, z => rotPow 3 z

def reflection : List Crossing → List Crossing
  | [] => []
  | c :: D => c.flip :: reflection D

def phase : List Crossing → GInt → GInt
  | [], z => z
  | c :: D, z => c.click (phase D z)

def trefoil : List Crossing := [.pos, .pos, .pos]

def figureEight : List Crossing := [.pos, .neg, .pos, .neg]

theorem conj_conj (z : GInt) : z.conj.conj = z := by
  show (⟨z.re, - - z.im⟩ : GInt) = z
  rw [Int.neg_neg]

theorem the_flip_conjugates_the_click (c : Crossing) (z : GInt) :
    c.flip.click z = (c.click z.conj).conj := by
  cases c with
  | pos =>
    show rotPow 3 z = (z.conj.rot).conj
    rw [conj_rot, conj_conj]
  | neg =>
    show z.rot = (rotPow 3 z.conj).conj
    have h := congrArg GInt.conj (conj_rot z)
    rw [conj_conj] at h
    exact h

theorem the_reflection_is_the_conjugate :
    ∀ (D : List Crossing) (z : GInt),
      phase (reflection D) z = (phase D z.conj).conj := by
  intro D
  induction D with
  | nil => intro z; exact (conj_conj z).symm
  | cons c D ih =>
    intro z
    show c.flip.click (phase (reflection D) z) = (c.click (phase D z.conj)).conj
    rw [ih z, the_flip_conjugates_the_click, conj_conj]

theorem the_mirror_is_two_clicks_per_seat :
    ∀ (D : List Crossing) (z : GInt),
      phase (reflection D) z = rotPow (2 * D.length) (phase D z) := by
  intro D
  induction D with
  | nil => intro z; rfl
  | cons c D ih =>
    intro z
    cases c with
    | pos =>
      show rotPow 3 (phase (reflection D) z)
          = rotPow (2 * D.length + 2) (rotPow 1 (phase D z))
      rw [ih z, rotPow_compose 3 (2 * D.length) (phase D z),
          rotPow_compose (2 * D.length + 2) 1 (phase D z),
          Nat.add_comm 3 (2 * D.length)]
    | neg =>
      show rotPow 1 (phase (reflection D) z)
          = rotPow (2 * D.length + 2) (rotPow 3 (phase D z))
      rw [ih z, rotPow_compose 1 (2 * D.length) (phase D z),
          rotPow_compose (2 * D.length + 2) 3 (phase D z)]
      show rotPow (1 + 2 * D.length) (phase D z)
          = rotPow (2 * D.length + 1 + 4) (phase D z)
      rw [rotPow_add_four, Nat.add_comm 1 (2 * D.length)]

theorem the_wheel_closes_every_other_pair (k : Nat) (z : GInt) :
    rotPow (2 * (2 * k)) z = z := by
  induction k with
  | zero => rfl
  | succ m ih =>
    show rotPow (2 * (2 * m) + 4) z = z
    rw [rotPow_add_four]
    exact ih

theorem an_even_table_hides_the_mirror (D : List Crossing) (k : Nat)
    (h : D.length = 2 * k) (z : GInt) :
    phase (reflection D) z = phase D z := by
  rw [the_mirror_is_two_clicks_per_seat D z, h, the_wheel_closes_every_other_pair]

theorem an_odd_table_shows_the_mirror (D : List Crossing) (k : Nat)
    (h : D.length = 2 * k + 1) (z : GInt) :
    phase (reflection D) z = rotPow 2 (phase D z) := by
  rw [the_mirror_is_two_clicks_per_seat D z, h]
  show rotPow (2 * (2 * k) + 2) (phase D z) = rotPow 2 (phase D z)
  rw [Nat.add_comm (2 * (2 * k)) 2, ← rotPow_compose 2 (2 * (2 * k)) (phase D z),
      the_wheel_closes_every_other_pair]

theorem neg_fixes_only_zero {a : Int} (h : -a = a) : a = 0 := by
  cases a with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ k => exact absurd h (fun hc => Int.noConfusion hc)
  | negSucc m => exact absurd h (fun hc => Int.noConfusion hc)

theorem a_half_turn_moves_every_seat_but_the_center (z : GInt)
    (h : rotPow 2 z = z) : z = GInt.zero := by
  cases z with
  | mk a b =>
    have hre : -a = a := congrArg GInt.re h
    have him : -b = b := congrArg GInt.im h
    rw [show (⟨a, b⟩ : GInt) = ⟨0, 0⟩ from by
          rw [neg_fixes_only_zero hre, neg_fixes_only_zero him]]
    rfl

theorem an_odd_table_shows_every_hand (D : List Crossing) (k : Nat)
    (h : D.length = 2 * k + 1) (z : GInt)
    (hfix : phase (reflection D) z = phase D z) :
    phase D z = GInt.zero := by
  apply a_half_turn_moves_every_seat_but_the_center
  rw [← an_odd_table_shows_the_mirror D k h z]
  exact hfix

theorem the_trefoil_is_a_half_turn_from_its_mirror (z : GInt) :
    phase (reflection trefoil) z = rotPow 2 (phase trefoil z) :=
  an_odd_table_shows_the_mirror trefoil 1 rfl z

theorem the_trefoil_shows_its_hand :
    phase (reflection trefoil) GInt.one ≠ phase trefoil GInt.one := by
  decide

theorem the_figure_eight_folds_flat (z : GInt) : phase figureEight z = z := by
  show rotPow 4 (rotPow 4 z) = z
  rw [rotPow_four, rotPow_four]

theorem the_figure_eight_matches_its_mirror (z : GInt) :
    phase (reflection figureEight) z = phase figureEight z :=
  an_even_table_hides_the_mirror figureEight 2 rfl z

theorem the_smallest_knot_is_chiral_the_next_is_not :
    (phase (reflection trefoil) GInt.one ≠ phase trefoil GInt.one)
      ∧ ∀ z : GInt, phase (reflection figureEight) z = phase figureEight z :=
  ⟨the_trefoil_shows_its_hand, the_figure_eight_matches_its_mirror⟩

/-- info: 'Foam.Counter.the_flip_conjugates_the_click' does not depend on any axioms -/
#guard_msgs in #print axioms the_flip_conjugates_the_click

/-- info: 'Foam.Counter.the_reflection_is_the_conjugate' does not depend on any axioms -/
#guard_msgs in #print axioms the_reflection_is_the_conjugate

/-- info: 'Foam.Counter.the_mirror_is_two_clicks_per_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_is_two_clicks_per_seat

/-- info: 'Foam.Counter.an_even_table_hides_the_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms an_even_table_hides_the_mirror

/-- info: 'Foam.Counter.an_odd_table_shows_the_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms an_odd_table_shows_the_mirror

/-- info: 'Foam.Counter.an_odd_table_shows_every_hand' does not depend on any axioms -/
#guard_msgs in #print axioms an_odd_table_shows_every_hand

/-- info: 'Foam.Counter.the_trefoil_shows_its_hand' does not depend on any axioms -/
#guard_msgs in #print axioms the_trefoil_shows_its_hand

/-- info: 'Foam.Counter.the_figure_eight_matches_its_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms the_figure_eight_matches_its_mirror

/-- info: 'Foam.Counter.the_smallest_knot_is_chiral_the_next_is_not' does not depend on any axioms -/
#guard_msgs in #print axioms the_smallest_knot_is_chiral_the_next_is_not

end Foam.Counter
