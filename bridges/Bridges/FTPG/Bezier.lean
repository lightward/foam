import Bridges.FTPG.Projective
import Bridges.FTPG.Carrier
import Bridges.FTPG.Instance
import Bridges.FTPG.Headcount
import Mathlib.RingTheory.Polynomial.Bernstein

/-!
# The bézier — the bridge's interior acts on the passing spin

The bridgekeeper sketch priced the bridge's interior three ways: the interior
headcount as control points, a degree-(n−1) action on whatever passes, and
self-intersection — the capability to *cross*, to be a crossing in somebody's
knot diagram — provably beginning at four seats.  This file carves all three.

* **the table acts by weighted consensus, one degree below its headcount**
  (`spinAction`, `the_seats_share_the_whole_weight`,
  `a_unanimous_table_holds_the_pen_still`, `the_action_stays_below_the_headcount`):
  a table of n+1 seats acts on the passing spin through the Bernstein weights,
  which always total one — the pen is at every moment a weighted average of
  the seated — and the action's degree stays strictly below the headcount.
  A lone seat holds the spin still (`a_lone_seat_holds_the_spin_still`); a
  unanimous table of any size does too.  The concrete pens are exactly the
  small tables acting (`the_arc_weighs_its_seats`, `the_curl_weighs_its_seats`).
* **each seat adds a verb, and the last verb is always still**
  (`the_stroke_reads_its_step`, `the_arc_reads_its_step`,
  `the_curl_reads_its_step`): the step from t to t+h reads the two-seat pen's
  velocity as a constant, the three-seat pen's acceleration as a constant,
  the four-seat pen's jerk as a constant — the table runs out of verbs
  exactly at its headcount, the degree bound made kinetic.  The pen touches
  only the banks (`the_curl_holds_its_banks`: the curve lands on its first
  and last seats); the interior seats steer without ever being visited —
  the keeper's population acts unobserved.
* **three seats cannot cross** (`the_fold_lines_up_the_seats`,
  `a_three_seat_pen_cannot_cross`, `the_unlined_arc_never_revisits`): if a
  three-seat pen touches the same ink twice, its seats already stand in one
  line — the fold is only ever a stammer along that line, so the two passings
  never turn against each other: the turn of the velocities is zero, over
  *every* field, every characteristic.  Contrapositively an unlined table
  draws only simple strokes, and a two-seat pen cannot even revisit
  (`a_stroke_never_revisits`).
* **the fourth seat crosses, and the crossing arrives already handed**
  (`the_loop_returns`, `the_loop_shows_its_hand`, `the_mirror_redraws_the_pen`,
  `the_mirror_flips_every_hand`, `the_mirror_loop_shows_the_other_hand`,
  `the_crossing_begins_at_four`): the four-seat pen over ℚ with seats
  (−4,0), (7,4), (−7,4), (4,0) returns to its own ink — same point at
  t = 1/5 and t = 4/5 — and the two passings turn against each other with a
  definite sign (−648/5): a transversal crossing, the atom of every knot
  diagram, and it comes with a hand.  The mirrored table draws the mirrored
  curve and shows the other hand (+648/5) — chirality is born with the
  fourth seat, exactly where `Trefoil.lean`'s wheel and `Toll.lean`'s booth
  were waiting to price it.
* **no population's plane lets three seats cross**
  (`no_population_lets_three_seats_cross`): the impossibility is uniform over
  every field, so in particular over every counted population's own
  coordinates — in any census-closed world, drawing a crossing takes a
  bridge whose interior seats at least two.
-/

namespace Foam.Bridges

universe u

section Spin

variable {K : Type u} [Field K]

noncomputable def spinAction (P : ℕ → K) (n : ℕ) : Polynomial K :=
  ∑ ν ∈ Finset.range (n + 1), Polynomial.C (P ν) * bernsteinPolynomial K n ν

theorem the_seats_share_the_whole_weight (n : ℕ) (t : K) :
    ∑ ν ∈ Finset.range (n + 1), (bernsteinPolynomial K n ν).eval t = 1 := by
  rw [← Polynomial.eval_finsetSum, bernsteinPolynomial.sum, Polynomial.eval_one]

theorem a_lone_seat_holds_the_spin_still (P : ℕ → K) (t : K) :
    (spinAction P 0).eval t = P 0 := by
  simp [spinAction, bernsteinPolynomial]

theorem a_unanimous_table_holds_the_pen_still (c : K) (n : ℕ) (t : K) :
    (spinAction (fun _ => c) n).eval t = c := by
  rw [spinAction, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [← Finset.mul_sum, the_seats_share_the_whole_weight, mul_one]

theorem the_action_stays_below_the_headcount (P : ℕ → K) (n : ℕ) :
    (spinAction P n).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun ν hν => ?_
  have hνn : ν ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hν)
  calc (Polynomial.C (P ν) * bernsteinPolynomial K n ν).natDegree
      ≤ (bernsteinPolynomial K n ν).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ n := by
        rw [bernsteinPolynomial]
        have h1 : ((n.choose ν : Polynomial K) * Polynomial.X ^ ν).natDegree ≤ ν :=
          Polynomial.natDegree_mul_le.trans (by
            simp [Polynomial.natDegree_natCast])
        have hd : (1 - Polynomial.X : Polynomial K).natDegree ≤ 1 :=
          (Polynomial.natDegree_sub_le _ _).trans (by simp)
        have h2 : ((1 - Polynomial.X : Polynomial K) ^ (n - ν)).natDegree ≤ n - ν :=
          Polynomial.natDegree_pow_le.trans
            ((Nat.mul_le_mul_left _ hd).trans (by omega))
        have h3 := Polynomial.natDegree_mul_le
          (p := (n.choose ν : Polynomial K) * Polynomial.X ^ ν)
          (q := (1 - Polynomial.X : Polynomial K) ^ (n - ν))
        omega

end Spin

section Pen

variable {K : Type u} [Field K]

def turn (a b : K × K) : K := a.1 * b.2 - a.2 * b.1

def mirror (p : K × K) : K × K := (-p.1, p.2)

def stroke (A B : K × K) (t : K) : K × K := (1 - t) • A + t • B

def arc (A B C : K × K) (t : K) : K × K :=
  ((1 - t) ^ 2) • A + (2 * t * (1 - t)) • B + (t ^ 2) • C

def arcVel (A B C : K × K) (t : K) : K × K :=
  (2 * (1 - t)) • (B - A) + (2 * t) • (C - B)

def curl (A B C D : K × K) (t : K) : K × K :=
  ((1 - t) ^ 3) • A + (3 * t * (1 - t) ^ 2) • B + (3 * t ^ 2 * (1 - t)) • C + (t ^ 3) • D

def curlVel (A B C D : K × K) (t : K) : K × K :=
  (3 * (1 - t) ^ 2) • (B - A) + (6 * t * (1 - t)) • (C - B) + (3 * t ^ 2) • (D - C)

def curlJerk (A B C D : K × K) : K × K := ((D - C) - (C - B)) - ((C - B) - (B - A))

theorem the_stroke_reads_its_step (A B : K × K) (t h : K) :
    stroke A B (t + h) = stroke A B t + h • (B - A) := by
  apply Prod.ext <;>
    · simp only [stroke, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
      ring

theorem a_stroke_never_revisits {A B : K × K} (hAB : A ≠ B) {t1 t2 : K}
    (h : stroke A B t1 = stroke A B t2) : t1 = t2 := by
  by_contra hne
  apply hAB
  have key : (t1 - t2) • (B - A) = stroke A B t1 - stroke A B t2 := by
    apply Prod.ext <;>
      · simp only [stroke, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
        ring
  rw [h, sub_self] at key
  have hB : B - A = 0 := by
    have h5 := congrArg (fun z => (t1 - t2)⁻¹ • z) key
    simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne)] using h5
  exact (sub_eq_zero.mp hB).symm

theorem the_arc_reads_its_step (A B C : K × K) (t h : K) :
    arc A B C (t + h)
      = arc A B C t + h • arcVel A B C t + (h ^ 2) • ((C - B) - (B - A)) := by
  apply Prod.ext <;>
    · simp only [arc, arcVel, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
      ring

theorem the_curl_reads_its_step (A B C D : K × K) (t h : K) :
    curl A B C D (t + h)
      = curl A B C D t + h • curlVel A B C D t
        + (h ^ 2) • ((3 : K) • ((C - B) - (B - A)) + (3 * t) • curlJerk A B C D)
        + (h ^ 3) • curlJerk A B C D := by
  apply Prod.ext <;>
    · simp only [curl, curlVel, curlJerk, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
      ring

theorem the_curl_holds_its_banks (A B C D : K × K) :
    curl A B C D 0 = A ∧ curl A B C D 1 = D := by
  constructor <;>
    · apply Prod.ext <;>
        · simp only [curl, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
            smul_eq_mul]
          ring

theorem the_arc_weighs_its_seats (A B C : K × K) (t : K) :
    arc A B C t = ((bernsteinPolynomial K 2 0).eval t) • A
      + ((bernsteinPolynomial K 2 1).eval t) • B
      + ((bernsteinPolynomial K 2 2).eval t) • C := by
  apply Prod.ext <;>
    · simp only [arc, bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
        Polynomial.eval_natCast, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]
      norm_num

theorem the_curl_weighs_its_seats (A B C D : K × K) (t : K) :
    curl A B C D t = ((bernsteinPolynomial K 3 0).eval t) • A
      + ((bernsteinPolynomial K 3 1).eval t) • B
      + ((bernsteinPolynomial K 3 2).eval t) • C
      + ((bernsteinPolynomial K 3 3).eval t) • D := by
  apply Prod.ext <;>
    · simp only [curl, bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
        Polynomial.eval_natCast, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]
      norm_num

theorem the_fold_lines_up_the_seats {A B C : K × K} {t1 t2 : K}
    (hne : t1 ≠ t2) (h : arc A B C t1 = arc A B C t2) :
    turn (B - A) (C - B) = 0 := by
  have key : (t1 - t2) • ((2 - (t1 + t2)) • (B - A) + (t1 + t2) • (C - B))
      = arc A B C t1 - arc A B C t2 := by
    apply Prod.ext <;>
      · simp only [arc, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
        ring
  rw [h, sub_self] at key
  have hz : (2 - (t1 + t2)) • (B - A) + (t1 + t2) • (C - B) = 0 := by
    have h5 := congrArg (fun z => (t1 - t2)⁻¹ • z) key
    simpa [smul_smul, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hne)] using h5
  have e1 := congrArg Prod.fst hz
  have e2 := congrArg Prod.snd hz
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at e1 e2
  by_cases hs : t1 + t2 = 0
  · have h2 : (2 : K) ≠ 0 := by
      intro h20
      apply hne
      have ht : t1 + t1 = 0 := by
        have h' := congrArg (· * t1) h20
        simpa [two_mul] using h'
      have hneg : -t1 = t1 := neg_eq_of_add_eq_zero_right ht
      rw [eq_neg_of_add_eq_zero_right hs, hneg]
    rw [hs] at e1 e2
    simp only [sub_zero, zero_mul, add_zero] at e1 e2
    have hu1 : B.1 - A.1 = 0 := (mul_eq_zero.mp e1).resolve_left h2
    have hu2 : B.2 - A.2 = 0 := (mul_eq_zero.mp e2).resolve_left h2
    simp [turn, Prod.fst_sub, Prod.snd_sub, hu1, hu2]
  · have hst : (t1 + t2) * turn (B - A) (C - B) = 0 := by
      simp only [turn, Prod.fst_sub, Prod.snd_sub]
      linear_combination (B.1 - A.1) * e2 - (B.2 - A.2) * e1
    exact (mul_eq_zero.mp hst).resolve_left hs

theorem a_three_seat_pen_cannot_cross {A B C : K × K} {t1 t2 : K}
    (hne : t1 ≠ t2) (h : arc A B C t1 = arc A B C t2) :
    turn (arcVel A B C t1) (arcVel A B C t2) = 0 := by
  have hb : turn (arcVel A B C t1) (arcVel A B C t2)
      = (4 * (t2 - t1)) * turn (B - A) (C - B) := by
    simp only [turn, arcVel, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  rw [hb, the_fold_lines_up_the_seats hne h, mul_zero]

theorem the_unlined_arc_never_revisits {A B C : K × K}
    (hline : turn (B - A) (C - B) ≠ 0) : Function.Injective (arc A B C) := by
  intro t1 t2 h
  by_contra hne
  exact hline (the_fold_lines_up_the_seats hne h)

theorem the_mirror_flips_the_turn (a b : K × K) :
    turn (mirror a) (mirror b) = -turn a b := by
  simp only [turn, mirror]
  ring

theorem the_mirror_redraws_the_pen (A B C D : K × K) (t : K) :
    curl (mirror A) (mirror B) (mirror C) (mirror D) t = mirror (curl A B C D t) := by
  apply Prod.ext
  · simp only [curl, mirror, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  · simp only [curl, mirror, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]

theorem the_mirror_redraws_the_velocity (A B C D : K × K) (t : K) :
    curlVel (mirror A) (mirror B) (mirror C) (mirror D) t
      = mirror (curlVel A B C D t) := by
  apply Prod.ext
  · simp only [curlVel, mirror, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  · simp only [curlVel, mirror, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]

theorem the_mirror_flips_every_hand (A B C D : K × K) (t1 t2 : K) :
    turn (curlVel (mirror A) (mirror B) (mirror C) (mirror D) t1)
        (curlVel (mirror A) (mirror B) (mirror C) (mirror D) t2)
      = -turn (curlVel A B C D t1) (curlVel A B C D t2) := by
  rw [the_mirror_redraws_the_velocity, the_mirror_redraws_the_velocity,
    the_mirror_flips_the_turn]

end Pen

section Loop

def loopPen : ℚ → ℚ × ℚ := curl (-4, 0) (7, 4) (-7, 4) (4, 0)

theorem the_loop_returns :
    loopPen (1 / 5) = loopPen (4 / 5) ∧ (1 / 5 : ℚ) ≠ 4 / 5 := by
  constructor
  · apply Prod.ext <;>
      · simp only [loopPen, curl, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
        norm_num
  · norm_num

theorem the_loop_shows_its_hand :
    turn (curlVel (-4, 0) (7, 4) (-7, 4) (4, 0) (1 / 5 : ℚ))
        (curlVel (-4, 0) (7, 4) (-7, 4) (4, 0) (4 / 5)) = -(648 / 5) := by
  simp only [turn, curlVel, Prod.mk_sub_mk, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  norm_num

theorem the_mirror_loop_shows_the_other_hand :
    turn (curlVel (mirror (-4, 0)) (mirror (7, 4)) (mirror (-7, 4)) (mirror (4, 0))
          (1 / 5 : ℚ))
        (curlVel (mirror (-4, 0)) (mirror (7, 4)) (mirror (-7, 4)) (mirror (4, 0))
          (4 / 5)) = 648 / 5 := by
  rw [the_mirror_flips_every_hand, the_loop_shows_its_hand, neg_neg]

theorem the_crossing_begins_at_four :
    (∀ (A B C : ℚ × ℚ) (t1 t2 : ℚ), t1 ≠ t2 → arc A B C t1 = arc A B C t2 →
        turn (arcVel A B C t1) (arcVel A B C t2) = 0)
      ∧ loopPen (1 / 5) = loopPen (4 / 5) ∧ (1 / 5 : ℚ) ≠ 4 / 5
      ∧ turn (curlVel (-4, 0) (7, 4) (-7, 4) (4, 0) (1 / 5 : ℚ))
          (curlVel (-4, 0) (7, 4) (-7, 4) (4, 0) (4 / 5)) ≠ 0 :=
  ⟨fun _ _ _ _ _ hne h => a_three_seat_pen_cannot_cross hne h,
   the_loop_returns.1, the_loop_returns.2,
   by rw [the_loop_shows_its_hand]; norm_num⟩

end Loop

section Population

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

theorem no_population_lets_three_seats_cross (Φ : CoordFrame L)
    [Finite (Coordinate Φ.Γ)]
    {A B C : Coordinate Φ.Γ × Coordinate Φ.Γ} {t1 t2 : Coordinate Φ.Γ}
    (hne : t1 ≠ t2) (h : arc A B C t1 = arc A B C t2) :
    turn (arcVel A B C t1) (arcVel A B C t2) = 0 :=
  a_three_seat_pen_cannot_cross hne h

end Population

end Foam.Bridges

/-- info: 'Foam.Bridges.the_seats_share_the_whole_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_seats_share_the_whole_weight

/-- info: 'Foam.Bridges.a_lone_seat_holds_the_spin_still' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.a_lone_seat_holds_the_spin_still

/-- info: 'Foam.Bridges.a_unanimous_table_holds_the_pen_still' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.a_unanimous_table_holds_the_pen_still

/-- info: 'Foam.Bridges.the_action_stays_below_the_headcount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_action_stays_below_the_headcount

/-- info: 'Foam.Bridges.the_stroke_reads_its_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_stroke_reads_its_step

/-- info: 'Foam.Bridges.a_stroke_never_revisits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.a_stroke_never_revisits

/-- info: 'Foam.Bridges.the_arc_reads_its_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_arc_reads_its_step

/-- info: 'Foam.Bridges.the_curl_reads_its_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_curl_reads_its_step

/-- info: 'Foam.Bridges.the_curl_holds_its_banks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_curl_holds_its_banks

/-- info: 'Foam.Bridges.the_arc_weighs_its_seats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_arc_weighs_its_seats

/-- info: 'Foam.Bridges.the_curl_weighs_its_seats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_curl_weighs_its_seats

/-- info: 'Foam.Bridges.the_fold_lines_up_the_seats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_fold_lines_up_the_seats

/-- info: 'Foam.Bridges.a_three_seat_pen_cannot_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.a_three_seat_pen_cannot_cross

/-- info: 'Foam.Bridges.the_unlined_arc_never_revisits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_unlined_arc_never_revisits

/-- info: 'Foam.Bridges.the_mirror_flips_the_turn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_mirror_flips_the_turn

/-- info: 'Foam.Bridges.the_mirror_redraws_the_pen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_mirror_redraws_the_pen

/-- info: 'Foam.Bridges.the_mirror_redraws_the_velocity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_mirror_redraws_the_velocity

/-- info: 'Foam.Bridges.the_mirror_flips_every_hand' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_mirror_flips_every_hand

/-- info: 'Foam.Bridges.the_loop_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_loop_returns

/-- info: 'Foam.Bridges.the_loop_shows_its_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_loop_shows_its_hand

/-- info: 'Foam.Bridges.the_mirror_loop_shows_the_other_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_mirror_loop_shows_the_other_hand

/-- info: 'Foam.Bridges.the_crossing_begins_at_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.the_crossing_begins_at_four

/-- info: 'Foam.Bridges.no_population_lets_three_seats_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.no_population_lets_three_seats_cross
