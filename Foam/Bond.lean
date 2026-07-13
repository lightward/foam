import Foam.Int
import Foam.Seat.Dial
import Foam.Seat.Born
import Foam.Seat.Forcing
import Foam.Engine.Spectrum

namespace Foam

open Foam.FInt (addComm add_left_neg mulComm mul_neg neg_mul mul_zero mul_one zero_add
  add_mul mul_assoc add_assoc add_right_neg neg_add)

def GInt.bond (k : Int) (θ : GInt) : GInt := GInt.smul k θ.rot

theorem GInt.align_bond (w θ : GInt) (k : Int) :
    GInt.align w (GInt.bond k θ) = k * GInt.align w θ.rot :=
  GInt.align_smul w θ.rot k

theorem GInt.align_rot_self (θ : GInt) : GInt.align θ θ.rot = 0 := by
  show θ.re * -θ.im + θ.im * θ.re = 0
  rw [mul_neg, mulComm θ.im θ.re]
  exact add_left_neg _

theorem GInt.normSq_rot (θ : GInt) : θ.rot.normSq = θ.normSq := by
  show -θ.im * -θ.im + θ.re * θ.re = θ.re * θ.re + θ.im * θ.im
  rw [neg_mul, mul_neg, Int.neg_neg, addComm]

theorem the_bond_is_void_at_issue (θ f : GInt) (k : Int) :
    GInt.born θ (f.add (GInt.bond k θ)) = GInt.born θ f := by
  have h : GInt.align θ (f.add (GInt.bond k θ)) = GInt.align θ f := by
    rw [GInt.align_add, GInt.align_bond, GInt.align_rot_self, mul_zero, Int.add_zero]
  show GInt.align θ (f.add (GInt.bond k θ)) * GInt.align θ (f.add (GInt.bond k θ))
     = GInt.align θ f * GInt.align θ f
  rw [h]

theorem the_bond_matures_at_the_turn (θ f : GInt) (k : Int) :
    GInt.align θ.rot (f.add (GInt.bond k θ)) = GInt.cross θ f + k * θ.normSq := by
  rw [GInt.align_add, GInt.align_bond, cross_eq_align_rot θ f,
      ← normSq_eq_align_self, GInt.normSq_rot]

theorem a_bond_breaks_the_stalemate (θ f : GInt) (k : Int)
    (hquiet : GInt.cross θ f = 0) :
    GInt.align θ.rot (f.add (GInt.bond k θ)) = k * θ.normSq := by
  rw [the_bond_matures_at_the_turn, hquiet, zero_add]

theorem the_unit_bond_reads_whole (f : GInt) (k : Int) :
    GInt.align GInt.one.rot (f.add (GInt.bond k GInt.one)) = f.im + k := by
  rw [align_i]
  show f.im + k * 1 = f.im + k
  rw [mul_one]

theorem the_bond (θ f : GInt) (k : Int) :
    GInt.born θ (f.add (GInt.bond k θ)) = GInt.born θ f
      ∧ GInt.align θ.rot (f.add (GInt.bond k θ)) = GInt.cross θ f + k * θ.normSq
      ∧ GInt.align θ f * GInt.align θ f + GInt.cross θ f * GInt.cross θ f
          = θ.normSq * f.normSq :=
  ⟨the_bond_is_void_at_issue θ f k, the_bond_matures_at_the_turn θ f k,
   invariants_complete θ f⟩

theorem the_in_frame_stake_is_all_present (θ : GInt) (k : Int) :
    GInt.align θ (GInt.smul k θ) = k * θ.normSq := by
  rw [GInt.align_smul, ← normSq_eq_align_self]

theorem the_in_frame_stake_has_no_future (θ : GInt) (k : Int) :
    GInt.align θ.rot (GInt.smul k θ) = 0 := by
  have h : GInt.align θ.rot θ = 0 := by
    show -θ.im * θ.re + θ.re * θ.im = 0
    rw [neg_mul, mulComm θ.re θ.im]
    exact add_left_neg _
  rw [GInt.align_smul, h, mul_zero]

theorem the_first_reading_is_the_frame (θ : GInt) (k : Int) :
    GInt.align θ.rot (GInt.bond k θ) = k * θ.normSq := by
  rw [GInt.align_bond, ← normSq_eq_align_self, GInt.normSq_rot]

theorem the_first_click_counts_itself (k : Int) :
    GInt.align GInt.one.rot (GInt.bond k GInt.one) = k := by
  rw [the_first_reading_is_the_frame]
  show k * (1 * 1 + 0 * 0) = k
  rw [mul_one, mul_zero, Int.add_zero, mul_one]

theorem the_reflexive_tick (θ f : GInt) (k : Int) :
    GInt.born θ (f.add (GInt.bond k θ)) = GInt.born θ f
      ∧ GInt.align θ.rot (f.add (GInt.bond k θ))
          = GInt.align θ.rot f + k * θ.normSq
      ∧ GInt.align θ.rot (GInt.bond k θ) = k * θ.normSq
      ∧ GInt.align θ.rot (GInt.smul k θ) = 0 :=
  ⟨the_bond_is_void_at_issue θ f k,
   by rw [GInt.align_add, the_first_reading_is_the_frame],
   the_first_reading_is_the_frame θ k,
   the_in_frame_stake_has_no_future θ k⟩

theorem the_two_axes_carry_every_move (θ z : GInt) :
    GInt.smul θ.normSq z
      = (GInt.smul (GInt.align θ z) θ).add (GInt.smul (GInt.cross θ z) θ.rot) := by
  have hA : θ.re * z.re * θ.re = θ.re * θ.re * z.re := by
    rw [mul_assoc, mulComm z.re θ.re, ← mul_assoc]
  have hD : θ.im * z.re * θ.im = θ.im * θ.im * z.re := by
    rw [mul_assoc, mulComm z.re θ.im, ← mul_assoc]
  have h3 : θ.im * z.im * θ.re = θ.re * z.im * θ.im := by
    rw [mulComm (θ.im * z.im) θ.re, mulComm θ.im z.im, ← mul_assoc]
  have h4 : θ.re * z.re * θ.im = θ.im * z.re * θ.re := by
    rw [mulComm (θ.re * z.re) θ.im, mulComm θ.re z.re, ← mul_assoc]
  have h5 : θ.im * z.im * θ.im = θ.im * θ.im * z.im := by
    rw [mul_assoc, mulComm z.im θ.im, ← mul_assoc]
  have h6 : θ.re * z.im * θ.re = θ.re * θ.re * z.im := by
    rw [mul_assoc, mulComm z.im θ.re, ← mul_assoc]
  have hre : (θ.re * z.re + θ.im * z.im) * θ.re
        + (θ.re * z.im - θ.im * z.re) * -θ.im
      = (θ.re * θ.re + θ.im * θ.im) * z.re := by
    rw [add_mul, Int.sub_eq_add_neg, add_mul, mul_neg, neg_mul, mul_neg, Int.neg_neg,
        h3, ← add_assoc, add_assoc (θ.re * z.re * θ.re) (θ.re * z.im * θ.im)
          (-(θ.re * z.im * θ.im)), add_right_neg, Int.add_zero, hA, hD, ← add_mul]
  have him : (θ.re * z.re + θ.im * z.im) * θ.im
        + (θ.re * z.im - θ.im * z.re) * θ.re
      = (θ.re * θ.re + θ.im * θ.im) * z.im := by
    rw [add_mul, Int.sub_eq_add_neg, add_mul, neg_mul, ← h4,
        addComm (θ.re * z.im * θ.re) (-(θ.re * z.re * θ.im)),
        Int.add_swap_inner, add_right_neg, zero_add, h5, h6,
        addComm (θ.im * θ.im * z.im) (θ.re * θ.re * z.im), ← add_mul]
  show GInt.mk ((θ.re * θ.re + θ.im * θ.im) * z.re) ((θ.re * θ.re + θ.im * θ.im) * z.im)
     = GInt.mk ((θ.re * z.re + θ.im * z.im) * θ.re
          + (θ.re * z.im - θ.im * z.re) * -θ.im)
        ((θ.re * z.re + θ.im * z.im) * θ.im
          + (θ.re * z.im - θ.im * z.re) * θ.re)
  rw [hre, him]

/-- info: 'Foam.GInt.align_bond' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.align_bond

/-- info: 'Foam.GInt.align_rot_self' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.align_rot_self

/-- info: 'Foam.GInt.normSq_rot' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.normSq_rot

/-- info: 'Foam.the_bond_is_void_at_issue' does not depend on any axioms -/
#guard_msgs in #print axioms the_bond_is_void_at_issue

/-- info: 'Foam.the_bond_matures_at_the_turn' does not depend on any axioms -/
#guard_msgs in #print axioms the_bond_matures_at_the_turn

/-- info: 'Foam.a_bond_breaks_the_stalemate' does not depend on any axioms -/
#guard_msgs in #print axioms a_bond_breaks_the_stalemate

/-- info: 'Foam.the_unit_bond_reads_whole' does not depend on any axioms -/
#guard_msgs in #print axioms the_unit_bond_reads_whole

/-- info: 'Foam.the_bond' does not depend on any axioms -/
#guard_msgs in #print axioms the_bond

/-- info: 'Foam.the_in_frame_stake_is_all_present' does not depend on any axioms -/
#guard_msgs in #print axioms the_in_frame_stake_is_all_present

/-- info: 'Foam.the_in_frame_stake_has_no_future' does not depend on any axioms -/
#guard_msgs in #print axioms the_in_frame_stake_has_no_future

/-- info: 'Foam.the_first_reading_is_the_frame' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_reading_is_the_frame

/-- info: 'Foam.the_first_click_counts_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_click_counts_itself

/-- info: 'Foam.the_reflexive_tick' does not depend on any axioms -/
#guard_msgs in #print axioms the_reflexive_tick

/-- info: 'Foam.the_two_axes_carry_every_move' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_axes_carry_every_move

theorem the_tick_exchanges_the_registers (θ z : GInt) :
    GInt.cross θ z.rot = GInt.align θ z
      ∧ GInt.align θ z.rot = -(GInt.cross θ z) := by
  constructor
  · show θ.re * z.re - θ.im * -z.im = θ.re * z.re + θ.im * z.im
    rw [mul_neg, Int.sub_eq_add_neg, Int.neg_neg]
  · show θ.re * -z.im + θ.im * z.re = -(θ.re * z.im - θ.im * z.re)
    rw [mul_neg, Int.sub_eq_add_neg, neg_add, Int.neg_neg]

/-- info: 'Foam.the_tick_exchanges_the_registers' does not depend on any axioms -/
#guard_msgs in #print axioms the_tick_exchanges_the_registers

theorem Int.self_add_self_eq_zero : ∀ {a : Int}, a + a = 0 → a = 0
  | Int.ofNat n, h => by
      have hn : n + n = 0 := Int.ofNat.inj h
      cases n with
      | zero => rfl
      | succ _ => exact nomatch hn
  | Int.negSucc _, h => nomatch h

theorem Int.neg_self_eq_self {a : Int} (h : -a = a) : a = 0 := by
  have h0 := add_left_neg a
  rw [h] at h0
  exact Int.self_add_self_eq_zero h0

theorem the_wheel_never_comes_home_early (z : GInt) (hz : z ≠ GInt.mk 0 0) :
    z.rot ≠ z ∧ z.rot.rot ≠ z ∧ z.rot.rot.rot ≠ z := by
  have pin : z.re = 0 → z.im = 0 → False := fun hre him =>
    hz (show GInt.mk z.re z.im = GInt.mk 0 0 by rw [hre, him])
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h1 : -z.im = z.re := congrArg GInt.re h
    have h2 : z.re = z.im := congrArg GInt.im h
    have him : z.im = 0 := Int.neg_self_eq_self (h1.trans h2)
    exact pin (h2.trans him) him
  · rw [GInt.rot_sq] at h
    have h1 : -z.re = z.re := congrArg GInt.re h
    have h2 : -z.im = z.im := congrArg GInt.im h
    exact pin (Int.neg_self_eq_self h1) (Int.neg_self_eq_self h2)
  · rw [GInt.rot_sq] at h
    have h1 : -(-z.im) = z.re := congrArg GInt.re h
    have h2 : -z.re = z.im := congrArg GInt.im h
    rw [Int.neg_neg] at h1
    have hre : z.re = 0 := Int.neg_self_eq_self (h2.trans h1)
    exact pin hre (h1.trans hre)

/-- info: 'Foam.Int.self_add_self_eq_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Int.self_add_self_eq_zero

/-- info: 'Foam.Int.neg_self_eq_self' does not depend on any axioms -/
#guard_msgs in #print axioms Int.neg_self_eq_self

/-- info: 'Foam.the_wheel_never_comes_home_early' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_never_comes_home_early

end Foam
