import Counter.Imaginary
import Counter.Third
import Counter.Tempo
import Counter.Mu
import Foam.Seat.Forcing
import Foam.Seat.Triad
import Foam.Seat.Epoch

namespace Foam.Counter

theorem add_sub_add_right_cancel (X Y Z : Int) : (X + Y) - (Z + Y) = X - Z := by
  rw [Int.sub_eq_add_neg, FInt.neg_add, Int.add_swap_inner X Y (-Z) (-Y),
      FInt.add_right_neg Y, Int.add_zero, ← Int.sub_eq_add_neg]

theorem add_sub_add_left_cancel (X Y Z : Int) : (X + Y) - (X + Z) = Y - Z := by
  rw [Int.sub_eq_add_neg, FInt.neg_add, Int.add_swap_inner X Y (-X) (-Z),
      FInt.add_right_neg X, FInt.zero_add, ← Int.sub_eq_add_neg]

theorem quad_pair_re (a b c d e f : Int) :
    (a * f - b * e) * c = f * (a * c + b * d) - b * (e * c + f * d) := by
  rw [FInt.mul_add f (a * c) (b * d), FInt.mul_add b (e * c) (f * d),
      ← FInt.mul_assoc f a c, FInt.mulComm f a,
      ← FInt.mul_assoc f b d,
      ← FInt.mul_assoc b e c,
      ← FInt.mul_assoc b f d, FInt.mulComm b f,
      add_sub_add_right_cancel (a * f * c) (f * b * d) (b * e * c),
      ← FInt.sub_mul]

theorem quad_pair_im (a b c d e f : Int) :
    (a * f - b * e) * d = a * (e * c + f * d) - e * (a * c + b * d) := by
  rw [FInt.mul_add a (e * c) (f * d), FInt.mul_add e (a * c) (b * d),
      ← FInt.mul_assoc a e c,
      ← FInt.mul_assoc e a c, FInt.mulComm e a,
      ← FInt.mul_assoc a f d,
      ← FInt.mul_assoc e b d, FInt.mulComm e b,
      add_sub_add_left_cancel (a * e * c) (a * f * d) (b * e * d),
      ← FInt.sub_mul]

theorem no_shared_quadrature_in_the_plane :
    ∀ (θ₁ θ₂ z : GInt), GInt.align θ₁ z = 0 → GInt.align θ₂ z = 0 →
      z ≠ GInt.zero → GInt.cross θ₁ θ₂ = 0
  | θ₁, θ₂, ⟨c, d⟩, h1, h2, hz => by
    have hre : GInt.cross θ₁ θ₂ * c
        = θ₂.im * GInt.align θ₁ ⟨c, d⟩ - θ₁.im * GInt.align θ₂ ⟨c, d⟩ :=
      quad_pair_re θ₁.re θ₁.im c d θ₂.re θ₂.im
    have him : GInt.cross θ₁ θ₂ * d
        = θ₁.re * GInt.align θ₂ ⟨c, d⟩ - θ₂.re * GInt.align θ₁ ⟨c, d⟩ :=
      quad_pair_im θ₁.re θ₁.im c d θ₂.re θ₂.im
    rw [h1, h2, FInt.mul_zero, FInt.mul_zero, FInt.sub_zero] at hre
    rw [h1, h2, FInt.mul_zero, FInt.mul_zero, FInt.sub_zero] at him
    rcases FInt.mul_eq_zero.mp hre with h | hc0
    · exact h
    · rcases FInt.mul_eq_zero.mp him with h | hd0
      · exact h
      · exact absurd (by subst hc0; subst hd0; rfl) hz

theorem the_shared_i_arrives_from_beyond (n : Nat) :
    Rung.mul (n + 1) (fresh n) (fresh n) = Rung.neg (n + 1) (Rung.one (n + 1))
      ∧ (rungSeam 0).prime (Quat.toRung jay) :=
  ⟨every_rung_issues_i n, jay_prime⟩

theorem the_triad_flows :
    (Quat.mul eye jay = kay ∧ Quat.mul jay kay = eye ∧ Quat.mul kay eye = jay)
      ∧ Quat.mul eye jay ≠ Quat.mul jay eye :=
  ⟨triad_closes, order_arrives⟩

theorem the_marriage_keeps_the_beat (n : Nat) :
    Rung.mul (n + 1) (Rung.mul (n + 1) (fresh n) (fresh n))
        (Rung.mul (n + 1) (fresh n) (fresh n)) = Rung.one (n + 1)
      ∧ Rung.mul (n + 1) (fresh n) (fresh n) ≠ Rung.one (n + 1) :=
  the_bar_is_four_at_every_rung n

theorem the_empty_seat_cannot_drift {Name : Type} (A B : Type) :
    (∀ o : List Name, Below ([] : List Name) o)
      ∧ (∀ e : List Name, (∀ o, Below e o) → e = [])
      ∧ (thirdSeat A B).Covers (pairSeat A B)
      ∧ ¬ (pairSeat Bool Bool).Covers (thirdSeat Bool Bool) :=
  ⟨wind_below_all, only_wind_is_floor, third_covers_the_pair A B,
   pair_blind_to_the_third⟩

theorem the_shared_imaginary_coordinate (θ₁ θ₂ z : GInt)
    (h1 : GInt.align θ₁ z = 0) (h2 : GInt.align θ₂ z = 0)
    (hz : z ≠ GInt.zero) (n : Nat) {Name : Type} (A B : Type) :
    GInt.cross θ₁ θ₂ = 0
      ∧ (Rung.mul (n + 1) (fresh n) (fresh n) = Rung.neg (n + 1) (Rung.one (n + 1))
          ∧ (rungSeam 0).prime (Quat.toRung jay))
      ∧ (Quat.mul eye jay = kay ∧ Quat.mul jay kay = eye ∧ Quat.mul kay eye = jay)
      ∧ ((∀ e : List Name, (∀ o, Below e o) → e = [])
          ∧ (thirdSeat A B).Covers (pairSeat A B)) :=
  ⟨no_shared_quadrature_in_the_plane θ₁ θ₂ z h1 h2 hz,
   the_shared_i_arrives_from_beyond n,
   triad_closes,
   only_wind_is_floor, third_covers_the_pair A B⟩

/-- info: 'Foam.Counter.add_sub_add_right_cancel' does not depend on any axioms -/
#guard_msgs in #print axioms add_sub_add_right_cancel

/-- info: 'Foam.Counter.add_sub_add_left_cancel' does not depend on any axioms -/
#guard_msgs in #print axioms add_sub_add_left_cancel

/-- info: 'Foam.Counter.quad_pair_re' does not depend on any axioms -/
#guard_msgs in #print axioms quad_pair_re

/-- info: 'Foam.Counter.quad_pair_im' does not depend on any axioms -/
#guard_msgs in #print axioms quad_pair_im

/-- info: 'Foam.Counter.no_shared_quadrature_in_the_plane' does not depend on any axioms -/
#guard_msgs in #print axioms no_shared_quadrature_in_the_plane

/-- info: 'Foam.Counter.the_shared_i_arrives_from_beyond' does not depend on any axioms -/
#guard_msgs in #print axioms the_shared_i_arrives_from_beyond

/-- info: 'Foam.Counter.the_triad_flows' does not depend on any axioms -/
#guard_msgs in #print axioms the_triad_flows

/-- info: 'Foam.Counter.the_marriage_keeps_the_beat' does not depend on any axioms -/
#guard_msgs in #print axioms the_marriage_keeps_the_beat

/-- info: 'Foam.Counter.the_empty_seat_cannot_drift' does not depend on any axioms -/
#guard_msgs in #print axioms the_empty_seat_cannot_drift

/-- info: 'Foam.Counter.the_shared_imaginary_coordinate' does not depend on any axioms -/
#guard_msgs in #print axioms the_shared_imaginary_coordinate

end Foam.Counter
