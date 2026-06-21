import Foam.Seat.Dial
import Foam.Seat.Doubling
import Foam.Seat.Born

namespace Foam

def Char.count : Rot → GInt
  | _ => ⟨1, 0⟩

def Char.alt : Rot → GInt
  | .r0 => ⟨1, 0⟩
  | .r1 => ⟨-1, 0⟩
  | .r2 => ⟨1, 0⟩
  | .r3 => ⟨-1, 0⟩

def Char.chi : Rot → GInt := Rot.amp

def Char.chiBar : Rot → GInt := fun a => GInt.conj (Rot.amp a)

theorem Char.count_hom (a b : Rot) :
    Char.count (a * b) = GInt.mul (Char.count a) (Char.count b) := by
  cases a <;> cases b <;> decide

theorem Char.alt_hom (a b : Rot) :
    Char.alt (a * b) = GInt.mul (Char.alt a) (Char.alt b) := by
  cases a <;> cases b <;> decide

theorem Char.chi_hom (a b : Rot) :
    Char.chi (a * b) = GInt.mul (Char.chi a) (Char.chi b) := by
  cases a <;> cases b <;> decide

theorem Char.chiBar_hom (a b : Rot) :
    Char.chiBar (a * b) = GInt.mul (Char.chiBar a) (Char.chiBar b) := by
  cases a <;> cases b <;> decide

theorem Char.count_unit (a : Rot) : (Char.count a).normSq = 1 := by
  cases a <;> decide

theorem Char.alt_unit (a : Rot) : (Char.alt a).normSq = 1 := by
  cases a <;> decide

theorem Char.chi_unit (a : Rot) : (Char.chi a).normSq = 1 := by
  cases a <;> decide

theorem Char.chiBar_unit (a : Rot) : (Char.chiBar a).normSq = 1 := by
  cases a <;> decide

def Char.inner (f g : Rot → GInt) : GInt :=
  GInt.add
    (GInt.add (GInt.mul (f .r0) (GInt.conj (g .r0))) (GInt.mul (f .r1) (GInt.conj (g .r1))))
    (GInt.add (GInt.mul (f .r2) (GInt.conj (g .r2))) (GInt.mul (f .r3) (GInt.conj (g .r3))))

theorem Char.count_norm : Char.inner Char.count Char.count = ⟨4, 0⟩ := by decide
theorem Char.alt_norm : Char.inner Char.alt Char.alt = ⟨4, 0⟩ := by decide
theorem Char.chi_norm : Char.inner Char.chi Char.chi = ⟨4, 0⟩ := by decide
theorem Char.chiBar_norm : Char.inner Char.chiBar Char.chiBar = ⟨4, 0⟩ := by decide

theorem Char.count_alt_orth : Char.inner Char.count Char.alt = GInt.zero := by decide
theorem Char.count_chi_orth : Char.inner Char.count Char.chi = GInt.zero := by decide
theorem Char.count_chiBar_orth : Char.inner Char.count Char.chiBar = GInt.zero := by decide
theorem Char.alt_chi_orth : Char.inner Char.alt Char.chi = GInt.zero := by decide
theorem Char.alt_chiBar_orth : Char.inner Char.alt Char.chiBar = GInt.zero := by decide
theorem Char.chi_chiBar_orth : Char.inner Char.chi Char.chiBar = GInt.zero := by decide

theorem Char.chi_distinct_chiBar : Char.chi ≠ Char.chiBar := by
  intro h
  have : Char.chi .r1 = Char.chiBar .r1 := by rw [h]
  exact absurd this (by decide)

theorem Char.alt_distinct_count : Char.alt ≠ Char.count := by
  intro h
  have : Char.alt .r1 = Char.count .r1 := by rw [h]
  exact absurd this (by decide)

def Char.fold (n0 n1 n2 n3 : Int) (f : Rot → GInt) : GInt :=
  GInt.add
    (GInt.add (GInt.mul ⟨n0, 0⟩ (f .r0)) (GInt.mul ⟨n1, 0⟩ (f .r1)))
    (GInt.add (GInt.mul ⟨n2, 0⟩ (f .r2)) (GInt.mul ⟨n3, 0⟩ (f .r3)))

def Char.readBal (n0 n1 n2 n3 : Int) : Int := (Char.fold n0 n1 n2 n3 Char.count).re
def Char.readAlt (n0 n1 n2 n3 : Int) : Int := (Char.fold n0 n1 n2 n3 Char.alt).re
def Char.readRe (n0 n1 n2 n3 : Int) : Int := (Char.fold n0 n1 n2 n3 Char.chi).re
def Char.readIm (n0 n1 n2 n3 : Int) : Int := (Char.fold n0 n1 n2 n3 Char.chi).im

theorem GInt.mulReal (n : Int) (w : GInt) :
    GInt.mul ⟨n, 0⟩ w = ⟨n * w.re, n * w.im⟩ := by
  show (GInt.mk (n * w.re - 0 * w.im) (n * w.im + 0 * w.re)) = ⟨n * w.re, n * w.im⟩
  rw [Int.zero_mul, Int.sub_zero, Int.zero_mul, Int.add_zero]

theorem Char.fold_re_components (n0 n1 n2 n3 : Int) (f : Rot → GInt) :
    (Char.fold n0 n1 n2 n3 f).re
      = (n0 * (f .r0).re + n1 * (f .r1).re) + (n2 * (f .r2).re + n3 * (f .r3).re) := by
  show ((GInt.mul ⟨n0, 0⟩ (f .r0)).re + (GInt.mul ⟨n1, 0⟩ (f .r1)).re)
       + ((GInt.mul ⟨n2, 0⟩ (f .r2)).re + (GInt.mul ⟨n3, 0⟩ (f .r3)).re)
     = (n0 * (f .r0).re + n1 * (f .r1).re) + (n2 * (f .r2).re + n3 * (f .r3).re)
  rw [GInt.mulReal, GInt.mulReal, GInt.mulReal, GInt.mulReal]

theorem Char.fold_im_components (n0 n1 n2 n3 : Int) (f : Rot → GInt) :
    (Char.fold n0 n1 n2 n3 f).im
      = (n0 * (f .r0).im + n1 * (f .r1).im) + (n2 * (f .r2).im + n3 * (f .r3).im) := by
  show ((GInt.mul ⟨n0, 0⟩ (f .r0)).im + (GInt.mul ⟨n1, 0⟩ (f .r1)).im)
       + ((GInt.mul ⟨n2, 0⟩ (f .r2)).im + (GInt.mul ⟨n3, 0⟩ (f .r3)).im)
     = (n0 * (f .r0).im + n1 * (f .r1).im) + (n2 * (f .r2).im + n3 * (f .r3).im)
  rw [GInt.mulReal, GInt.mulReal, GInt.mulReal, GInt.mulReal]

theorem Char.readBal_eq (n0 n1 n2 n3 : Int) :
    Char.readBal n0 n1 n2 n3 = n0 + n1 + n2 + n3 := by
  show (Char.fold n0 n1 n2 n3 Char.count).re = n0 + n1 + n2 + n3
  rw [Char.fold_re_components]
  show (n0 * 1 + n1 * 1) + (n2 * 1 + n3 * 1) = n0 + n1 + n2 + n3
  rw [Int.mul_one, Int.mul_one, Int.mul_one, Int.mul_one,
    ← Int.add_assoc (n0 + n1) n2 n3]

theorem Char.readAlt_eq (n0 n1 n2 n3 : Int) :
    Char.readAlt n0 n1 n2 n3 = n0 + -n1 + n2 + -n3 := by
  show (Char.fold n0 n1 n2 n3 Char.alt).re = n0 + -n1 + n2 + -n3
  rw [Char.fold_re_components]
  show (n0 * 1 + n1 * (-1)) + (n2 * 1 + n3 * (-1)) = n0 + -n1 + n2 + -n3
  rw [Int.mul_one, Int.mul_neg_one, Int.mul_one, Int.mul_neg_one,
    ← Int.add_assoc (n0 + -n1) n2 (-n3)]

theorem Char.readRe_eq (n0 n1 n2 n3 : Int) :
    Char.readRe n0 n1 n2 n3 = n0 + -n2 := by
  show (Char.fold n0 n1 n2 n3 Char.chi).re = n0 + -n2
  rw [Char.fold_re_components]
  show (n0 * 1 + n1 * 0) + (n2 * (-1) + n3 * 0) = n0 + -n2
  rw [Int.mul_one, Int.mul_zero, Int.add_zero, Int.mul_neg_one, Int.mul_zero, Int.add_zero]

theorem Char.readIm_eq (n0 n1 n2 n3 : Int) :
    Char.readIm n0 n1 n2 n3 = n1 + -n3 := by
  show (Char.fold n0 n1 n2 n3 Char.chi).im = n1 + -n3
  rw [Char.fold_im_components]
  show (n0 * 0 + n1 * 1) + (n2 * 0 + n3 * (-1)) = n1 + -n3
  rw [Int.mul_zero, Int.mul_one, Int.zero_add, Int.mul_zero, Int.mul_neg_one, Int.zero_add]

def Char.twice (a : Int) : Int := a + a

theorem Char.four_swap (a b c d : Int) : a + b + c + d = (a + c) + (b + d) := by
  rw [Int.add_assoc (a + b) c d, Int.add_assoc a b (c + d),
    ← Int.add_assoc b c d, Int.add_comm b c, Int.add_assoc c b d,
    ← Int.add_assoc a c (b + d)]

theorem Char.sub_pair (a b c d : Int) : a + -b + c + -d = (a + c) + -(b + d) := by
  rw [Char.four_swap a (-b) c (-d), ← Int.neg_add]

theorem Char.sum_diff (x y : Int) : (x + y) + (x + -y) = Char.twice x := by
  rw [← Int.add_assoc (x + y) x (-y), Char.four_swap x y x (-y),
    Int.add_right_neg y, Int.add_zero]
  rfl

theorem Char.diff_sum (x y : Int) : (x + y) + -(x + -y) = Char.twice y := by
  rw [Int.neg_add, Int.neg_neg y, ← Int.add_assoc (x + y) (-x) y,
    Char.four_swap x y (-x) y, Int.add_right_neg x, Int.zero_add]
  rfl

theorem Char.twice_add (a b : Int) : Char.twice (a + b) = Char.twice a + Char.twice b := by
  show (a + b) + (a + b) = (a + a) + (b + b)
  rw [← Int.add_assoc (a + b) a b, Char.four_swap a b a b]

theorem Char.twice_sub (a b : Int) : Char.twice (a + -b) = Char.twice a + -Char.twice b := by
  show (a + -b) + (a + -b) = (a + a) + -(b + b)
  rw [← Int.add_assoc (a + -b) a (-b), Char.four_swap a (-b) a (-b), Int.neg_add]

theorem Char.bal_add_alt (n0 n1 n2 n3 : Int) :
    Char.readBal n0 n1 n2 n3 + Char.readAlt n0 n1 n2 n3 = Char.twice (n0 + n2) := by
  rw [Char.readBal_eq, Char.readAlt_eq, Char.four_swap n0 n1 n2 n3,
    Char.sub_pair n0 n1 n2 n3, Char.sum_diff (n0 + n2) (n1 + n3)]

theorem Char.bal_sub_alt (n0 n1 n2 n3 : Int) :
    Char.readBal n0 n1 n2 n3 + -Char.readAlt n0 n1 n2 n3 = Char.twice (n1 + n3) := by
  rw [Char.readBal_eq, Char.readAlt_eq, Char.four_swap n0 n1 n2 n3,
    Char.sub_pair n0 n1 n2 n3, Char.diff_sum (n0 + n2) (n1 + n3)]

theorem Char.recover_bin0 (n0 n1 n2 n3 : Int) :
    (Char.readBal n0 n1 n2 n3 + Char.readAlt n0 n1 n2 n3)
      + Char.twice (Char.readRe n0 n1 n2 n3) = Char.twice (Char.twice n0) := by
  rw [Char.bal_add_alt, Char.readRe_eq, ← Char.twice_add (n0 + n2) (n0 + -n2),
    Char.sum_diff n0 n2]

theorem Char.recover_bin2 (n0 n1 n2 n3 : Int) :
    (Char.readBal n0 n1 n2 n3 + Char.readAlt n0 n1 n2 n3)
      + -Char.twice (Char.readRe n0 n1 n2 n3) = Char.twice (Char.twice n2) := by
  rw [Char.bal_add_alt, Char.readRe_eq, ← Char.twice_sub (n0 + n2) (n0 + -n2),
    Char.diff_sum n0 n2]

theorem Char.recover_bin1 (n0 n1 n2 n3 : Int) :
    (Char.readBal n0 n1 n2 n3 + -Char.readAlt n0 n1 n2 n3)
      + Char.twice (Char.readIm n0 n1 n2 n3) = Char.twice (Char.twice n1) := by
  rw [Char.bal_sub_alt, Char.readIm_eq, ← Char.twice_add (n1 + n3) (n1 + -n3),
    Char.sum_diff n1 n3]

theorem Char.recover_bin3 (n0 n1 n2 n3 : Int) :
    (Char.readBal n0 n1 n2 n3 + -Char.readAlt n0 n1 n2 n3)
      + -Char.twice (Char.readIm n0 n1 n2 n3) = Char.twice (Char.twice n3) := by
  rw [Char.bal_sub_alt, Char.readIm_eq, ← Char.twice_sub (n1 + n3) (n1 + -n3),
    Char.diff_sum n1 n3]

theorem Char.lossless (n0 n1 n2 n3 : Int) :
    (Char.readBal n0 n1 n2 n3 + Char.readAlt n0 n1 n2 n3)
        + Char.twice (Char.readRe n0 n1 n2 n3) = Char.twice (Char.twice n0) ∧
    (Char.readBal n0 n1 n2 n3 + -Char.readAlt n0 n1 n2 n3)
        + Char.twice (Char.readIm n0 n1 n2 n3) = Char.twice (Char.twice n1) ∧
    (Char.readBal n0 n1 n2 n3 + Char.readAlt n0 n1 n2 n3)
        + -Char.twice (Char.readRe n0 n1 n2 n3) = Char.twice (Char.twice n2) ∧
    (Char.readBal n0 n1 n2 n3 + -Char.readAlt n0 n1 n2 n3)
        + -Char.twice (Char.readIm n0 n1 n2 n3) = Char.twice (Char.twice n3) :=
  ⟨Char.recover_bin0 n0 n1 n2 n3, Char.recover_bin1 n0 n1 n2 n3,
    Char.recover_bin2 n0 n1 n2 n3, Char.recover_bin3 n0 n1 n2 n3⟩

theorem Char.bal_irreplaceable :
    Char.readRe 1 1 1 1 = Char.readRe 0 0 0 0 ∧
    Char.readIm 1 1 1 1 = Char.readIm 0 0 0 0 ∧
    Char.readAlt 1 1 1 1 = Char.readAlt 0 0 0 0 ∧
    Char.readBal 1 1 1 1 ≠ Char.readBal 0 0 0 0 := by decide

theorem Char.re_irreplaceable :
    Char.readBal 1 0 0 0 = Char.readBal 0 0 1 0 ∧
    Char.readIm 1 0 0 0 = Char.readIm 0 0 1 0 ∧
    Char.readAlt 1 0 0 0 = Char.readAlt 0 0 1 0 ∧
    Char.readRe 1 0 0 0 ≠ Char.readRe 0 0 1 0 := by decide

theorem Char.im_irreplaceable :
    Char.readBal 0 1 0 0 = Char.readBal 0 0 0 1 ∧
    Char.readRe 0 1 0 0 = Char.readRe 0 0 0 1 ∧
    Char.readAlt 0 1 0 0 = Char.readAlt 0 0 0 1 ∧
    Char.readIm 0 1 0 0 ≠ Char.readIm 0 0 0 1 := by decide

theorem Char.alt_irreplaceable :
    Char.readBal 1 0 1 0 = Char.readBal 0 1 0 1 ∧
    Char.readRe 1 0 1 0 = Char.readRe 0 1 0 1 ∧
    Char.readIm 1 0 1 0 = Char.readIm 0 1 0 1 ∧
    Char.readAlt 1 0 1 0 ≠ Char.readAlt 0 1 0 1 := by decide

/-- info: 'Foam.Char.count_hom' does not depend on any axioms -/
#guard_msgs in #print axioms Char.count_hom

/-- info: 'Foam.Char.alt_hom' does not depend on any axioms -/
#guard_msgs in #print axioms Char.alt_hom

/-- info: 'Foam.Char.chi_hom' does not depend on any axioms -/
#guard_msgs in #print axioms Char.chi_hom

/-- info: 'Foam.Char.chiBar_hom' does not depend on any axioms -/
#guard_msgs in #print axioms Char.chiBar_hom

/-- info: 'Foam.Char.count_unit' does not depend on any axioms -/
#guard_msgs in #print axioms Char.count_unit

/-- info: 'Foam.Char.alt_unit' does not depend on any axioms -/
#guard_msgs in #print axioms Char.alt_unit

/-- info: 'Foam.Char.chi_unit' does not depend on any axioms -/
#guard_msgs in #print axioms Char.chi_unit

/-- info: 'Foam.Char.chiBar_unit' does not depend on any axioms -/
#guard_msgs in #print axioms Char.chiBar_unit

/-- info: 'Foam.Char.count_norm' does not depend on any axioms -/
#guard_msgs in #print axioms Char.count_norm

/-- info: 'Foam.Char.alt_norm' does not depend on any axioms -/
#guard_msgs in #print axioms Char.alt_norm

/-- info: 'Foam.Char.chi_norm' does not depend on any axioms -/
#guard_msgs in #print axioms Char.chi_norm

/-- info: 'Foam.Char.chiBar_norm' does not depend on any axioms -/
#guard_msgs in #print axioms Char.chiBar_norm

/-- info: 'Foam.Char.count_alt_orth' does not depend on any axioms -/
#guard_msgs in #print axioms Char.count_alt_orth

/-- info: 'Foam.Char.count_chi_orth' does not depend on any axioms -/
#guard_msgs in #print axioms Char.count_chi_orth

/-- info: 'Foam.Char.count_chiBar_orth' does not depend on any axioms -/
#guard_msgs in #print axioms Char.count_chiBar_orth

/-- info: 'Foam.Char.alt_chi_orth' does not depend on any axioms -/
#guard_msgs in #print axioms Char.alt_chi_orth

/-- info: 'Foam.Char.alt_chiBar_orth' does not depend on any axioms -/
#guard_msgs in #print axioms Char.alt_chiBar_orth

/-- info: 'Foam.Char.chi_chiBar_orth' does not depend on any axioms -/
#guard_msgs in #print axioms Char.chi_chiBar_orth

/-- info: 'Foam.Char.chi_distinct_chiBar' does not depend on any axioms -/
#guard_msgs in #print axioms Char.chi_distinct_chiBar

/-- info: 'Foam.Char.alt_distinct_count' does not depend on any axioms -/
#guard_msgs in #print axioms Char.alt_distinct_count

/-- info: 'Foam.GInt.mulReal' depends on axioms: [propext] -/
#guard_msgs in #print axioms GInt.mulReal

/-- info: 'Foam.Char.fold_re_components' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.fold_re_components

/-- info: 'Foam.Char.fold_im_components' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.fold_im_components

/-- info: 'Foam.Char.readBal_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.readBal_eq

/-- info: 'Foam.Char.readAlt_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.readAlt_eq

/-- info: 'Foam.Char.readRe_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.readRe_eq

/-- info: 'Foam.Char.readIm_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.readIm_eq

/-- info: 'Foam.Char.four_swap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.four_swap

/-- info: 'Foam.Char.sub_pair' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.sub_pair

/-- info: 'Foam.Char.sum_diff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.sum_diff

/-- info: 'Foam.Char.diff_sum' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.diff_sum

/-- info: 'Foam.Char.twice_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.twice_add

/-- info: 'Foam.Char.twice_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.twice_sub

/-- info: 'Foam.Char.bal_add_alt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.bal_add_alt

/-- info: 'Foam.Char.bal_sub_alt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.bal_sub_alt

/-- info: 'Foam.Char.recover_bin0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.recover_bin0

/-- info: 'Foam.Char.recover_bin1' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.recover_bin1

/-- info: 'Foam.Char.recover_bin2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.recover_bin2

/-- info: 'Foam.Char.recover_bin3' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.recover_bin3

/-- info: 'Foam.Char.lossless' depends on axioms: [propext] -/
#guard_msgs in #print axioms Char.lossless

/-- info: 'Foam.Char.bal_irreplaceable' does not depend on any axioms -/
#guard_msgs in #print axioms Char.bal_irreplaceable

/-- info: 'Foam.Char.re_irreplaceable' does not depend on any axioms -/
#guard_msgs in #print axioms Char.re_irreplaceable

/-- info: 'Foam.Char.im_irreplaceable' does not depend on any axioms -/
#guard_msgs in #print axioms Char.im_irreplaceable

/-- info: 'Foam.Char.alt_irreplaceable' does not depend on any axioms -/
#guard_msgs in #print axioms Char.alt_irreplaceable

end Foam