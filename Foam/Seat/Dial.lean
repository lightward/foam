import Foam.Seat.Clock

namespace Foam

structure GInt where
  re : Int
  im : Int
  deriving DecidableEq

def GInt.mul (z w : GInt) : GInt :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

def GInt.add (z w : GInt) : GInt := ⟨z.re + w.re, z.im + w.im⟩

def GInt.i : GInt := ⟨0, 1⟩
def GInt.normSq (z : GInt) : Int := z.re * z.re + z.im * z.im

def Rot.amp : Rot → GInt
  | .r0 => ⟨1, 0⟩
  | .r1 => ⟨0, 1⟩
  | .r2 => ⟨-1, 0⟩
  | .r3 => ⟨0, -1⟩

theorem Rot.amp_hom (a b : Rot) : (a * b).amp = GInt.mul a.amp b.amp := by
  cases a <;> cases b <;> decide

theorem Rot.amp_turn (a : Rot) : (Rot.r1 * a).amp = GInt.mul GInt.i a.amp := by
  cases a <;> decide

theorem Rot.amp_unit (a : Rot) : a.amp.normSq = 1 := by
  cases a <;> decide

theorem GInt.sq_image (a : Int) : ∃ k : Nat, a * a = Int.ofNat k := by
  cases a with
  | ofNat m => exact ⟨m * m, rfl⟩
  | negSucc m => exact ⟨(m + 1) * (m + 1), rfl⟩

theorem GInt.normSq_nonneg (z : GInt) : ∃ k : Nat, z.normSq = Int.ofNat k := by
  obtain ⟨k1, h1⟩ := GInt.sq_image z.re
  obtain ⟨k2, h2⟩ := GInt.sq_image z.im
  refine ⟨k1 + k2, ?_⟩
  show z.re * z.re + z.im * z.im = Int.ofNat (k1 + k2)
  rw [h1, h2]; rfl

/-- info: 'Foam.Rot.amp_hom' does not depend on any axioms -/
#guard_msgs in #print axioms Rot.amp_hom

/-- info: 'Foam.Rot.amp_turn' does not depend on any axioms -/
#guard_msgs in #print axioms Rot.amp_turn

/-- info: 'Foam.Rot.amp_unit' does not depend on any axioms -/
#guard_msgs in #print axioms Rot.amp_unit

/-- info: 'Foam.GInt.normSq_nonneg' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.normSq_nonneg

end Foam
