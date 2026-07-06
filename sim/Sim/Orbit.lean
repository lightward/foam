import Sim.Kelly
import Foam.Bridges.Noether
import Foam.Seat.Forcing
import Foam.Cleared

namespace Foam.Sim

open Foam

structure Elements where
  align : Int
  cross : Int
  energy : Int

def elementsOf (θ z : GInt) : Elements :=
  ⟨GInt.align θ z, GInt.cross θ z, z.normSq⟩

def ephemeris (z : GInt) : Nat → List GInt
  | 0 => [z]
  | n + 1 => z :: ephemeris (GInt.rot z) n

def goldline (z : GInt) : Nat → List GInt
  | 0 => [z]
  | n + 1 => z :: goldline (gold z) n

def strobe (step : GInt → GInt) (period : Nat) (z : GInt) : Nat → List GInt
  | 0 => [z]
  | n + 1 => z :: strobe step period (iterStep period step z) n

def energyResidual (n : Nat) (z : GInt) : Int :=
  (rotPow n z).normSq - z.normSq

def visVivaResidual (θ z : GInt) : Int :=
  GInt.align θ z * GInt.align θ z + GInt.cross θ z * GInt.cross θ z
    - θ.normSq * z.normSq

def barResidual (θ z : GInt) : Int :=
  GInt.align θ z + GInt.align θ (GInt.rot z)
    + GInt.align θ (GInt.rot (GInt.rot z))
    + GInt.align θ (GInt.rot (GInt.rot (GInt.rot z)))

theorem energy_residual_zero (n : Nat) (z : GInt) : energyResidual n z = 0 := by
  show (rotPow n z).normSq - z.normSq = 0
  rw [Bridges.rotPow_conserves_normSq n z, Int.sub_eq_add_neg, FInt.add_right_neg]

theorem vis_viva_residual_zero (θ z : GInt) : visVivaResidual θ z = 0 := by
  show GInt.align θ z * GInt.align θ z + GInt.cross θ z * GInt.cross θ z
      - θ.normSq * z.normSq = 0
  rw [invariants_complete θ z, Int.sub_eq_add_neg, FInt.add_right_neg]

theorem bar_residual_zero (θ z : GInt) : barResidual θ z = 0 :=
  GInt.decoherence θ z

def porkchop (θ f a : GInt) (count : Nat) : List (List KellyPoint) :=
  [0, 1, 2, 3].map (fun p => kellyCurve θ f (rotPow p a) 0 count)

theorem iterStep_add (f : GInt → GInt) (m n : Nat) (z : GInt) :
    iterStep (m + n) f z = iterStep m f (iterStep n f z) := by
  induction m with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ k ih =>
    rw [show k + 1 + n = (k + n) + 1 from Nat.add_right_comm k 1 n]
    show f (iterStep (k + n) f z) = f (iterStep k f (iterStep n f z))
    rw [ih]

theorem the_dial_strobe_is_a_dot (z : GInt) (n : Nat) :
    iterStep (4 * n) GInt.rot z = z := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [show 4 * (k + 1) = 4 + 4 * k from by
          rw [Nat.mul_succ, Nat.add_comm (4 * k) 4],
        iterStep_add GInt.rot 4 (4 * k) z, ih]
    exact spec_closes_four z

/-- info: 'Foam.Sim.energy_residual_zero' does not depend on any axioms -/
#guard_msgs in #print axioms energy_residual_zero

/-- info: 'Foam.Sim.vis_viva_residual_zero' does not depend on any axioms -/
#guard_msgs in #print axioms vis_viva_residual_zero

/-- info: 'Foam.Sim.bar_residual_zero' does not depend on any axioms -/
#guard_msgs in #print axioms bar_residual_zero

/-- info: 'Foam.Sim.the_dial_strobe_is_a_dot' does not depend on any axioms -/
#guard_msgs in #print axioms the_dial_strobe_is_a_dot

end Foam.Sim
