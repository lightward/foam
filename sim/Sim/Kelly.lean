import Sim.Walk
import Counter.Kelly

namespace Foam.Sim

open Foam

structure KellyPoint where
  stake : Int
  chargeAfter : Int
  weightAfter : Int
  harvest : Int

def kellyAt (θ f a : GInt) (k : Int) : KellyPoint :=
  let staked := f.add (GInt.smul k a)
  ⟨k, GInt.align θ staked, GInt.born θ staked,
   GInt.born θ f - GInt.born θ staked⟩

def intRange (lo : Int) : Nat → List Int
  | 0 => []
  | n + 1 => lo :: intRange (lo + 1) n

def kellyCurve (θ f a : GInt) (lo : Int) (count : Nat) : List KellyPoint :=
  (intRange lo count).map (kellyAt θ f a)

def grindSum (θ f a : GInt) (k : Int) : Int :=
  GInt.born θ (f.add (GInt.smul k a))
    + GInt.born θ (f.add (GInt.smul k a.rot))
    + GInt.born θ (f.add (GInt.smul k (a.rot.rot)))
    + GInt.born θ (f.add (GInt.smul k (a.rot.rot.rot)))

def grindToll (θ f a : GInt) (k : Int) : Int :=
  grindSum θ f a k - 4 * GInt.born θ f

theorem the_toll_is_the_theorem (θ f a : GInt) (k : Int) :
    grindToll θ f a k = 2 * ((k * k) * (GInt.normSq θ * GInt.normSq a)) := by
  show grindSum θ f a k - 4 * GInt.born θ f
      = 2 * ((k * k) * (GInt.normSq θ * GInt.normSq a))
  rw [show grindSum θ f a k
        = GInt.born θ (f.add (GInt.smul k a))
            + GInt.born θ (f.add (GInt.smul k a.rot))
            + GInt.born θ (f.add (GInt.smul k (a.rot.rot)))
            + GInt.born θ (f.add (GInt.smul k (a.rot.rot.rot))) from rfl,
      Foam.Counter.the_grind_pays_the_toll θ f a k, FInt.addComm,
      FInt.add_sub_cancel_right]

structure FrameStep where
  step : Nat
  lockedToll : Int
  freeToll : Int

def frameLockSeries (chargePerStep : Int) (steps : Nat) : List FrameStep :=
  let cross := 2 * chargePerStep
  (intRange 0 steps).map (fun i =>
    let n := i.toNat
    ⟨n, cross * Int.ofNat n, if n = 0 then 0 else cross⟩)

/-- info: 'Foam.Sim.the_toll_is_the_theorem' does not depend on any axioms -/
#guard_msgs in #print axioms the_toll_is_the_theorem

end Foam.Sim
