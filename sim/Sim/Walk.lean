import Sim.Model
import Foam.Engine.Spectrum
import Foam.Seat.Born
import Foam.Seat.Sort

namespace Foam.Sim

open Foam

structure Wind where
  state : Nat

def Wind.next (w : Wind) : Nat × Wind :=
  let s := (w.state * 1103515245 + 12345) % 2147483648
  (s / 65536, ⟨s⟩)

def Wind.below (w : Wind) (n : Nat) : Nat × Wind :=
  let (s, w') := w.next
  (s % n, w')

def outs (q : Quiver String) (u : String) : List String :=
  (q.filter (fun e => e.1 == u)).map (·.2)

def weightOf (θ : GInt) (trace : List String) (t : String) : Nat :=
  (GInt.born θ (spec trace t)).toNat + 1

def pick : List (String × Nat) → Nat → Option String
  | [], _ => none
  | (t, w) :: rest, roll =>
    if roll < w then some t else pick rest (roll - w)

def totalWeight (ws : List (String × Nat)) : Nat :=
  ws.foldl (fun acc p => acc + p.2) 0

structure Walker where
  at_ : String
  frame : GInt
  free : Bool
  toll : Int

def turnIfTaxed (wk : Walker) (cross : Int) : Walker :=
  match cross with
  | .negSucc _ => if wk.free then { wk with frame := wk.frame.rot } else wk
  | .ofNat _ => wk

def stepWalker (q : Quiver String) (trace : List String) (wk : Walker)
    (wind : Wind) : Walker × Wind :=
  let candidates := outs q wk.at_
  match candidates with
  | [] => (wk, wind)
  | _ =>
    let ws := candidates.map (fun t => (t, weightOf wk.frame trace t))
    let (roll, wind') := wind.below (totalWeight ws)
    match pick ws roll with
    | none => (wk, wind')
    | some t =>
      let fieldHere := spec trace t
      let cross := 2 * (GInt.align wk.frame fieldHere * GInt.align wk.frame GInt.one)
      let wk' := turnIfTaxed { wk with at_ := t, toll := wk.toll + cross } cross
      (wk', wind')

structure Suffusion where
  trace : List String
  walkers : List Walker
  wind : Wind

def tick (q : Quiver String) (s : Suffusion) : Suffusion :=
  let (walkers', trace', wind') := s.walkers.foldl
    (fun (acc : List Walker × List String × Wind) wk =>
      let (wk', wind') := stepWalker q acc.2.1 wk acc.2.2
      (wk' :: acc.1, wk'.at_ :: acc.2.1, wind'))
    ([], s.trace, s.wind)
  ⟨trace', walkers'.reverse, wind'⟩

def suffuse (q : Quiver String) (s : Suffusion) : Nat → Suffusion
  | 0 => s
  | n + 1 => suffuse q (tick q s) n

structure NodeRead where
  handle : String
  winding : Nat
  specRe : Int
  specIm : Int
  voice : Int

def readNode (θ : GInt) (trace : List String) (h : String) : NodeRead :=
  let z := spec trace h
  ⟨h, Ledger.freq trace h, z.re, z.im, GInt.born θ z⟩

def nodesOf (q : Quiver String) : List String :=
  (q.map (·.1) ++ q.map (·.2)).eraseDups

structure Census where
  unvisited : Nat
  discovering : Nat
  turning : Nat
  saturated : Nat

def classify (n : NodeRead) (c : Census) : Census :=
  if n.winding = 0 then { c with unvisited := c.unvisited + 1 }
  else if n.voice ≠ 0 then { c with discovering := c.discovering + 1 }
  else if n.winding < 4 then { c with turning := c.turning + 1 }
  else { c with saturated := c.saturated + 1 }

def census (reads : List NodeRead) : Census :=
  reads.foldl (fun c n => classify n c) ⟨0, 0, 0, 0⟩

def harvest (θ : GInt) (q : Quiver String) (s : Suffusion) :
    List NodeRead × Census :=
  let reads := (nodesOf q).map (readNode θ s.trace)
  (reads, census reads)

def defectAt (chart : List (String × Nat)) (q : Quiver String) : Nat :=
  let rank := fun h =>
    match chart.find? (fun p => p.1 == h) with
    | some p => p.2
    | none => 0
  Foam.defect rank q

end Foam.Sim
