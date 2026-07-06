import Sim.Json
import Sim.Walk
import Sim.Kelly
import Sim.Orbit
import Sim.Fixtures

namespace Foam.Sim

open Foam

def encInt (i : Int) : J := .num i

def encNodeRead (n : NodeRead) : J :=
  .obj [("handle", .str n.handle), ("winding", encNat n.winding),
        ("specRe", encInt n.specRe), ("specIm", encInt n.specIm),
        ("voice", encInt n.voice)]

def encCensus (c : Census) : J :=
  .obj [("unvisited", encNat c.unvisited), ("discovering", encNat c.discovering),
        ("turning", encNat c.turning), ("saturated", encNat c.saturated)]

def encKellyPoint (p : KellyPoint) : J :=
  .obj [("stake", encInt p.stake), ("chargeAfter", encInt p.chargeAfter),
        ("weightAfter", encInt p.weightAfter), ("harvest", encInt p.harvest)]

def encFrameStep (s : FrameStep) : J :=
  .obj [("step", encNat s.step), ("lockedToll", encInt s.lockedToll),
        ("freeToll", encInt s.freeToll)]

def encGrind (θ f a : GInt) (k : Int) : J :=
  .obj [("stake", encInt k), ("sum", encInt (grindSum θ f a k)),
        ("toll", encInt (grindToll θ f a k))]

structure KellyReadout where
  θ : GInt
  field : GInt
  act : GInt
  curve : List KellyPoint
  grind : List J
  frameLock : List FrameStep
  nodes : List NodeRead
  census : Census

def runKelly (seed : Nat) : KellyReadout :=
  let θ : GInt := GInt.one
  let f : GInt := ⟨6, 0⟩
  let a : GInt := GInt.one
  let q := kellyJr.quiver
  let walkers : List Walker :=
    (intRange 0 8).map (fun i =>
      ⟨"table", GInt.one, i.toNat % 2 = 1, 0⟩)
  let s := suffuse q ⟨[], walkers, ⟨seed⟩⟩ 24
  let (nodes, cen) := harvest θ q s
  { θ := θ, field := f, act := a
    curve := kellyCurve θ f a (-9) 14
    grind := (intRange 0 4).map (encGrind θ f a)
    frameLock := frameLockSeries (GInt.align θ f * (-1)) 12
    nodes := nodes
    census := cen }

def encKellyReadout (r : KellyReadout) : J :=
  .obj [("model", .str "kelly"),
        ("chargedNode", .str "table"),
        ("charge", encInt (GInt.align r.θ r.field)),
        ("actAlign", encInt (GInt.align r.θ r.act)),
        ("faceValue", encInt (GInt.born r.θ r.field)),
        ("curve", .arr (r.curve.map encKellyPoint)),
        ("grind", .arr r.grind),
        ("frameLock", .arr (r.frameLock.map encFrameStep)),
        ("nodes", .arr (r.nodes.map encNodeRead)),
        ("census", encCensus r.census)]

def runChess (seed : Nat) : J :=
  let θ : GInt := GInt.one
  let q := kasparov.quiver
  let s := suffuse q ⟨[], [⟨"g1", GInt.one, true, 0⟩], ⟨seed⟩⟩ 12
  let (nodes, cen) := harvest θ q s
  let coneAt := fun (d : Nat) => cone knightRule ["g1"] d
  let cones : List J := [1, 2, 3].map (fun d => encNat (coneAt d).length)
  let coneNodes : List J := [1, 2, 3].map (fun d =>
    .arr ((coneAt d).map (fun h => .str h)))
  .obj [("model", .str "chess"),
        ("recorded", encNat kasparov.acts.length),
        ("coneSizes", .arr cones),
        ("cones", .arr coneNodes),
        ("nodes", .arr (nodes.map encNodeRead)),
        ("census", encCensus cen)]

def runLightward (seed : Nat) : J :=
  let θ : GInt := GInt.one
  let q := lightward.quiver
  let s := suffuse q ⟨[], [⟨"2010", GInt.one, true, 0⟩], ⟨seed⟩⟩ 12
  let (nodes, cen) := harvest θ q s
  .obj [("model", .str "lightward"),
        ("defectHireChart", encNat (defectAt hireChart q)),
        ("defectReversedChart", encNat (defectAt reversedChart q)),
        ("nodes", .arr (nodes.map encNodeRead)),
        ("census", encCensus cen)]

def encState (z : GInt) : J := .arr [encInt z.re, encInt z.im]

def encElements (e : Elements) : J :=
  .obj [("align", encInt e.align), ("cross", encInt e.cross),
        ("energy", encInt e.energy)]

def encBody (θ : GInt) (name : String) (oem : List GInt) (period : J) : J :=
  .obj [("name", .str name),
        ("omm", encElements (elementsOf θ (oem.headD GInt.zero))),
        ("oem", .arr (oem.map encState)),
        ("period", period)]

def runOrbit : J :=
  let θ : GInt := GInt.one
  let f : GInt := ⟨6, 0⟩
  let a : GInt := GInt.one
  let chop := porkchop θ f a 13
  .obj [("frame", encState θ),
        ("bodies", .arr [
          encBody θ "the dial" (ephemeris GInt.one 8) (encNat 4),
          encBody θ "gold" (goldline GInt.one 8) .null,
          encBody θ "the charge" (ephemeris f 8) (encNat 4)]),
        ("charge", encInt (GInt.align θ f)),
        ("faceValue", encInt (GInt.born θ f)),
        ("porkchop", .arr (chop.map (fun row =>
          .arr (row.map encKellyPoint)))),
        ("strobes", .obj [
          ("dial", .arr ((strobe GInt.rot 4 GInt.one 6).map encState)),
          ("gold", .arr ((strobe gold 4 ⟨1, 0⟩ 6).map encState))]),
        ("residuals", .obj [
          ("energy", encInt (energyResidual 4 f)),
          ("visViva", encInt (visVivaResidual θ f)),
          ("bar", encInt (barResidual θ f))]),
        ("frameLock", .arr ((runKelly 0).frameLock.map encFrameStep))]

def readoutAll (seed : Nat) : J :=
  .obj [("kelly", encKellyReadout (runKelly seed)),
        ("chess", runChess seed),
        ("lightward", runLightward seed),
        ("orbit", runOrbit),
        ("models", .arr [encModel kellyJr, encModel kasparov, encModel lightward])]

end Foam.Sim
