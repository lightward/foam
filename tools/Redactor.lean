import Foam
import Lean
import Lean.Server.References
open Lean Lean.Elab

namespace FoamRedactor

/-- foam-authored ⟺ outermost name component is `Foam`. -/
def isFoam (n : Name) : Bool := n.getRoot == `Foam

/-- `Foam/Seat.lean` ⇒ module name `Foam.Seat`. -/
def moduleNameOf (path : System.FilePath) : Name :=
  (((path.toString).dropEnd 5).toString.replace "/" ".").toName

/-- A harvested occurrence: 0-based UTF-16 LSP coordinates, resolved full name,
    and whether this is the declaration site (vs a usage). -/
structure Occ where
  sLine  : Nat
  sChar  : Nat
  eLine  : Nat
  eChar  : Nat
  name   : String
  isDecl : Bool
deriving Inhabited, Repr

/-- Harvest every foam identifier occurrence in a file via the full snapshot
    pipeline: `runFrontend` writes an ilean that collects references from ALL
    snapshots (including tactic bodies), which `Ilean.load` parses back. Field
    projections resolve to their projection const; dot-notation spans cover only
    the field component. The map key is the resolved name; each value carries its
    declaration site (`definition?`, present only in the name's home module) and
    its usage sites. -/
unsafe def harvestIlean (path : System.FilePath) (ileanPath : System.FilePath) : IO (Array Occ) := do
  let src ← IO.FS.readFile path
  enableInitializersExecution
  let _ ← Lean.Elab.runFrontend src {} path.toString (moduleNameOf path)
    (ileanFileName? := some ileanPath)
  let ilean ← Lean.Server.Ilean.load ileanPath
  let mut hits : Array Occ := #[]
  for (ident, info) in ilean.references do
    match ident with
    | .const _ nameStr =>
      if nameStr.startsWith "Foam." then
        if let some d := info.definition? then
          hits := hits.push ⟨d.startPosLine, d.startPosCharacter, d.endPosLine, d.endPosCharacter, nameStr, true⟩
        for l in info.usages do
          hits := hits.push ⟨l.startPosLine, l.startPosCharacter, l.endPosLine, l.endPosCharacter, nameStr, false⟩
    | _ => pure ()
  return hits

unsafe def go : IO Unit := do
  let ilean : System.FilePath :=
    "/private/tmp/claude-501/-Users-isaac-dev-foam/c6b13605-4469-42f9-9bcb-67e3b9fa3353/scratchpad/tmp.ilean"
  let hits ← harvestIlean "Foam/Seat.lean" ilean
  let decls := (hits.filter (·.isDecl)).size
  IO.println s!"foam refs: {hits.size}  (decls: {decls}, usages: {hits.size - decls})"

#eval go

end FoamRedactor
