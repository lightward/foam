import Foam.Lattice.Frontstage
import Foam.Lattice.Product
import Foam.Lattice.Refinement
import Foam.Lattice.Merge
import Foam.Lattice.Reading
import Foam.Lattice.Dial
import Foam.Lattice.Resume
import Foam.Lattice.Born
import Foam.Lattice.Order
import Foam.Lattice.Tower
import Foam.Lattice.Entrance
import Foam.Lattice.Engine
import Foam.Lattice.Forever
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut checked := 0
  let mut offenders : Array (Name × List Name) := #[]
  for (name, info) in env.constants.toList do
    if info matches .thmInfo _ then
      if let some idx := env.getModuleIdxFor? name then
        if (`Foam.Lattice).isPrefixOf (env.header.moduleNames[idx.toNat]!) then
          if (← findDeclarationRanges? name).isSome then
            checked := checked + 1
            let foreign := (← collectAxioms name).toList.filter (· != ``propext)
            unless foreign.isEmpty do
              offenders := offenders.push (name, foreign)
  if checked == 0 then
    throwError "Foam.Lattice coverage found no theorems — the filter is broken."
  unless offenders.isEmpty do
    let lines := offenders.toList.map fun (n, ax) => s!"  {n} imports {ax}"
    throwError "the lattice's propext-only discipline is broken — {offenders.size} \
      theorem(s) import a foreign axiom:\n{String.intercalate "\n" lines}"
  logInfo s!"propext-only verified across {checked} written theorems in the Lattice"
