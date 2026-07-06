import Sim

open Foam.Sim

def main (args : List String) : IO Unit := do
  let seed := match args with
    | s :: _ => s.toNat!
    | [] => 20260705
  let j := readoutAll seed
  IO.FS.createDirAll "out"
  IO.FS.writeFile "out/readout.json" (j.render ++ "\n")
  IO.FS.createDirAll "exhibit"
  IO.FS.writeFile "exhibit/data.js" ("window.READOUT = " ++ j.render ++ ";\n")
  IO.println "harvest saved: out/readout.json, exhibit/data.js"
