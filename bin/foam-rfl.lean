import Lean
open Lean

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString
  | none => "<current>"

def owned (env : Environment) (n : Name) : Bool :=
  let m := moduleOf env n
  m == "Foam" || m.startsWith "Foam." || m == "Counter" || m.startsWith "Counter."

def presentable (n : Name) : Bool :=
  !n.isInternal
    && !(n.components.any fun c =>
          let s := c.toString
          s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_")

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Counter}] {}
  let mut items : Array (UInt64 × Name) := #[]
  for (n, ci) in env.constants.toList do
    if presentable n && owned env n then
      match ci with
      | .defnInfo d =>
          items := items.push (mixHash d.type.hash d.value.hash, n)
      | _ => pure ()
  let sorted := items.qsort (fun a b => a.1 < b.1)
  let mut i := 0
  let mut found := 0
  IO.println "[foam-rfl — byte-identical definition bodies, unidentified identities]"
  while h : i < sorted.size do
    let (hsh, n0) := sorted[i]
    let mut j := i + 1
    let mut grp : Array Name := #[n0]
    while hj : j < sorted.size do
      if sorted[j].1 == hsh then
        grp := grp.push sorted[j].2
        j := j + 1
      else
        break
    if grp.size ≥ 2 then
      let verified ← grp.filterM fun n => do
        match env.find? n0, env.find? n with
        | some (.defnInfo a), some (.defnInfo b) =>
            pure (a.type == b.type && a.value == b.value)
        | _, _ => pure false
      if verified.size ≥ 2 then
        found := found + 1
        IO.println s!"  twins ({verified.size}):"
        for n in verified do
          IO.println s!"    {n}  [{moduleOf env n}]"
    i := j
  if found == 0 then
    IO.println "  none — no def in Foam/Counter repeats another byte-for-byte"
  else
    IO.println s!"  {found} identity group(s) awaiting recognition (each is a free rfl)"
  IO.println "  (v1 is alpha-sensitive: renamed binders hide twins; defeq tier seeded)"
