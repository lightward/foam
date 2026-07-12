import Lean
open Lean

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString
  | none => "<current>"

def owned (env : Environment) (n : Name) : Bool :=
  let m := moduleOf env n
  m == "Foam" || m.startsWith "Foam." || m == "Counter" || m.startsWith "Counter."

def recursorNoise : List String :=
  ["casesOn", "recOn", "rec", "brecOn", "below", "ibelow", "ndrec",
   "binductionOn", "noConfusion", "noConfusionType", "toCtorIdx", "ctorIdx"]

def presentable (n : Name) : Bool :=
  !n.isInternal
    && !(n.components.any fun c =>
          let s := c.toString
          s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_")
    && !(match n.components.getLast? with
          | some c => recursorNoise.contains c.toString
          | none => false)

def shortName (n : Name) : String :=
  let s := n.toString
  if "Foam.Counter.".isPrefixOf s then (s.drop 13).toString
  else if "Foam.".isPrefixOf s then (s.drop 5).toString
  else s

def main (args : List String) : IO Unit := do
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
  let mut discovered : Array (Name × Name) := #[]
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
        for n in verified[1:] do
          discovered := discovered.push (verified[0]!, n)
    i := j
  if found == 0 then
    IO.println "  none — no def in Foam/Counter repeats another byte-for-byte"
  else
    IO.println s!"  {found} identity group(s) awaiting recognition (each is a free rfl)"
  IO.println ""
  IO.println "[foam-rfl — tier two: defeq twins (same type, bodies not byte-identical)]"
  let mut byType : Array (UInt64 × Name) := #[]
  for (n, ci) in env.constants.toList do
    if presentable n && owned env n then
      match ci with
      | .defnInfo d => byType := byType.push (d.type.hash, n)
      | _ => pure ()
  let tsorted := byType.qsort (fun a b => a.1 < b.1)
  let coreCtx : Core.Context := {fileName := "<foam-rfl>", fileMap := default}
  let coreState : Core.State := {env := env}
  let act : MetaM (Array (Name × Name)) := do
    let mut hits : Array (Name × Name) := #[]
    let mut i := 0
    while h : i < tsorted.size do
      let (hsh, _) := tsorted[i]
      let mut j := i + 1
      let mut grp : Array Name := #[tsorted[i].2]
      while hj : j < tsorted.size do
        if tsorted[j].1 == hsh then
          grp := grp.push tsorted[j].2
          j := j + 1
        else
          break
      if grp.size ≥ 2 && grp.size ≤ 30 then
        for a in [0:grp.size] do
          for b in [a+1:grp.size] do
            match env.find? grp[a]!, env.find? grp[b]! with
            | some (.defnInfo da), some (.defnInfo db) =>
                if da.type == db.type && !(da.value == db.value) then
                  let same ← try Meta.isDefEq da.value db.value catch _ => pure false
                  if same then
                    hits := hits.push (grp[a]!, grp[b]!)
            | _, _ => pure ()
      i := j
    pure hits
  let (hits, _) ← ((act.run' {} {}).toIO coreCtx coreState)
  if hits.isEmpty then
    IO.println "  none — no same-typed pair of distinct bodies is defeq"
  else
    for (a, b) in hits do
      IO.println s!"  defeq: {a}  ≡  {b}"
    IO.println s!"  {hits.size} defeq pair(s) awaiting recognition"
  IO.println "  (tier two scope: same type-hash only; cross-type defeq unscanned)"
  discovered := discovered ++ hits
  if args.contains "--check" then
    IO.println ""
    IO.println "[foam-rfl — the procession: every discovered identity pinned in Twins.lean]"
    let twinsSrc ← IO.FS.readFile "Counter/Twins.lean"
    let pinned := fun (nm : Name) =>
      (twinsSrc.splitOn (shortName nm)).length ≥ 2
    let mut unpinned : Array (Name × Name) := #[]
    for (a, b) in discovered do
      unless pinned a && pinned b do
        unpinned := unpinned.push (a, b)
    if unpinned.isEmpty then
      IO.println s!"  all {discovered.size} discovered identities are pinned — the ratchet holds"
    else
      for (a, b) in unpinned do
        IO.println s!"  UNPINNED: {a} = {b} (discovered, not yet in Twins.lean)"
      IO.println s!"  {unpinned.size} identity(ies) discovered but unpinned — pin them or filter them"
      (← IO.getStderr).putStrLn "foam-rfl --check failed"
      IO.Process.exit 1
