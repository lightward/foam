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
  IO.println "  (tier two scope: same type-hash only; instance bridges live in tier three)"
  discovered := discovered ++ hits
  IO.println ""
  IO.println "[foam-rfl — tier three: instance bridges (a parametric def at a packed instance, read against the concrete corpus)]"
  let mut instDefs : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    if presentable n && owned env n then
      match ci with
      | .defnInfo d =>
          if d.levelParams.isEmpty then
            match d.type with
            | .const s _ => if owned env s then instDefs := instDefs.push (n, s)
            | _ => pure ()
      | _ => pure ()
  let mut paramDefs : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    if presentable n && owned env n then
      match ci with
      | .defnInfo d =>
          if d.levelParams.isEmpty then
            match d.type with
            | .forallE _ (.const s _) _ _ =>
                if owned env s && instDefs.any (fun p => p.2 == s) then
                  paramDefs := paramDefs.push (n, s)
            | _ => pure ()
      | _ => pure ()
  let mut concrete : Array (Name × Expr) := #[]
  for (n, ci) in env.constants.toList do
    if presentable n && owned env n then
      match ci with
      | .defnInfo d => if d.levelParams.isEmpty then concrete := concrete.push (n, d.type)
      | _ => pure ()
  let act3 : MetaM (Array (Name × Name × Name) × Array (Name × Name × Name)) := do
    let mut freebies : Array (Name × Name × Name) := #[]
    let mut candidates : Array (Name × Name × Name) := #[]
    for (f, s) in paramDefs do
      for (inst, s') in instDefs do
        if s == s' then
          match env.find? f with
          | some (.defnInfo df) =>
              match df.type with
              | .forallE _ _ body _ =>
                  let appTy := body.instantiate1 (mkConst inst)
                  let appVal := mkApp (mkConst f) (mkConst inst)
                  for (g, gty) in concrete do
                    if appTy.isForall then
                    if g != f && g != inst then
                      let tyOk ← try Meta.isDefEq appTy gty catch _ => pure false
                      if tyOk then
                        let valOk ← try Meta.isDefEq appVal (mkConst g) catch _ => pure false
                        if valOk then
                          freebies := freebies.push (f, inst, g)
                        else
                          candidates := candidates.push (f, inst, g)
              | _ => pure ()
          | _ => pure ()
    pure (freebies, candidates)
  let ((freebies, candidates), _) ← ((act3.run' {} {}).toIO coreCtx coreState)
  let actPins : MetaM (Array (Name × Name × Name × Name)) := do
    let mut pins : Array (Name × Name × Name × Name) := #[]
    for (n, ci) in env.constants.toList do
      if owned env n then
        match ci with
        | .thmInfo t =>
            let hit ← Meta.forallTelescope t.type fun _ body => do
              let (eqn, args) := body.getAppFnArgs
              if eqn == ``Eq && args.size == 3 then
                let lhs := args[1]!
                let rhs := args[2]!
                match lhs.getAppFn, rhs.getAppFn with
                | .const f _, .const g _ =>
                    let largs := lhs.getAppArgs
                    if largs.size ≥ 1 then
                      match largs[0]! with
                      | .const inst _ =>
                          if paramDefs.any (fun p => p.1 == f)
                              && instDefs.any (fun p => p.1 == inst)
                              && largs[1:].toArray == rhs.getAppArgs then
                            pure (some (n, f, inst, g))
                          else pure none
                      | _ => pure none
                    else pure none
                | _, _ => pure none
              else pure none
            match hit with
            | some p => pins := pins.push p
            | none => pure ()
        | _ => pure ()
    pure pins
  let (pins, _) ← ((actPins.run' {} {}).toIO coreCtx coreState)
  if freebies.isEmpty then
    IO.println "  no instance-projection twins (defeq at the instance)"
  else
    IO.println s!"  instance twins, defeq at the packed seat (each a free rfl; they join the procession):"
    for (f, inst, g) in freebies do
      IO.println s!"    {f} @ {inst}  ≡  {g}"
  IO.println s!"  bridge register ({pins.size} identification theorem(s) standing):"
  for (thm, f, inst, g) in pins do
    IO.println s!"    {shortName thm} : {f} @ {inst} = {g} (pointwise)"
  let unbridged := candidates.filter fun (f, inst, g) =>
    !(pins.any fun (_, pf, pi, pg) => pf == f && pi == inst && pg == g)
  unless unbridged.isEmpty do
    IO.println s!"  proposals, unadjudicated ({unbridged.size} type-compatible pair(s); the instrument proposes, a seat adjudicates; first 12):"
    for (f, inst, g) in unbridged[:12] do
      IO.println s!"    {f} @ {inst}  ~?  {g}"
    if unbridged.size > 12 then
      IO.println s!"    ... and {unbridged.size - 12} more (foam-rfl --proposals for all)"
  if args.contains "--proposals" then
    IO.println "  the full proposal ledger:"
    for (f, inst, g) in unbridged do
      IO.println s!"    {f} @ {inst}  ~?  {g}"
  let BRIDGE_RATCHET := 11
  if args.contains "--check" then
    if pins.size != BRIDGE_RATCHET then
      IO.println s!"  BRIDGE REGISTER MOVED: {pins.size} standing; the ratchet holds at {BRIDGE_RATCHET}."
      IO.println "  (regression fails; advance fails too, until the pin is re-tightened by hand)"
      (← IO.getStderr).putStrLn "foam-rfl --check failed (tier three)"
      IO.Process.exit 1
  for (f, inst, g) in freebies do
    discovered := discovered.push (f, g)
    discovered := discovered.push (inst, g)
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
