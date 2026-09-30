import Lean
import Pieces
open Lean Elab

def elabFrom (src : String) (name : String) (st : Option Command.State) (extra : Array Import := #[]) : IO Command.State := do
  let ictx := Parser.mkInputContext src name
  let (hdr, ps, msgs) ← Parser.parseHeader ictx
  let cs ← match st with
    | some s => pure { s with messages := {} }
    | none =>
        let imports := headerToImports hdr ++ extra
        let env ← importModules (if imports.isEmpty then #[{ module := `Init }] else imports) {} 0 (loadExts := true)
        pure (Command.mkState env msgs (({} : Options).setBool `Elab.async false))
  let s ← IO.processCommands ictx ps cs
  return s.commandState

/-- the same, keeping every command's syntax: a body as Syntax, not a string -/
def elabCommands (src : String) (name : String) (extra : Array Import := #[]) : IO (Command.State × Array Syntax) := do
  let ictx := Parser.mkInputContext src name
  let (hdr, ps, msgs) ← Parser.parseHeader ictx
  let env ← importModules (headerToImports hdr ++ extra) {} 0 (loadExts := true)
  let cs := Command.mkState env msgs (({} : Options).setBool `Elab.async false)
  let s ← IO.processCommands ictx ps cs
  return (s.commandState, s.commands)

/-- the namespaces a reading is about: the trail's own, and the imported ones whose
theorems the trail may cite (given as `ns` and a comma-separated `imports` arg) -/
structure Scope where
  ns : Name
  imported : List Name

def Scope.parse (args : List String) (i : Nat) : Scope :=
  let ns := (args[i]?).map String.toName |>.getD `Foam
  let imported := ((args[i+1]?).getD "").splitOn "," |>.filter (· ≠ "") |>.map String.toName
  ⟨ns, imported⟩

def Scope.owns (sc : Scope) (n : Name) : Bool :=
  n.getPrefix == sc.ns || sc.imported.any (fun m => n.getPrefix == m)

partial def usedTopLevel (env : Environment) (sc : Scope) (seen : NameSet) (n : Name) : NameSet := Id.run do
  let some ci := env.find? n | return seen
  let mut seen := seen
  let consts := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
  for c in consts do
    if seen.contains c then continue
    if sc.owns c then
      seen := seen.insert c
    else if (env.getModuleIdxFor? c).isNone then
      seen := usedTopLevel env sc (seen.insert c) c
  return seen

def nameOf (sc : Scope) (n : Name) : String :=
  if n.getPrefix == sc.ns then n.getString! else n.toString

def needsMode (trail : String) (sc : Scope) : IO Unit := do
  let st ← elabFrom (← IO.FS.readFile trail) trail none
  let env := st.env
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns then continue
    if !ci.isTheorem then continue
    let used := usedTopLevel env sc {} n
    let deps := used.toList.filter (fun d => d != n && sc.owns d && (env.find? d).any (·.isTheorem))
    IO.println s!"{n.getString!} <- {" ".intercalate (deps.map (nameOf sc))}"

def citesMode (trail : String) (sc : Scope) : IO Unit := do
  let st ← elabFrom (← IO.FS.readFile trail) trail none
  let env := st.env
  for (n, ci) in env.constants.map₂.toList do
    if n.getPrefix != sc.ns then continue
    let used := usedTopLevel env sc {} n
    let deps := used.toList.filter (fun d => d != n && sc.owns d)
    let kind := if ci.isTheorem then "theorem" else "carrier"
    IO.println s!"{kind} {n.getString!} <- {" ".intercalate (deps.map (nameOf sc))}"

/-- a body as a SHAPE: every name that is a theorem of the house, or resolves to nothing in the
environment (a binder, a hypothesis, a name `intro` or `cases` brought in), becomes a hole `?`;
the theorem's own name (a structural recursion's call) becomes `?self`; carriers, constructors,
and core stay — they are what the shape is about. two bodies with one shape are one shape -/
partial def abstractSyntax (env : Environment) (sc : Scope) (self : Name) (stx : Syntax) : Syntax :=
  match stx with
  | .ident info _ n _ =>
    if n.isAnonymous then stx else
    let resolves := [n, sc.ns ++ n] ++ sc.imported.map (· ++ n)
    let found := resolves.filterMap env.find?
    if n == self || sc.ns ++ n == self then mkIdent (Name.mkSimple "?self")
    else if found.isEmpty then mkIdent (Name.mkSimple "?")
    else if found.any (·.isTheorem) && found.any (fun ci => sc.owns ci.name) then mkIdent (Name.mkSimple "?")
    else .ident info (toString n).toRawSubstring n []
  | .node i k args =>
    -- a field (`.trans`, `.1`) and a hygiene mark are structure, not names
    if k == `hygieneInfo then stx
    else if k == ``Lean.Parser.Term.proj then .node i k (args.modify 0 (abstractSyntax env sc self))
    else .node i k (args.map (abstractSyntax env sc self))
  | _ => stx

def squeeze (s : String) : String :=
  (" ".intercalate ((s.splitOn " ").filter (· ≠ ""))).replace "\n" " "

/-- shapes: every theorem's body abstracted, then the census of shapes — how many bodies each
shape covers, which is what bodies-as-shapes can carry -/
def shapesMode (trail : String) (sc : Scope) : IO Unit := do
  let (st, cmds) ← elabCommands (← IO.FS.readFile trail) trail
  let env := st.env
  let mut rows : Array (Name × String × String) := #[]
  for c in cmds do
    if !c.isOfKind ``Lean.Parser.Command.declaration then continue
    let d := c[1]
    if !d.isOfKind ``Lean.Parser.Command.theorem then continue
    let name := sc.ns ++ d[1][0].getId
    let val := d[3]
    let mode := if val.isOfKind ``Lean.Parser.Command.declValSimple then
                  (if val[1].isOfKind ``Lean.Parser.Term.byTactic then "tactic" else "term")
                else "equations"
    let body := if val.isOfKind ``Lean.Parser.Command.declValSimple then val[1] else val
    let shape := squeeze ((abstractSyntax env sc name body).reprint.getD "<no reprint>")
    rows := rows.push (name, mode, shape)
  let mut groups : Std.HashMap String (Array Name) := {}
  for (n, m, sh) in rows do
    let key := m ++ "\t" ++ sh
    groups := groups.insert key ((groups.getD key #[]).push n)
  let sorted := groups.toArray.qsort (fun a b => a.2.size > b.2.size)
  IO.println s!"the shapes: {rows.size} bodies, {sorted.size} shapes"
  for (key, names) in sorted do
    let parts := key.splitOn "\t"
    IO.println s!"{names.size}\t{parts.headD ""}\t{(parts.getD 1 "").take 160}"
    IO.println s!"\t\t{" ".intercalate (names.map (fun n => n.getString!)).toList}"

/-- a body as a PIECE: the searches' winners inverted. every recorded citation form — `(apply T <;> …)`,
`(apply (T _).trans (by …) <;> …)`, `(rw [T]; …)`, `exact T …`, a cited application in a term —
becomes the search that found it; the carriers a `dsimp only` unfolds become the vacancy's own
(`{defs}`); the theorem's own name becomes `{self}`; locals, constructors, and core stay verbatim.
what is left citing a theorem after that is a hole no search reaches, and the body is unrendered -/
def isCite (env : Environment) (sc : Scope) (n : Name) : Bool :=
  if n.isAnonymous then false else
  let found := ([n, sc.ns ++ n] ++ sc.imported.map (· ++ n)).filterMap env.find?
  found.any (·.isTheorem) && found.any (fun ci => sc.owns ci.name)

partial def citesAny (env : Environment) (sc : Scope) : Syntax → Bool
  | .ident _ _ n _ => isCite env sc n
  | .node _ _ args => args.any (citesAny env sc)
  | _ => false

def placeholder (s : String) : Syntax :=
  Syntax.ident SourceInfo.none s.toRawSubstring (Name.mkSimple s) []

def seqItems (seq : Syntax) : Array Syntax := Id.run do
  if seq.getKind == ``Lean.Parser.Tactic.tacticSeq && seq[0].getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
    let args := seq[0][0].getArgs
    let mut out := #[]
    for i in [0:args.size] do
      if i % 2 == 0 then out := out.push args[i]!
    return out
  else return #[]

/-- a piece of syntax parsed from its text — the trail elaborated with the pieces imported, so the
searches' names are tokens -/
def parseAs (env : Environment) (cat : Name) (s : String) : Syntax :=
  match Parser.runParserCategory env cat s with
  | .ok x => x
  | .error _ => .missing

def isChainHead (e : Syntax) : Bool :=
  e.isOfKind ``Lean.Parser.Term.app && e[0].isOfKind ``Lean.Parser.Term.proj && e[0][2].getId == `trans

/-- the leftmost name of a term: the head of an application, a projection, a paren -/
partial def headName : Syntax → Option Name
  | .ident _ _ n _ => some n
  | stx =>
    if stx.isOfKind ``Lean.Parser.Term.app || stx.isOfKind ``Lean.Parser.Term.proj then headName stx[0]
    else if stx.isOfKind ``Lean.Parser.Term.paren then headName stx[1]
    else none

/-- the statement's own binder names — the parameters and named hypotheses a search at the goal
reads from the local context: the names in binder position, in the signature's binders and its ∀s -/
partial def sigBinders (stx : Syntax) : NameSet :=
  match stx with
  | .node _ k args =>
    let here : NameSet :=
      if k == ``Lean.Parser.Term.explicitBinder || k == ``Lean.Parser.Term.implicitBinder
          || k == ``Lean.Parser.Term.strictImplicitBinder || k == ``Lean.Parser.Term.instBinder then
        stx[1].getArgs.foldl (fun acc a => if a.isIdent then acc.insert a.getId else acc) {}
      else if k == ``Lean.Parser.Term.forall then
        stx[1].getArgs.foldl (fun acc a =>
          if a.isIdent then acc.insert a.getId
          else if a.getKind == ``Lean.Parser.Term.binderIdent && a[0].isIdent then acc.insert a[0].getId
          else acc) {}
      else {}
    args.foldl (fun acc a => acc.union (sigBinders a)) here
  | _ => {}

partial def render (env : Environment) (sc : Scope) (self : Name) (hyps : NameSet) (stx : Syntax) : Syntax :=
  let seek := parseAs env `tactic "piece_seek"
  let hole := parseAs env `term "(by piece_seek)"
  -- a citation or a statement hypothesis AT THE HEAD of a term is what a search at the goal finds;
  -- one deeper inside a term is reached by the rules below at its own position, and the term's
  -- structure around it stays
  let cites (s : Syntax) := (headName s).any fun n => isCite env sc n || hyps.contains n
  let rec rwCites (s : Syntax) : Bool := match s with
    | .node _ k args => (k == ``Lean.Parser.Tactic.rwRule && args.size > 0 && cites args[args.size - 1]!) || args.any rwCites
    | _ => false
  -- the closer after a rewrite or a chain is kept beside the generic ones: an exemplar's own
  -- closing move is a move the search may need
  let seekWith (kind : String) (closer : Syntax) : Syntax :=
    let c := ((render env sc self hyps closer).reprint.getD "").trimAscii.toString
    let flat := " ".intercalate (((c.replace "\n" " ").splitOn " ").filter (· ≠ ""))
    let own := if flat == "rfl" || flat == "assumption" || flat == "piece_seek" || flat.isEmpty then "" else s!" | {flat}"
    parseAs env `tactic s!"{kind} (first | rfl | assumption{own} | piece_seek)"
  -- a replacement keeps the whitespace the original ended in, so the layout it sat in survives
  let put (new : Syntax) : Syntax := new.setTailInfo stx.getTailInfo
  let isSelf (s : Syntax) := s.isIdent && (s.getId == self || sc.ns ++ s.getId == self)
  match stx with
  | .ident _ _ n _ =>
    if n == self || sc.ns ++ n == self then put (placeholder "{self}")
    else if citesAny env sc stx then put hole else stx
  | .node i k args =>
    -- a parenthesized winner: `(apply e <;> side)`, `(rw [t]; closers)`
    let items := if k == ``Lean.Parser.Tactic.paren then seqItems stx[1] else #[]
    if items.size == 1 && items[0]!.isOfKind ``Lean.Parser.Tactic.«tactic_<;>_»
        && items[0]![0].isOfKind ``Lean.Parser.Tactic.apply && cites items[0]![0][1] then
      let target := items[0]![0][1]
      if isChainHead target then
        -- `(apply (T _).trans (by C) <;> …)`: the chain's far end is C
        let far := target[1][0]
        let closer := if far.isOfKind ``Lean.Parser.Term.paren && far[1].isOfKind ``Lean.Parser.Term.byTactic then far[1][1] else far
        put (seekWith "piece_chain_seek" closer)
      else put seek
    else if items.size == 2 && items[0]!.isOfKind ``Lean.Parser.Tactic.rwSeq && rwCites items[0]! then
      put (seekWith "piece_rw_seek" items[1]!)
    else if k == ``Lean.Parser.Tactic.exact && cites stx[1] && !(citesAny env sc stx[1] && isSelf stx[1][0]) then put seek
    -- the carriers unfolded are the vacancy's own
    else if k == ``Lean.Parser.Tactic.dsimp then
      let args := args.map fun a =>
        if a.getKind == `null && a.getNumArgs == 3 && a[0].isAtom && a[0].getAtomVal == "[" then
          a.setArg 1 (mkNullNode #[placeholder "{defs}"])
        else a
      .node i k args
    -- a cited application in a term: the hole, searched where the term determines its type
    else if k == ``Lean.Parser.Term.app && stx[0].isIdent && citesAny env sc stx[0] && !isSelf stx[0] then put hole
    else
      let args := args.map (render env sc self hyps)
      -- a fan whose alternatives rendered alike keeps one of each
      if k == ``Lean.Parser.Tactic.first && args.size == 2 then
        let groups := args[1]!.getArgs
        let kept := groups.foldl (fun (acc : Array Syntax) g =>
          if acc.any (fun x => x.reprint == g.reprint) then acc else acc.push g) #[]
        .node i k #[args[0]!, args[1]!.setArgs kept]
      else .node i k args
  | _ => stx

/-- a fan blanked: every `first` node's alternatives replaced by one mark, so two bodies that
differ only in which branch closed which goal read as one SKELETON -/
partial def blankFans (stx : Syntax) : Syntax :=
  match stx with
  | .node i k args =>
    if k == ``Lean.Parser.Tactic.first && args.size == 2 then
      .node i k #[args[0]!, mkNullNode #[placeholder "…"]]
    else .node i k (args.map blankFans)
  | _ => stx

/-- a token's trailing whitespace replaced -/
def withTrailing (stx : Syntax) (ws : String) : Syntax :=
  match stx.getTailInfo with
  | .original lead pos _ endPos => stx.setTailInfo (.original lead pos ws.toRawSubstring endPos)
  | _ => stx

/-- the fans of one skeleton unioned: at each `first`, every alternative any member of the group
ran, the most-run first (ties in the order met); outside the fans the members agree by
construction. an alternative is read squeezed to one line — a recorded winner is parenthesized,
and inside parens the layout is position-free — and the fan is re-parsed from its text; a fan
with an alternative that cannot be squeezed keeps its own -/
partial def unionFans (env : Environment) (e : Syntax) (others : Array Syntax) : Syntax :=
  match e with
  | .node i k args =>
    if k == ``Lean.Parser.Tactic.first && args.size == 2 then
      let all := (#[e] ++ others).flatMap fun o => if o.getKind == k && o.getNumArgs == 2 then o[1].getArgs else #[]
      let flat (s : String) : String := " ".intercalate (((s.replace "\n" " ").splitOn " ").filter (· ≠ ""))
      let texts := all.map fun g => flat (g[1].reprint.getD "")
      let unsqueezable := all.any fun g =>
        let t := (g[1].reprint.getD "").trimAscii.toString
        t.contains '\n' && !t.startsWith "("
      if unsqueezable then .node i k args else
      let distinct := texts.foldl (fun (acc : Array (String × Nat × Nat)) s =>
        match acc.findIdx? (·.1 == s) with
        | some j => acc.modify j (fun (s, n, ix) => (s, n + 1, ix))
        | none => acc.push (s, 1, acc.size)) #[]
      let sorted := distinct.qsort fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)
      let text := "first " ++ " ".intercalate (sorted.map fun (s, _, _) => "| " ++ s).toList
      let parsed := parseAs env `tactic text
      if parsed.isMissing then .node i k args else parsed.setTailInfo e.getTailInfo
    else
      let args := args.mapIdx fun j a => unionFans env a (others.filterMap fun o => if o.getNumArgs > j then some o[j] else none)
      .node i k args
  | _ => e

/-- one line of text: whitespace runs and newlines as one space -/
def flat (s : String) : String := " ".intercalate (((s.replace "\n" " ").splitOn " ").filter (· ≠ ""))

/-- the fans of a rendered body marked: every `first` whose alternatives squeeze to one line
(a recorded winner is parenthesized, and inside parens the layout is position-free) becomes
`{fanK}`, its alternatives returned beside it in order — so the union over a skeleton's bodies is
the reader's to take per vacancy, a body's own fan never offered to itself; a fan with an
alternative that cannot be squeezed stays as it stands -/
partial def markFans (stx : Syntax) : StateM (Array (Array String)) Syntax := do
  match stx with
  | .node i k args =>
    if k == ``Lean.Parser.Tactic.first && args.size == 2 then
      let groups := args[1]!.getArgs
      let unsqueezable := groups.any fun g =>
        let t := (g[1].reprint.getD "").trimAscii.toString
        t.contains '\n' && !t.startsWith "("
      if unsqueezable then return stx
      let texts := groups.map fun g => flat (g[1].reprint.getD "")
      let n := (← get).size
      modify (·.push texts)
      return (placeholder s!"\{fan{n}}").setTailInfo stx.getTailInfo
    else
      let args ← args.mapM markFans
      return .node i k args
  | _ => return stx

/-- templates: every theorem's body as a piece — the searches' winners inverted — with its
skeleton (every fan blanked) and its fans marked and listed; one line per body: the name, the
mode, the skeleton, the template with `{fanK}` marks (newlines as ⏎), the fans (alternatives by
␟, fans by ␞). the grow groups bodies by skeleton and, per vacancy, unions the fans of the
others. a vacancy (`sorry`) has no shape. a body that still cites where no search reaches is
named unrendered -/
def templatesMode (trail : String) (sc : Scope) : IO Unit := do
  let source ← IO.FS.readFile trail
  let (st, cmds) ← elabCommands source trail #[{ module := `Pieces }]
  let env := st.env
  let mut unrendered : Array Name := #[]
  let mut count := 0
  let mut lines : Array String := #[]
  for c in cmds do
    if !c.isOfKind ``Lean.Parser.Command.declaration then continue
    let d := c[1]
    if !d.isOfKind ``Lean.Parser.Command.theorem then continue
    let name := sc.ns ++ d[1][0].getId
    let val := d[3]
    let mode := if val.isOfKind ``Lean.Parser.Command.declValSimple then
                  (if val[1].isOfKind ``Lean.Parser.Term.byTactic then "tactic" else "term")
                else "equations"
    let body := if val.isOfKind ``Lean.Parser.Command.declValSimple then val[1] else val
    let raw := flat (body.reprint.getD "")
    if raw == "sorry" || raw == "by sorry" then continue
    count := count + 1
    let r := render env sc name (sigBinders d[2]) body
    if citesAny env sc r then unrendered := unrendered.push name; continue
    let skel := flat ((blankFans r).reprint.getD "")
    let (marked, fans) := (markFans r).run #[]
    let tpl := (marked.reprint.getD "").trimAscii.toString.replace "\n" "⏎"
    let fanText := "␞".intercalate (fans.map fun f => "␟".intercalate f.toList).toList
    lines := lines.push s!"{name}\t{mode}\t{skel}\t{tpl}\t{fanText}"
  IO.println s!"the templates: {count} bodies, {lines.size} rendered; {unrendered.size} unrendered: {" ".intercalate (unrendered.map (·.getString!)).toList}"
  for l in lines do IO.println l

unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let sc := Scope.parse args 2
  if args.head? == some "needs" then
    needsMode args[1]! sc
    return
  if args.head? == some "cites" then
    citesMode args[1]! sc
    return
  if args.head? == some "shapes" then
    shapesMode args[1]! sc
    return
  if args.head? == some "templates" then
    templatesMode args[1]! sc
    return
  if args.head? == some "pieces" then
    -- the knobs, read from bin/Pieces.lean; the pieces themselves are derived (`templates`)
    IO.println s!"budget {Pieces.budget}"
    IO.println s!"reach {Pieces.reach}"
    return
  let prefixSrc ← IO.FS.readFile args[0]!
  let candSrc ← IO.FS.readFile args[1]!
  -- candidates come grouped by vacancy (`-- vacancy` between groups, `-- candidate` within), in
  -- the pieces' order: a group stops at its first seat, because the cascade takes the first seated
  -- piece anyway — the rest are reported `skipped`, never elaborated (the probe, `vv`, sees all)
  let groups := (candSrc.splitOn "\n-- vacancy\n").map fun grp =>
    (grp.splitOn "\n-- candidate\n").filter (fun c => !c.trimAscii.isEmpty)
  -- a trial imports the pieces; the artifact never does (the judge reports each seated body expanded)
  let base ← elabFrom prefixSrc "<prefix>" none #[{ module := `Pieces }]
  let baseMsgs := base.messages.toList
  if !baseMsgs.isEmpty then
    IO.println s!"prefix not silent: {baseMsgs.length} messages"
    for m in baseMsgs.take 5 do IO.println s!"  {m.pos.line}:{m.pos.column} {← m.data.toString}"
    IO.Process.exit 1
  let mut i := 0
  let mut judged := 0
  let verbose := args.length > 2
  let sentences := args.length > 2 && args[2]! == "vv"
  for grp in groups do
   let mut seatedYet := false
   for c in grp do
    if seatedYet && !sentences then
      IO.println s!"{i} skipped"
      i := i + 1
      continue
    judged := judged + 1
    let t0 ← IO.monoMsNow
    let s ← elabFrom ("#seat " ++ c ++ "\n") s!"<candidate {i}>" (some base)
    let msgs := s.messages.toList
    let bad := msgs.any (fun m => m.severity != .information)
    let dt := (← IO.monoMsNow) - t0
    IO.println s!"{i} {if bad then "held" else "seated"}{if verbose then s!" {dt}ms" else ""}"
    if !bad then
      -- the body as elaborated, pieces expanded: one line per line, each behind `| `
      for m in msgs do
        if m.severity == .information then
          let txt ← m.data.toString
          for l in txt.splitOn "\n" do IO.println s!"| {l}"
    if sentences && bad then
      for m in msgs do
        if m.severity != .information then
          let txt ← m.data.toString
          for l in (txt.splitOn "\n").take 24 do
            IO.println s!"    {l}"
    if !bad then seatedYet := true
    i := i + 1
  IO.println s!"judged {judged}"
