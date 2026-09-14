import Lean
import Counter
open Lean Elab

/-! the gate, drawn from the compiler's own species: an artifact is elaborated whole (every
message a parting — a receipt that does not match prints one), each organ's receipt is read by
the kernel (the axioms it seats on) — theorems and carriers alike, since a def carries its
compilation into every theorem that cites it (2026-09-14: an overlapping catch-all compiled
through propext and was heard only two rows downstream) — and the verdict is `Counter.conductive`
on that shadow, the same def the assay's rows run. every organ carries its receipt inline, minted
by the grow at one seat, and the gate counts the kernel's organs against the file's receipts. the
gate reads a body only through the kernel;
its verdict is a function of the shadow (`Counter.the_gate_hears_only_the_receipt`). -/

abbrev EnvM := StateM Environment
instance : MonadEnv EnvM where
  getEnv := get
  modifyEnv f := modify f

def receiptsOf (env : Environment) (n : Name) : List Name :=
  ((collectAxioms n : EnvM (Array Name)).run env).1.toList

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let mut red := false
  for path in args do
    Lean.enableInitializersExecution
    let src ← IO.FS.readFile path
    let ictx := Parser.mkInputContext src path
    let (hdr, ps, msgs) ← Parser.parseHeader ictx
    let imports := headerToImports hdr
    let env ← importModules (if imports.isEmpty then #[{ module := `Init }] else imports) {} 0 (loadExts := true)
    let cs := Command.mkState env msgs (({} : Options).setBool `Elab.async false)
    let s ← IO.processCommands ictx ps cs
    let st := s.commandState
    let ns : Name := Id.run do
      for line in src.splitOn "\n" do
        if line.startsWith "namespace " then return (line.drop 10).trimAscii.toName
      return .anonymous
    -- the organs are what the file receipts (the grow mints one per block, dotted names included),
    -- and every top-level constant of the namespace must be among them: the file decides, the kernel
    -- checks the file's list is complete at the top and reads every name on it
    let receipted : List Name := ((src.splitOn "#print axioms ").drop 1).map fun rest =>
      let ident := (rest.takeWhile fun c => c.isAlphanum || c == '_' || c == '.' || c == '\'').toName
      if ns == .anonymous then ident else ns ++ ident
    let mut shadow : List (Name × List Name) := []
    let mut theorems := 0
    let mut holds : List String := []
    for n in receipted do
      match st.env.find? n with
      | some ci =>
        if ci.isTheorem then theorems := theorems + 1
        shadow := (n, receiptsOf st.env n) :: shadow
      | none => holds := holds ++ [s!"{n} is receipted but is no constant"]
    for (n, _) in st.env.constants.map₂.toList do
      if n.isInternal then continue
      if ns != .anonymous && n.getPrefix != ns then continue
      if !receipted.contains n then holds := holds ++ [s!"{n} is an organ without a receipt"]
    let carriers := shadow.length - theorems
    let receipts := receipted.length
    let partings := st.messages.toList
    let conductive := Counter.conductive shadow
    if !partings.isEmpty then
      holds := holds ++ [s!"{partings.length} messages (the first: {(← partings.head!.toString).trimAscii.take 160})"]
    if !conductive then
      let smuggled := shadow.filter (fun r => !r.2.isEmpty)
      holds := holds ++ smuggled.map (fun r => s!"{r.1} seats on {r.2}")
    if holds.isEmpty then
      IO.println s!"the gate [{path}]: silent, {shadow.length} organs ({theorems} theorems, {carriers} carriers), {receipts} receipts inline, conductive — drawn from Counter.gate"
    else
      red := true
      IO.println s!"the gate [{path}]: PARTS"
      for h in holds do IO.println s!"  {h}"
  if red then IO.Process.exit 1
