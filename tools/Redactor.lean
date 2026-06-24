import Foam
import Lean
import Lean.Server.References
open Lean Lean.Elab

namespace FoamRedactor

/-! ## Harvest -------------------------------------------------------------- -/

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

/-- Harvest every foam identifier occurrence via the full snapshot pipeline:
    `runFrontend` writes an ilean collecting references from ALL snapshots
    (including tactic bodies), which `Ilean.load` parses back. Field projections
    resolve to their projection const; dot-notation spans cover only the field
    component. `definition?` is the decl site (present only in the home module). -/
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

/-! ## Dictionary ----------------------------------------------------------- -/

/-- name → (leaf token, redacted qualified name, role), from the deposit. -/
def loadDict (path : System.FilePath) : IO (Std.HashMap String (String × String × String)) := do
  let content ← IO.FS.readFile path
  let mut m : Std.HashMap String (String × String × String) := {}
  for line in content.splitOn "\n" do
    let parts := line.splitOn "\t"
    if parts.length ≥ 5 then
      m := m.insert parts[3]! (parts[0]!, parts[4]!, parts[1]!)
  return m

/-! ## Coordinates ---------------------------------------------------------- -/

/-- Byte offset within a line for a 0-based UTF-16 column. -/
def utf16ColToByte (line : String) (col : Nat) : Nat := Id.run do
  let mut u16 := 0
  let mut bytes := 0
  for c in line.data do
    if u16 ≥ col then return bytes
    u16 := u16 + (if c.val < 0x10000 then 1 else 2)
    bytes := bytes + c.utf8Size
  return bytes

/-- Byte offset of the start of each line (UTF-8). -/
def lineByteStarts (lines : Array String) : Array Nat := Id.run do
  let mut starts := #[0]
  let mut acc := 0
  for ln in lines do
    acc := acc + ln.toUTF8.size + 1
    starts := starts.push acc
  return starts

/-! ## Structural line-pass -------------------------------------------------- -/

def hasSub (s sub : String) : Bool := (s.splitOn sub).length ≥ 2

/-- After the ident splice: drop the now-redundant `open Foam.FInt (…)` (possibly
    multi-line), and flatten the dissolved sub-namespaces. -/
def structuralPass (src : String) (dict : Std.HashMap String (String × String × String)) : String := Id.run do
  let mut out : Array String := #[]
  let mut inOpen := false
  for line in src.splitOn "\n" do
    if inOpen then
      if hasSub line ")" then inOpen := false
    else if line.trimLeft.startsWith "open Foam.FInt" then
      if !hasSub line ")" then inOpen := true
    else if line.startsWith "namespace Foam." || line.startsWith "end Foam." then
      -- a sub-namespace that IS a foam type (e.g. `Ledger`) keeps its token
      -- nesting; a pure organizational one (`FInt`) dissolves into `Foam`.
      let ws := line.splitOn " "
      out := out.push <| match dict.get? ws[1]! with
        | some (tok, _, _) => s!"{ws[0]!} Foam.{tok}"
        | none             => s!"{ws[0]!} Foam"
    else
      out := out.push line
  return "\n".intercalate out.toList

/-! ## Structure-body sibling fields ---------------------------------------- -/

def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '.'

/-- Replace whole-word occurrences of `old` with `new` (identifier boundaries). -/
def wordReplace (s old new : String) : String := Id.run do
  let parts := s.splitOn old
  if parts.length ≤ 1 then return s
  let mut res := parts[0]!
  for i in [1:parts.length] do
    let before := parts[i-1]!
    let after := parts[i]!
    let leftOk  := before.isEmpty || !isIdentChar before.toList.getLast!
    let rightOk := after.isEmpty  || !isIdentChar after.toList.head!
    res := res ++ (if leftOk && rightOk then new else old) ++ after
  return res

/-- Within each `structure`/`class` body, rewrite sibling-field references —
    which structure elaboration resolves specially and the ilean never sees, so
    the field *decls* get renamed but their type bodies still hold old names. -/
def structFieldPass (src : String) (fieldMap : Std.HashMap String (Array (String × String))) : String := Id.run do
  let mut out : Array String := #[]
  let mut cur : Array (String × String) := #[]
  let mut inBody := false
  for line in src.splitOn "\n" do
    if line.startsWith "structure " || line.startsWith "class " then
      cur := fieldMap.getD ((line.splitOn " ")[1]!) #[]
      inBody := true
      out := out.push line
    else if inBody && (line.isEmpty || !line.startsWith " ") then
      inBody := false
      out := out.push line
    else if inBody then
      out := out.push (cur.foldl (fun l (old, tok) => wordReplace l old tok) line)
    else
      out := out.push line
  return "\n".intercalate out.toList

/-- structure-token → its members' (original short name, token), from the deposit. -/
def buildFieldMap (dict : Std.HashMap String (String × String × String)) :
    Std.HashMap String (Array (String × String)) := Id.run do
  let mut m : Std.HashMap String (Array (String × String)) := {}
  for (name, (tok, qname, _)) in dict.toList do
    let qc := qname.splitOn "."
    if qc.length ≥ 3 then
      let structTok := qc[1]!
      m := m.insert structTok ((m.getD structTok #[]).push ((name.splitOn ".").getLast!, tok))
  return m

/-! ## Redact one file ------------------------------------------------------- -/

structure FileStats where
  occs   : Nat
  reps   : Nat
  misses : Array String

unsafe def redactFile (path : System.FilePath) (ileanPath : System.FilePath)
    (dict : Std.HashMap String (String × String × String))
    (fieldMap : Std.HashMap String (Array (String × String))) : IO FileStats := do
  let occs ← harvestIlean path ileanPath
  let src ← IO.FS.readFile path
  let bytes := src.toUTF8
  let lines := (src.splitOn "\n").toArray
  let starts := lineByteStarts lines
  let lspToByte := fun (l c : Nat) => (starts[l]!) + utf16ColToByte (lines[l]!) c
  let mut reps : Array (Nat × Nat × String) := #[]
  let mut misses : Array String := #[]
  for o in occs do
    let sB := lspToByte o.sLine o.sChar
    let eB := lspToByte o.eLine o.eChar
    let dot := sB > 0 && bytes[sB-1]! == 46  -- preceded by '.' ⇒ dot-notation
    let written := String.fromUTF8! (bytes.extract sB eB)
    let qualified := written.contains '.'    -- how the occurrence is written
    match dict.get? o.name with
    | some (leaf, qname, _) =>
      let repl :=
        if o.isDecl then
          -- nested decls are written qualified (`Seat.foo`) ⇒ namespace-relative
          -- qname; physically-nested ctors/fields are bare ⇒ leaf token.
          if qualified then ".".intercalate ((qname.splitOn ".").drop 1) else leaf
        else if dot then leaf            -- dot-notation: field/method component
        else if !qualified then leaf     -- bare: case-tag, sibling field, in-namespace
        else qname                       -- qualified head usage
      reps := reps.push (sB, eB, repl)
    | none =>
      -- A companion (`.mk`/`.rec`/…) of a renamed parent: nest the unchanged
      -- suffix under the parent's redaction. (Anonymous-instance decl sites like
      -- `instMulRot` have no parent in the dict and are correctly skipped.)
      let comps := o.name.splitOn "."
      let suffix := comps.getLast!
      match dict.get? (".".intercalate comps.dropLast) with
      | some (_, pqname, _) =>
        if o.isDecl then misses := misses.push o.name
        else reps := reps.push (sB, eB, if dot || !qualified then suffix else s!"{pqname}.{suffix}")
      | none => misses := misses.push o.name
  -- splice ascending, skipping overlaps/dups
  let sorted := reps.qsort (fun a b => a.1 < b.1)
  let mut out : ByteArray := .empty
  let mut cursor := 0
  for (s, e, repl) in sorted do
    if s ≥ cursor then
      out := out ++ bytes.extract cursor s ++ repl.toUTF8
      cursor := e
  out := out ++ bytes.extract cursor bytes.size
  let mut newSrc := structFieldPass (String.fromUTF8! out) fieldMap
  newSrc := structuralPass newSrc dict
  -- guard-message docstrings: 'Foam.name' ⇒ 'qname'. Longest names first, so a
  -- prime-suffixed `X'` is consumed before `X`'s search mistakes the prime for a
  -- closing quote.
  for (name, (_, qname, _)) in dict.toList.toArray.qsort (fun a b => a.1.length > b.1.length) do
    newSrc := newSrc.replace s!"'{name}'" s!"'{qname}'"
  IO.FS.writeFile path newSrc
  return ⟨occs.size, reps.size, misses⟩

/-! ## Drive ----------------------------------------------------------------- -/

partial def collectLean (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut acc := #[]
  for entry in (← dir.readDir) do
    let p := entry.path
    if (← p.isDir) then acc := acc ++ (← collectLean p)
    else if p.toString.endsWith ".lean" then acc := acc.push p
  return acc

unsafe def main : IO Unit := do
  let dict ← loadDict "tools/dictionary.tsv"
  let fieldMap := buildFieldMap dict
  let ilean : System.FilePath :=
    "/private/tmp/claude-501/-Users-isaac-dev-foam/c6b13605-4469-42f9-9bcb-67e3b9fa3353/scratchpad/tmp.ilean"
  let mut files ← collectLean "Foam"
  files := files.push "Foam.lean"
  let mut totalMiss : Std.HashMap String Nat := {}
  for f in files.qsort (·.toString < ·.toString) do
    let st ← redactFile f ilean dict fieldMap
    for m in st.misses do totalMiss := totalMiss.insert m ((totalMiss.getD m 0) + 1)
    IO.println s!"{f}: occs={st.occs} reps={st.reps} misses={st.misses.size}"
  IO.println s!"\ndistinct dict-misses: {totalMiss.size}"
  for (m, c) in totalMiss.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {c}×  {m}"

#eval main

end FoamRedactor
