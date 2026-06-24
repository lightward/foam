import Foam
import Lean
open Lean

namespace FoamInstrument

/-- Output location for the dictionary. -/
def outPath : System.FilePath :=
  "tools/dictionary.tsv"

/-- Auto-generated companion suffixes we never redact independently — they
    inherit their parent's token by namespace. `mk` covers structure ctors. -/
def autoComponents : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ind",
   "noConfusion", "noConfusionType", "injEq", "inj", "mk", "sizeOf",
   "toCtorIdx", "rawCast", "ctorElimType", "elimType"]

/-- True if any component of `n` matches an auto-generated marker. `inst…`
    catches `deriving`/`instance` synthesis — host plumbing, not foam coinage. -/
partial def hasAutoComponent : Name → Bool
  | .anonymous => false
  | .num p _ => hasAutoComponent p
  | .str p s =>
      autoComponents.contains s || s.startsWith "eq_" || s.startsWith "match_"
        || s.startsWith "inst"
        || hasAutoComponent p

/-- `p` is an ancestor-prefix of `n` (core lacks `Name.isPrefixOf`). -/
partial def isPrefix (p : Name) : Name → Bool
  | n =>
    p == n || (match n with
      | .str n' _ => isPrefix p n'
      | .num n' _ => isPrefix p n'
      | .anonymous => false)

/-- foam-authored ⟺ under the `Foam` namespace. The `Foam.` prefix is the
    common-language boundary: anything without it is host/common vocabulary. -/
def isFoam (n : Name) : Bool := isPrefix `Foam n

partial def hasNumOrUnderscore : Name → Bool
  | .anonymous => false
  | .num _ _ => true
  | .str p s => s.startsWith "_" || hasNumOrUnderscore p

def lastStr : Name → String
  | .str _ s => s
  | _ => ""

/-- A primary, source-authored name: foam, not internal, not an auto companion. -/
def isPrimary (n : Name) : Bool :=
  isFoam n && !n.isInternalDetail && !hasNumOrUnderscore n && !hasAutoComponent n

/-- Collapse any foam name onto the nearest enclosing primary node. -/
partial def ownerOf (primSet : NameSet) : Name → Option Name
  | n =>
    if primSet.contains n then some n
    else match n with
      | .str p _ => ownerOf primSet p
      | .num p _ => ownerOf primSet p
      | .anonymous => none

open Lean.Meta in
/-- Role by *result-sort*, not by source keyword:
    `Prop`-valued (theorems **and** predicates) → proof;
    `Type`-valued (structures **and** type-valued defs like `Rung`) → type;
    constructors stay constructors; everything else → term. -/
def classify (ci : ConstantInfo) : MetaM String := do
  match ci with
  | .ctorInfo _  => return "ctor"
  | .axiomInfo _ => return "AXIOM"
  | _ =>
    forallTelescopeReducing ci.type fun _ body => do
      match body with
      | .sort lvl => return (if lvl.isZero then "proof" else "type")
      | _ =>
        match ← whnf (← inferType ci.type) with
        | .sort lvl => return (if lvl.isZero then "proof" else "term")
        | _ => return "term"

/-- All constant names referenced in a declaration's type and value. -/
def constDeps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.foldConsts ({} : NameSet) (fun n acc => acc.insert n)
  match ci.value? with
  | some v => v.foldConsts s (fun n acc => acc.insert n)
  | none   => s

/-- Longest path to a root in the primary dependency DAG, with a cycle guard. -/
partial def computeDepth (g : NameMap (Array Name))
    (memo : IO.Ref (NameMap Nat)) (stack : NameSet) (n : Name) : IO Nat := do
  if let some d := (← memo.get).find? n then return d
  if stack.contains n then return 0
  let deps := (g.find? n).getD #[]
  let stack' := stack.insert n
  let mut best := 0
  for d in deps do
    let dd ← computeDepth g memo stack' d
    if dd + 1 > best then best := dd + 1
  memo.modify (·.insert n best)
  return best

def pad (n : Nat) (w : Nat) : String :=
  let s := toString n
  "".pushn '0' (w - s.length) ++ s

def rolePrefix : String → String
  | "type"  => "Ty"
  | "ctor"  => "c"
  | "proof" => "t"
  | _       => "d"

/-- Under B, the only surviving nesting is host-forced: a constructor under its
    inductive, a field/projection under its structure. Everything else flattens
    to a flat `Foam.<token>`. -/
def nestedParent? (env : Environment) (n : Name) (ci : ConstantInfo) : Option Name :=
  match ci with
  | .ctorInfo c => some c.induct
  | _ =>
    let p := n.getPrefix
    if isStructure env p && (getStructureFields env p).contains (Name.mkSimple (lastStr n))
    then some p else none

#eval show MetaM Unit from do
  let env ← getEnv
  -- 1. gather primaries
  let prims : Array (Name × ConstantInfo) :=
    env.constants.fold (fun acc n ci =>
      if isPrimary n then acc.push (n, ci) else acc) #[]
  let primSet : NameSet := prims.foldl (fun s p => s.insert p.1) {}
  -- 2. collapsed edges
  let mut g : NameMap (Array Name) := {}
  for (n, ci) in prims do
    let owners : NameSet := (constDeps ci).foldl (fun acc d =>
      if isFoam d then
        match ownerOf primSet d with
        | some o => if o != n then acc.insert o else acc
        | none   => acc
      else acc) {}
    g := g.insert n (owners.foldl (fun a x => a.push x) #[])
  -- 3. depths
  let memo ← IO.mkRef ({} : NameMap Nat)
  let mut rows : Array (Name × String × Nat) := #[]
  for (n, ci) in prims do
    let d ← computeDepth g memo {} n
    let role ← classify ci
    rows := rows.push (n, role, d)
  -- 4. canonical sort: (depth, name)
  let sorted := rows.qsort (fun a b =>
    if a.2.2 != b.2.2 then a.2.2 < b.2.2 else a.1.toString < b.1.toString)
  -- 5. per-role token assignment + role histogram
  let roleTotal := fun r => (sorted.filter (·.2.1 == r)).size
  let widths : List (String × Nat) :=
    ["type","ctor","proof","term"].map (fun r => (r, (toString (roleTotal r)).length))
  let widthOf := fun r => ((widths.find? (·.1 == r)).map (·.2)).getD 3
  -- pass A: assign every token, build the name→token map
  let mut idx : NameMap Nat := {}
  let mut tokenMap : NameMap String := {}
  let mut toks : Array (Name × String × Nat × String) := #[]
  let mut axioms : Array Name := #[]
  for (n, role, d) in sorted do
    if role == "AXIOM" then axioms := axioms.push n
    let i := ((idx.find? (Name.mkSimple role)).getD 0) + 1
    idx := idx.insert (Name.mkSimple role) i
    let token := rolePrefix role ++ pad i (widthOf role)
    tokenMap := tokenMap.insert n token
    toks := toks.push (n, role, d, token)
  -- pass B: compute the redacted qualified name (B-rule) and emit
  let mut lines : Array String := #[]
  for (n, role, d, token) in toks do
    let qname :=
      match env.find? n with
      | some ci =>
        match nestedParent? env n ci with
        | some parent =>
          match tokenMap.find? parent with
          | some ptok => s!"Foam.{ptok}.{token}"
          | none      => s!"Foam.{token}"
        | none => s!"Foam.{token}"
      | none => s!"Foam.{token}"
    lines := lines.push s!"{token}\t{role}\t{d}\t{n}\t{qname}"
  -- 6. write + summarize
  IO.FS.writeFile outPath (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"primaries: {prims.size}"
  IO.println s!"  type  : {roleTotal "type"}"
  IO.println s!"  ctor  : {roleTotal "ctor"}"
  IO.println s!"  proof : {roleTotal "proof"}"
  IO.println s!"  term  : {roleTotal "term"}"
  IO.println s!"  AXIOM : {axioms.size}  {if axioms.isEmpty then "(clean)" else toString axioms}"
  let maxD := sorted.foldl (fun m r => Nat.max m r.2.2) 0
  IO.println s!"max depth: {maxD}"
  IO.println "--- first 30 (canonical order) ---"
  for line in lines.toList.take 30 do
    IO.println line

end FoamInstrument
