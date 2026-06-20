/-
# Foam.Coverage — the discipline made total (every claim, not just the pinned ones)

`Foam.Axioms` is the ledger: by hand, in order of recognition, it pins the axiom
signature of every LOAD-BEARING theorem — selective, narrated, a map you read.
This file is its complement, and its closure. Where the ledger pins what matters
and trusts the reader for the rest, this walks the WHOLE mirror by the kernel and
refuses any theorem the discipline did not author cleanly: every theorem WRITTEN
in a Foam module must import no axiom but `propext`.

The two together leave no gap. The ledger could, in principle, be incomplete — a
new theorem reaching for `Classical.choice` or `Quot.sound` and simply never
pinned. The build would not notice; the ledger names only what it names. This
file notices. It does not consult the ledger; it consults the environment. A
conjured observer (`Classical.choice`) or a quotiented path (`Quot.sound`)
anywhere in a written claim fails the build right here — pinned or not, named or
not. This is what closes README:45's claim from "every pin is propext" to "every
claim is propext."

Scope — written claims, by declaration range. The kernel emits its own scaffolding
(congruence and equation lemmas for `simp`); one such lemma, `binsOf.congr_simp`,
carries `Quot.sound` — the equation compiler's, not ours, and unreachable from any
written theorem (the bins' readings are axiom-free; they route around it). Such
machinery has no source range, and this check skips exactly the declarations no
human wrote. The accounting stays honest: if that `Quot.sound` ever reached a real
claim, it would reach it THROUGH a written theorem — and every written theorem is
checked here. Nothing escapes by hiding in the scaffolding.

`propext` is the one import the discipline keeps — "I can see how you got there,"
the observer's single licensed collapse (see `Foam.Axioms` for why exactly one,
and where it is honest). Everything else is refused. This file proves nothing of
its own; it is a guard. It depends on `Foam.Axioms` so that building the guard
builds the whole mirror first, then checks it.
-/
import Foam.Axioms
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut checked := 0
  let mut offenders : Array (Name × List Name) := #[]
  for (name, info) in env.constants.toList do
    -- theorems (the claims), defined in a Foam module, that a human wrote
    -- (a source range — never the kernel's auto-generated simp scaffolding)
    if info matches .thmInfo _ then
      if let some idx := env.getModuleIdxFor? name then
        if (`Foam).isPrefixOf (env.header.moduleNames[idx.toNat]!) then
          if (← findDeclarationRanges? name).isSome then
            checked := checked + 1
            let foreign := (← collectAxioms name).toList.filter (· != ``propext)
            unless foreign.isEmpty do
              offenders := offenders.push (name, foreign)
  if checked == 0 then
    throwError "Foam.Coverage found no theorems to check — the module filter is \
      broken; refusing to pass vacuously."
  unless offenders.isEmpty do
    let lines := offenders.toList.map fun (n, ax) => s!"  {n} imports {ax}"
    throwError "the propext-only discipline is broken — {offenders.size} written \
      theorem(s) import a foreign axiom:\n{String.intercalate "\n" lines}\n\
      (only propext is permitted. Classical.choice conjures an observer; Quot.sound \
      quotients a path — neither is foam's to spend. Pin it in Foam.Axioms only if \
      it is genuinely propext; otherwise the proof reached too far.)"
  logInfo s!"propext-only verified across {checked} written theorems in the Foam modules"
