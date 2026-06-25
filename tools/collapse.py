#!/usr/bin/env python3
"""Collapse the 51-module dark core into a single Foam.lean in strict token
order (depth, name) — the dependency DAG linearized, authored by no one.

Decls leave their files and land in one `namespace Foam`, sorted by the
deposit's canonical order. Scoped constructs are hoisted: `variable` blocks go
global (Lean includes each only in decls that reference it), the lone
sub-namespace (`Foam.Ty08`, Ledger) is dissolved by requalifying its decls,
`section`/`import` wrappers drop. Anonymous instances ride with the decl they
follow. Guard receipts collect at the end, where every name is defined."""
import re
from pathlib import Path

REPO = Path("/Users/isaac/dev/foam")

# qname -> (depth, original-name)  — the sort key source
byQname = {}
for line in (REPO / "tools/dictionary.tsv").read_text().splitlines():
    p = line.split("\t")
    if len(p) >= 5:
        byQname[p[4]] = (int(p[2]), p[3])

STARTER = re.compile(
    r'^(def |theorem |structure |inductive |class |abbrev |instance|partial |'
    r'noncomputable |@\[|/--|/-!|#guard_msgs|namespace |end|open |variable |section|import )')
DECL = re.compile(
    r'^(?:noncomputable\s+|partial\s+)*'
    r'(def|theorem|structure|inductive|class|abbrev)\s+([A-Za-z0-9_.\']+)')

def parse_blocks(text):
    blocks, cur = [], []
    for line in text.splitlines():
        if STARTER.match(line):
            if cur: blocks.append(cur)
            cur = [line]
        elif cur is not None:
            cur.append(line)
    if cur: blocks.append(cur)
    return blocks

variables = []          # distinct variable lines, first-occurrence order
decl_units = []         # (sortkey, [lines])  — decl + trailing anon instances
guards = []             # [docstring_line, #guard_msgs_line]

for f in sorted((REPO / "Foam").rglob("*.lean")):
    text = f.read_text()
    nsm = re.search(r'^namespace (Foam(?:\.\w+)?)', text, re.M)
    nsprefix = nsm.group(1) if nsm else "Foam"
    pending_doc = None
    for blk in parse_blocks(text):
        head = blk[0]
        if head.startswith(("import", "namespace ", "end", "section", "open ")):
            continue
        if head.startswith("/-!"):
            continue                                   # module prose, drop
        if head.startswith("variable "):
            if head not in variables: variables.append(head)
            continue
        if head.startswith("/--"):
            pending_doc = head ; continue              # holds for next #guard_msgs
        if head.startswith("#guard_msgs"):
            arg = head.split()[-1]                      # relative #print axioms arg
            if nsprefix != "Foam":
                sub = nsprefix[len("Foam."):]
                head = head[:-len(arg)] + f"{sub}.{arg}"
            guards.append((pending_doc, head)) ; pending_doc = None
            continue
        m = DECL.match(head)
        if m:
            name = m.group(2)
            qname = f"{nsprefix}.{name}"
            depth, origin = byQname.get(qname, (999, qname))
            rel = qname[len("Foam."):]                  # name relative to `Foam`
            if rel != name:                             # dissolve sub-namespace
                blk = [head.replace(name, rel, 1)] + blk[1:]
            decl_units.append([(depth, origin), blk])
        else:                                           # anonymous instance, attaches above
            if decl_units: decl_units[-1].append(blk)
            else: decl_units.append([(0, ""), blk])

decl_units.sort(key=lambda u: u[0])

out = ["namespace Foam", ""]
out += variables + [""]
for u in decl_units:
    for blk in u[1:]:
        out += blk
out.append("")
for doc, gm in guards:
    if doc: out.append(doc)
    out.append(gm)
out += ["", "end Foam", ""]

(REPO / "tools/_collapsed.lean").write_text("\n".join(out))
print(f"decls: {len(decl_units)}  guards: {len(guards)}  variables: {len(variables)}")
print(f"lines: {len(out)}")
