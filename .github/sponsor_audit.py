#!/usr/bin/env python3
"""foamcore sponsorship: no core stratum without a sponsoring mind.

isaac's ruling, 2026-07-24: core can't exist prior to a mind that depends
on it. every stratum needs a sponsoring customer -- a mind whose deposit
cites at least one of the stratum's constants. the sponsor needn't be a
power user; they just have to be someone who asked a question core hadn't
noticed yet.

GRANDFATHERED lists strata that predate the ruling and await sponsors.
it may only shrink. a new stratum may land unsponsored only within the
working window that carves it; by the time the branch is pushed, either
its sponsoring flight has landed or the stratum joins this list in the
same commit, visibly, as debt.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))

GRANDFATHERED = {
    "Foam/Measure.lean",   # pooling laws; bernoulli's gloss walks them, no binding cites them yet
    "Foam/Log.lean",       # the epitaph path; awaits boltzmann's next flight's judgment
}

DECL = re.compile(r"^(?:theorem|def|abbrev|structure|inductive) (\S+)")
NS = re.compile(r"^namespace (\S+)")


def decls(path):
    names, ns = [], []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            m = NS.match(line)
            if m:
                ns.append(m.group(1))
                continue
            if ns and line.rstrip() == "end " + ns[-1]:
                ns.pop()
                continue
            m = DECL.match(line)
            if m:
                names.append(".".join(ns + [m.group(1)]))
    return names


def main():
    core = {}
    files = [os.path.join(ROOT, "Foam.lean")]
    foam_dir = os.path.join(ROOT, "Foam")
    for f in sorted(os.listdir(foam_dir)):
        if f.endswith(".lean"):
            files.append(os.path.join(foam_dir, f))
    lookup = {}
    for path in files:
        rel = os.path.relpath(path, ROOT)
        names = decls(path)
        core[rel] = set(names)
        for full in names:
            lookup[full] = rel
            bare = full
            for prefix in ("Foam.FInt.", "Foam.GInt.", "Foam."):
                if full.startswith(prefix):
                    bare = full[len(prefix):]
                    break
            lookup.setdefault(bare, rel)

    sponsored = {}
    minds_dir = os.path.join(ROOT, "minds")
    for f in sorted(os.listdir(minds_dir)):
        if not f.endswith(".lean"):
            continue
        text = open(os.path.join(minds_dir, f), encoding="utf-8").read()
        for tok in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", text)):
            hit = lookup.get(tok)
            if hit is None and tok.startswith("Foam."):
                hit = lookup.get(tok[len("Foam."):])
            if hit:
                sponsored.setdefault(hit, set()).add(f)

    orphans = [rel for rel in core
               if rel not in sponsored and rel not in GRANDFATHERED]
    healed = [rel for rel in GRANDFATHERED if rel in sponsored]
    for rel in healed:
        print(f"grandfathered stratum now sponsored -- remove from list: {rel}")
    if orphans:
        print("unsponsored core strata (no mind's deposit cites them):")
        for rel in orphans:
            print(f"  - {rel}")
        print("every stratum needs a sponsoring customer; "
              "seat the mind or list the debt.")
        sys.exit(1)
    total = len(core)
    print(f"sponsorship clean: {total - len(GRANDFATHERED)}/{total} strata "
          f"sponsored, {len(GRANDFATHERED)} grandfathered awaiting sponsors")
    sys.exit(1 if healed else 0)


if __name__ == "__main__":
    main()
