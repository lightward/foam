#!/usr/bin/env python3
"""foamcore sponsorship, at the constant: every thing in core must be
eventually a dependency of something a mind is doing.

isaac's ruling, 2026-07-24, tightened the same day it landed: core is the
lumenal content of the shared overlap of every mind's spotlight. a core
constant is sponsored if it lies in the dependency cone of the set of
constants that minds' deposits cite -- cited directly, or used
(transitively) by the proof or definition of something cited. the sponsor
needn't be a power user; they just have to be someone who asked a question
core hadn't noticed yet.

GRANDFATHERED lists constants that predate the ruling and await either a
sponsoring flight or a considered countermove. it may only shrink; when a
listed constant enters some mind's cone the audit fails until the list is
trimmed, so healing is recorded in the commit where it happens.

citation detection is textual (token match), which over-approximates
gently; the fail direction is under-sponsorship, which this never causes.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))

GRANDFATHERED = {
    # Foam/Measure.lean -- mass pair claimed by shannon 2026-07-24; the
    # aggregation pair awaits gauss, whose gloss walks it by name
    "Foam.aggregation_reads_the_reading",
    "Foam.measure_lives_frontstage",
    # Foam/Log.lean -- the epitaph path, claimed by boltzmann 2026-07-24
    # Foam/Lap.lean -- racemate trio claimed by pasteur 2026-07-24 (trim
    # recorded one commit late, at shannon's flight); the reversal waits
    "Foam.the_two_laps_are_reverses",
    # Foam/Portal.lean -- the positive half and capstone; isaac's entry
    # cites the no-translator half only
    # Foam/Roles.lean -- badge-blindness clause claimed by boltzmann 2026-07-24
    # Foam/Margin.lean -- the settle/deposit plumbing beyond hilbert's seals
    "Foam.a_deposit_moves_the_reading_by_one",
    "Foam.deposit",
    "Foam.the_decomposition_is_the_remainder",
    "Foam.the_margin_handshake",
    "Foam.the_settle_leaves_no_transcript",
    # Foam/Engine.lean -- demo engines and shims outside every cone
    "Foam.compassEngine",
    "Foam.twoWheels",
    "Foam.drain_chargeIn",
    "Foam.the_implementation_stays_backstage",
    "Foam.the_three_turns_undo",
    "Foam.the_turn_loses_no_state",
    # Foam/Tower.lean -- rfl-shims and recursion notes beyond the seals
    "Foam.a_wider_seat_is_still_a_seat",
    "Foam.the_ground_floor_is_the_stage",
    "Foam.the_handshake_recurses",
    "Foam.the_reading_descends",
    "Foam.the_tower_climbs_by_dressing",
    # Foam/Serving.lean -- the pair-refinement lemmas, uncited
    "Foam.the_pair_refines_the_other",
    "Foam.the_pair_refines_you",
    # Foam/Discovery.lean -- the continuum-license pair, uncited
    "Foam.pointwise_is_licensed",
    "Foam.the_approach_is_yours",
    # Foam/Surprise.lean -- path plumbing outside the sealed conjunctions
    # Foam/Countermove.lean -- the flip involution, uncited
    "Foam.every_move_carries_its_counter",
    # Foam/Contact.lean -- the dress identification, uncited
    "Foam.dress_is_contact_with_the_integers",
    # Foam/Amplitude.lean -- align outside current cones (the screen and
    # phase theorems are cited; their defs ride those blocks; add rides
    # the quaternion product since hamilton's after-flight)
    # Foam/Int.lean -- ground arithmetic not yet in any proof chain
    "Foam.FInt.add_sub_cancel_right",
    "Foam.FInt.mul_neg_one",
    "Foam.FInt.mul_sub",
    "Foam.FInt.neg_ofNat_add_ofNat",
    "Foam.FInt.neg_sub",
    "Foam.FInt.sub_add_cancel",
    "Foam.FInt.sub_mul",
    "Foam.FInt.sub_sub",
}

DECL = re.compile(r"^(theorem|def|abbrev|structure|inductive) (\S+)", re.M)
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def core_files():
    files = [os.path.join(ROOT, "Foam.lean")]
    foam_dir = os.path.join(ROOT, "Foam")
    for f in sorted(os.listdir(foam_dir)):
        if f.endswith(".lean"):
            files.append(os.path.join(foam_dir, f))
    return files


def parse(path):
    text = open(path, encoding="utf-8").read()
    m = re.search(r"^namespace (\S+)", text, re.M)
    ns = m.group(1) if m else ""
    blocks = {}
    chunks = re.split(r"(?m)^(?=(?:theorem|def|abbrev|structure|inductive) )",
                      text)
    for chunk in chunks[1:]:
        dm = DECL.match(chunk)
        if not dm:
            continue
        name = (ns + "." if ns else "") + dm.group(2)
        body = chunk.split("#guard_msgs")[0]
        blocks[name] = body
    return blocks


def main():
    blocks, home = {}, {}
    for path in core_files():
        rel = os.path.relpath(path, ROOT)
        for name, body in parse(path).items():
            blocks[name] = body
            home[name] = rel
    lookup = {}
    for full in blocks:
        lookup[full] = full
        for prefix in ("Foam.",):
            if full.startswith(prefix):
                lookup.setdefault(full[len(prefix):], full)
                bare = full.split(".")[-1]
                lookup.setdefault(bare, full)

    def resolve(tok):
        parts = tok.split(".")
        for end in range(len(parts), 0, -1):
            cand = ".".join(parts[:end])
            full = lookup.get(cand)
            if full is None and cand.startswith("Foam."):
                full = lookup.get(cand[len("Foam."):])
            if full:
                return full
        if len(parts) > 1:
            return lookup.get(parts[-1])
        return None

    def hits(text, skip=None):
        out = set()
        for tok in set(TOKEN.findall(text)):
            full = resolve(tok)
            if full and full != skip:
                out.add(full)
        return out

    deps = {name: hits(body, skip=name) for name, body in blocks.items()}

    cited = set()
    minds_dir = os.path.join(ROOT, "minds")
    for f in sorted(os.listdir(minds_dir)):
        if f.endswith(".lean"):
            text = open(os.path.join(minds_dir, f), encoding="utf-8").read()
            cited |= hits(text)

    reached, frontier = set(), sorted(cited)
    while frontier:
        name = frontier.pop()
        if name in reached:
            continue
        reached.add(name)
        frontier.extend(deps.get(name, ()))

    orphans = sorted(n for n in blocks
                     if n not in reached and n not in GRANDFATHERED)
    healed = sorted(n for n in GRANDFATHERED if n in reached)
    for n in healed:
        print(f"grandfathered constant now sponsored -- trim the list: {n}")
    if orphans:
        print("unsponsored core constants "
              "(in no mind's dependency cone):")
        for n in orphans:
            print(f"  - {n}  ({home[n]})")
        print("every thing in core must eventually be a dependency of "
              "something a mind is doing; seat the mind or list the debt.")
        sys.exit(1)
    total = len(blocks)
    print(f"sponsorship clean: {total - len(GRANDFATHERED)}/{total} core "
          f"constants in mind-cones, {len(GRANDFATHERED)} grandfathered")
    sys.exit(1 if healed else 0)


if __name__ == "__main__":
    main()
