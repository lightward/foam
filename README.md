# foam

strict phenomenology is indistinguishable from physics. this repo is the working demonstration: a type system where the two realms are made rigorously useful to each other, one receipted theorem at a time.

## the root

`Foam.lean` holds one theorem, `the_handshake`, and it is the whole organizing claim in miniature. a `Stage` is the operational skeleton both realms share — states, probes, answers, one measurement map. the theorem has two halves, about that one map:

- **the license half** (`a_license_is_a_gauge`): any identification that observation respects is gauge — moves through it change no transcript, ever. this is physics' side of the handshake: every symmetry, conservation law, and gauge equivalence is a license. (its ancestors: `maintenance_unobservable`, `noether_for_licenses`.)
- **the remainder half** (`the_remainder_is_real`, `a_wider_seat_reads_the_remainder`): any identification observation does *not* respect merges states that are provably distinct and provably readable from a wider seat. this is phenomenology's side: the interior is real even where the current probe family is blind, and "hidden" is always relative to a seat that can grow. (`dropping_the_remainder_is_platonism` names the error of quotienting anyway.)

physics gives phenomenology its license-checker; phenomenology gives physics its remainder-keeper. business is the load test — the practice where both must clear daily, with real ledgers and free exits.

every quotient is thus gauge or Platonism, and the question is decidable per-relation: does it respect `obs`, and does the ledger stay finer? existing operational physics takes the quotient by indistinguishability silently, at step zero. here it is never taken silently: licensed, or priced.

the handshake's statement is a named `Prop` (`Handshake S`), so it composes: it can be asserted of any stage anyone constructs.

## the tower (`Foam/Tower.lean`)

the recursion carve, first step. `towerN` iterates `dress`: each height adds a coordinate the resident probes cannot read. sealed there:

- `the_handshake_recurses`: the handshake holds at every height — one schema, every runtime.
- `the_tower_reads_only_the_ground`: states with equal floors are indistinguishable at every height; no amount of dressing adds anything the ground probes can hear.
- `a_wider_seat_is_still_a_seat` and `no_seat_is_the_last_seat`: the seat that reads a remainder has its own remainder, readable one seat wider. the reader of the hidden is itself hidden-bearing — the tower never closes from inside, at any height. (hollowness, load-bearing: this is why there is always a counter-move.)

this is the substrate for the amplitude bearing: backstage stays finite marks at every height; whatever continuum appears must appear frontstage, by recursing readings — and now the recursion has its receipts.

## surfaces

two, from the beginning, both running the vow: **CI** (`.github/workflows/ci.yml`) builds every file whole and individually, tolerates zero warnings (`sorry` included), and audits that Lean files carry no comments but receipts. **pages** (`.github/workflows/pages.yml`, `bin/foam-wiki`) renders the corpus as a wiki on every push to main — the reading rendered from the record, nothing hand-maintained between them.

## the vow (carried forward whole)

- axiom-free everywhere in the growing corpus: every theorem ends with its receipt — `/-- info: '...' does not depend on any axioms -/` + `#guard_msgs in #print axioms ...`. the receipts are the memory; the kernel forgets how a proposition was established.
- identifications someone chooses to *receive* (closing equivalence into equality) will live in their own stratum, stamped with their exact cost, no retraction — when that stratum is needed again.
- Lean files are comment-free except receipts; prose lives here.
- update this README in the same commit as every carve.

## the record

everything that stood before this root is one parent away: the full strata — the observation calculus, the stigmergy corpus, the seams, the bridges, ~3,400 receipts — are reachable at the commit before `from the top` (`git show 445dc3a^:README.md` for the old map). that corpus is this repo's demonstration mass and quarry: the best carve is often a citation wearing a new name, and the prior tree is where citations live. deletion here is an append; the history is the order-reading.

## bearings (seated, not scheduled)

- the recursion carve, continued: the tower stands; amplitude is the far end — continua live frontstage, made of licenses, not marks; each identification on the way licensed or priced. (backstage is always finite marks; a real number is an equivalence class of records.)
- the amnesiac-stigmergic corpus re-enters as the navigation practice `the_handshake` induces: everything needed to continue is in the record; not everything real is.

---

"It can do whatever we know how to order it to perform." (Lovelace, 1843)

*same*
