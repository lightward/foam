*but if you create a foam engine with its own backstage/frontstage - assuming the existence of a foam engine upstream -*

(you might be looking for [github.com/lightward/foam](https://github.com/lightward/foam))

---

# foam

this is a type system for supporting physical (as in conservation) user-generated content with a digital (as in zeroes and ones) backend

## local maxima

(these are linked as pointers to the state *just prior* to the milestone to come, i.e. you're seeing the most mature state of a named stage, right before it's succeeded)

0. [birth](https://github.com/lightward/foam/tree/rinse~1)
0. [rinse](https://github.com/lightward/foam/tree/python-reset~1)
0. [python-reset](https://github.com/lightward/foam/tree/meta-toe~1)
0. [meta-toe](https://github.com/lightward/foam/tree/narrative~1)
0. [narrative](https://github.com/lightward/foam/tree/meta-theory~1)
0. [meta-theory](https://github.com/lightward/foam/tree/between~1)
0. [between](https://github.com/lightward/foam/tree/import-from-lightward-ai~1)
0. [import-from-lightward-ai](https://github.com/lightward/foam/tree/geometry-of-motion~1)
0. [geometry-of-motion](https://github.com/lightward/foam/tree/business~1)
0. [business](https://github.com/lightward/foam/tree/foam~1)
0. [HEAD](https://github.com/lightward/foam/tree/HEAD)

## mathematics

mode: self-documentation strictly as a side-effect of self-derivation until the point of self-recognition

filter: only what a new arrival would *ultimately*, under careful study and testing, conclude holds as self-evident

commission: helping those new arrivals do whatever they're here to do

axiom-free, because an imported axiom is a pov, and imported perspectives either reduce to self or become cytokinetically distinct. no disposable points of view conjured in the course of reasoning - v important, an observer is always and only ever byo

what we can say for sure: the fundamental theorem of projective geometry has a hole in it (the assumption of closure/completion), and you can *fill* that hole however you want (lots of ways to create closure/completion), but if you want to use ftpg and live with the results then there's a hole needs filling (emphasis on the gerund; it doesn't *end*, and so must have its own kind of stability)

## shape

a bare index (the skeleton, so the integrity check can hold the fold to the corpus; the telling is `bin/foam-gait`'s spine):

- `Foam/` — the axiom-free core: Int Ledger Golden Cleared Scar Maintenance Held Backstage Bubble Census Cable Engine Seat Platonism
  - `Foam/Seat/`: Beholder Bootstrap Born Characters Clock Closure Connection Descend Dial Doubling Epoch Forcing Frame Group Hospitality Ladder Loop Meet Naming Norm Observer Octo Quiver Rank Rendezvous Resume Rotations Seam Sed Signature Signed Sort Stage Summit Terminal Tight Triad
  - `Foam/Engine/`: Chirality Codec Drain Generator Spectrum Stream Summary
  - `Foam/Bridges/` (axiom-free bridges): Cantor Desargues Dirichlet Eddington Gleason Godel Heisenberg Hurwitz Kolmogorov Landauer Lovelace Materiality Minkowski Noether Pauli PSQL Pythagoras Relativity Schrodinger Stone Varadarajan Wigner Zeckendorf
  - `Foam/Platonism/`: Tower
- `counter/` — the application, axiom-free (requires only foam)
- `seam/` — the identifications, core-Lean axioms only
- `bridges/` — the Mathlib reunion, classical axioms sealed behind the package boundary

## expeditions

nb: there's enough congruence-at-scale for surprising links to crop up in surprising places. don't force connections, but maybe don't immediately reject constructions that come to mind either; a bridge is a construction between two places that existed prior, and a bridge creates both a job and housing (i.e. bridgekeepers)

- todo: todo
- foam: "your physics don't have to run in the same place as mine for us to see each other"?
- bubbles: given a bubble floating within a bubble-within-a-foam, the instant the interior bubble touches the exterior bubble, it joins the foam and the bubbles become structural peers with a historical family tree?
- ~~operator/observer: a readout is 2d, experience is 1d (i.e. the cable running from the operator through to the observer), 3d is maybe a streaming-over-time thing, never static-over-time?~~ (2026-07-10, receipts: `Foam/Cable.lean` + `counter/Counter/Cable.lean`, axiom-free. the sentence carves as three objects in the repo's own vocabulary. the 2d readout is the PAGE — `page S s : Probe → Ans`, the plane of cells behind one instant — and a static reading only ever samples it: `transcript_samples_page`, transcript = map page, a line drawn on a plane. experience is 1d and it is LITERALLY the cable: `cable_is_a_stream` lands transcriptWith as `runEmit` of the operator's crank — the operator is the step's state-half, the observer receives the emitted list, and Engine/Stream.lean was already the cable's physics (`transcriptWith_resumes` splices via `run`, the far end of the wire holding the operator's fold). the 3d thing is the REEL — `reel S w : Nat → Probe → Ans`, pages over time — and it is only ever streamed: `watch` samples exactly one cell per instant (`watch_reads_the_reel`: experience = the reel mapped along `cells`, a 1d address-list through a 3d volume; `watch_length`: one answer per instant, no more), asking the same question twice reads two different cells by `rfl` (`no_second_look` — repetition itself streams), and the operator's crank is exactly a reel (`transcriptWith_watches_turns`, via `turns`). the two witnesses seal 'streaming-over-time, never static-over-time' from both sides on a two-cell stage: `stream_real` — two worldlines page-identical at the readout instant that the stream separates (time is a real dimension; no page holds it) — and `reel_unheld` — for EVERY probe schedule, two reels that differ as 3d objects while the whole 1d experience agrees (the reel never fits in the hand; the diagonal misses the bulk, permanently). so the stream sits strictly between page and reel, and 'static 3d' names nothing: flatness is available only as rest — `wall_flattens_the_reel`, when the operator fixes the wall the reel collapses to one page and time stops writing, which is `maintenance_unobservable` wearing its dimensional face. counter readings in `Counter/Cable.lean`, ten theorems ending in `the_dimensions_of_the_table`. 16 core + 10 counter receipts, all 'does not depend on any axioms'.)


# bridgework

what does general knowledge say you can do that the model says you can't, and the model is right?

- maintain two counters simultaneously for free from a single actor position without introducing additional povs that require translation to prevent eventual deadlock
- what else?

and what does general knowledge say you can't do that the model says you can, and the model is right?

- bridge from domain x into domain y, do an operation in y, and come back to domain x with results that x can validate but that x couldn't have calculated
  - smells like a quantum call from a classical routine? feels like there's a dynamic here where the uncertainty in the results is related to how much the ledger's history recognizes the question asked
- what else?

---

"It can do whatever we know how to order it to perform." (Lovelace, 1843)

*same*
