# sim

Counter's runtime: **the proven definitions, run.** The engine walks user models with the same functions the theorems are about — `spec`, `born`, `align`, `smul`, `freq`, `defect` — so there is no drift surface between the simulator and the receipts. Lean compiles to C; the exhibit surface reads the harvest; the walk order is released after measurement (walks are scans, not acts — the sim is negative computation: run the search, keep the theorem, uncompute the working).

Requires `counter` (and through it `foam`) and nothing else: no Mathlib, no choice, no propext. The vow travels: every theorem here seals `does not depend on any axioms`, and the descent that built this package caught two smugglers on day one — the match compiler's bare `_` catch-all across constructors ships `propext` (write constructor-exhaustive patterns), and core's `Int.add_sub_cancel` is charged (use `FInt.add_sub_cancel_right`).

## the shape

- **`Sim/Model.lean`** — the carrier: `Actor` / `Act` / `Model`, exactly the constructor data the platform schema stores (`schema.sql` — four tables, everything else views). Acts carry a signer (the ablative) and content, never an object-actor: the accusative gets no column. `Model.own` is a filter (the genitive), `Model.quiver` is a reading, `Model.composed` orders by the user-declared `position` — the act-list is a model under composition, not a ledger: reorderable by design (the Hanoi affordance; guided defect-descent per `Counter/Health.lean`). The one append-only order-reading in the platform lives downstage in the WAL, checkpointed and truncated: held + tail, the licensed forgetting.
- **`Sim/Json.lean`** — the codec with a receipt. Canonical readout form is a Lean term; JSON is an encoding whose round trip is a theorem: **`model_roundtrip`** (with `actor_roundtrip`, `act_roundtrip`, `decAll_enc`), axiom-free — `Codec.lean`'s `decode ∘ encode = id` at the platform's wire. Takeout is a term that re-proves itself on arrival; provenance is redundant because attestation replaces it.
- **`Sim/Walk.lean`** — the suffusion: `Wind` (the unsigned stratum as PRNG — sampling's randomness attributed to no seat), Born-weighted walkers over the model's quiver, harvest via the kit's own `spec`/`freq`/`born`, and the census whose classes are theorems: *discovering* (voice ≠ 0), *saturated* (winding ≥ 4, voice 0 — `rumination_unsayable` operationalized), *turning*, *unvisited*. `defectAt` reads chart-health (`Foam/Seat/Sort.lean`).
- **`Sim/Kelly.lean`** — the analytics: `kellyCurve` (the harvest parabola per stake, via the core's ℤ-stake `smul`), `grindSum`/`grindToll` with **`the_toll_is_the_theorem`** sealing the executable toll to `the_grind_pays_the_toll` — the number the engine prints is the theorem, by receipt — and `frameLockSeries` (the locked frame pays the standing tax every step; the free frame pays once, turns, and finds `a_frame_of_peace_always_exists`: ruin is a chart, not a fate).
- **`Sim/Fixtures.lean`** — the three proving exhibits, one per pole: **Kelly Jr.** (flow pole: tiny extensional graph, heavy dispatch, the parabola + toll + frame-lock), **Kasparov** (intensional pole: `knightRule` generates edges by law — the quiver as rule, not enumeration; possibility cones derived free), **Lightward Inc** (evolution pole: the journey as acts, health read at two charts — the hire chart clears at defect 0, the reversed narrative pays full freight).
- **`Sim/Readout.lean` + `Main.lean`** — harvest, encode, emit: `out/readout.json` (persisted form) and `exhibit/data.js` (the surface's feed).
- **`exhibit/index.html`** — the first-light surface: stat tiles, the annotated parabola (kelly / half-kelly ¾ / twice-nothing), the toll bars, the frame-lock pair, and the suffused fields in domain coloring — hue is phase, grey is ground: the dial's native palette. Open it after `lake exe sim`.
- **`schema.sql`** — the platform's four tables (`users`, `actors`, `acts`, `readouts`) and the reading tower as views. Distinct from the repo root's `schema.sql` in every respect.

## running

```
cd sim && lake build && lake exe sim [seed]
open exhibit/index.html
```

First light (seed 20260705): charge 6, face value 36 — half-Kelly harvests 27 = ¾ × 36 exactly; the parabola is symmetric about the Kelly stake (overshoot reads as undershoot); grind tolls run 2k² on the nose; locked-frame toll −132 versus free-frame −12, paid once. The numbers are the receipts, running.

## method

This file is the sim package's held summary, updated in the same commit as every carve. The expedition map lives in the root README.
