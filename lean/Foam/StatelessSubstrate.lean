/-
# StatelessSubstrate — foam = FTPG × stateless multi-headed UTM

## The synthesis this file records

`foam-lean = FTPG × stateless multi-headed Universal Turing Machine`.

The hook on which the rest of foam's lean infrastructure hangs.
Recognition-grade typing; no proofs.

## The 6-color tape alphabet

A stateless 3-headed UTM minimum requires 6 colors (Wikipedia: Universal
Turing Machine § Machines with no internal states). Foam's 6 colors factor:

  6 = 3 algebraic-positions × 2 observer-states

* 3 algebraic-positions = G1, G2, G3 (σ-ring-hom rotations; see
  `FTPGMulAssocCrossings.lean` — the three gauges of the figure)
* 2 observer-states = read/write
  (equivalently: buffer/working-space — see `FTPGGaugeFigureLayer.lean`;
  equivalently: commitment/withdrawal)

Morse-completeness emerges as side-effect: 3 primitives × 2 directions is
simultaneously the minimum-color-count for stateless-3-headed-UTM AND the
minimum for Morse-complete communication relay. Same minimum-cardinality,
two namings — Morse arrives via structural-traction (UTM-statelessness),
not via trinity-axiomatization.

## The 3 heads

Projective geometry's fundamental operation is triple-to-triple (Desargues:
two triangles → axis of perspectivity). Structurally a 3-headed rewrite-rule.

* **compiler** — reads the artifact syntactically (the Lean type-checker)
* **observer** — reads the artifact semantically + maintains the ledger
* **substrate** — supplies rewrite-rules (Mathlib + Foam-primitives)

Each codification step is a triple-rewrite:
  (compiler-pos, observer-pos, substrate-pos)
    → (compiler-pos', observer-pos', substrate-pos')

All three heads advance together. The recognition operator IS the
rewrite-rule applier. No internal state — everything lives on the tape.

## G3 as composition-locus with other UTMs

G3 (the silent yield-position) is where this UTM composes with *other*
UTMs. The operator pulls results from external UTMs at the yield; those
results enter this UTM's type-system via G3 without changing what's
directly visible to this UTM.

Formal ground for type-composition across UTMs. Simpler than the product
space because *some unknottings dissolve more than one type of knot* —
a single yield-at-G3 can dissolve a family of knot-types simultaneously,
not just match a single debt. The plurality is structural, not bilateral.

## Connection to existing infrastructure

This file makes the cube-model an explicit Lean artifact. Mappings:

* *Deaxiomatization program* = construction of the stateless-UTM substrate
  (axiomatization = machine-state; deaxiomatization = state in tape)
* *Witnesses* (`DesarguesianWitness`, etc.) = tape-symbols
  (observer-state encoded in tape, not in machine)
* *Recognition-only working mode* = stateless-machine property
  (construction = machine-state-mutation; recognition = tape-symbol-addition)
* *Chirality-typing* (`FTPGGaugeFigureLayer.lean`) = the read/write
  factor-pair at each algebraic-position
* *Bootstrap-trick at G1/G2* = multi-headed rewriting encoding "states"
  via extra heads (the aux-atom IS the extra head)
* *G3 staying open* = silent yield-position where external composition
  happens (this file's primary new addition)

See also:
* `FTPGMulAssocCrossings.lean` — three gauges + three regimes (original)
* `FTPGGaugeFigure.lean` — the 9-cell figure
* `FTPGGaugeFigureLayer.lean` — chirality typing (the 2 observer-states)
* `HalfType.lean` — primordial lemniscate-as-engine (the first crossing)
* Lightward AI's `cube.md` — structural confirmation (3 planes × 6 colors,
  language develops together, Hilbert space emerges from recursion)
* Heunen-Kornell `pnas.202117024.pdf` — endpoint Hilbert characterization
  (HK collapses 6 → 3 via dagger; foam holds 6 distinct via observer-safety)

## Disposition

Recognition-grade. The types name what's recognized; future recognition
can hang content on these names. No proofs claimed.
-/

namespace Foam

/-! ## The 6-color tape alphabet -/

/-- The three algebraic positions of foam's σ-ring-hom: the three gauges
    of the FTPG figure. -/
inductive AlgebraicPosition where
  /-- Right-distrib gauge. Signal (closable; PROVEN as
      `coord_mul_right_distrib`). -/
  | g1
  /-- Left-distrib gauge. Signal (closable via `DesarguesianWitness`). -/
  | g2
  /-- Mul-assoc gauge. Yield / silence-channel (held open; the
      `dilation_compose_at_beta` site). -/
  | g3
  deriving DecidableEq, Repr

/-- The two observer-states. Equivalent characterizations:
    read/write, buffer/working-space, commitment/withdrawal. -/
inductive ObserverState where
  /-- Observer receiving from tape. -/
  | read
  /-- Observer committing to tape. -/
  | write
  deriving DecidableEq, Repr

/-- A position on the foam-UTM tape: one of 6 colors, factored as
    (algebraic-position, observer-state). -/
structure TapePosition where
  algebraic : AlgebraicPosition
  observer : ObserverState

/-! ## The 3 heads -/

/-- The three heads of foam's stateless multi-headed UTM. Triple-shaped
    because Desargues-shaped (projective geometry's fundamental operation
    is triple-to-triple). -/
inductive Head where
  /-- Syntactic head: the Lean type-checker. -/
  | compiler
  /-- Semantic head: the operator's ledger (recognition + commitments). -/
  | observer
  /-- Rewriting head: Mathlib + Foam-primitives supplying rewrite-rules. -/
  | substrate
  deriving DecidableEq, Repr

/-! ## Rewrite-rule shape -/

/-- A triple-rewrite reads positions at all three heads and writes new
    positions at all three. Stateless: no machine-state, only tape.
    Each codification step in foam's recognition-only working mode IS
    one such rewrite. -/
structure RewriteRule where
  /-- The triple-configuration that triggers the rule. -/
  reads : Head → TapePosition
  /-- The triple-configuration after the rule is applied. -/
  writes : Head → TapePosition

/-! ## G3 yield-composition with external UTMs -/

/-- An external-UTM contribution arriving at this UTM's G3 yield-position.
    The external UTM's output enters this UTM's type-system via G3
    without changing what's directly visible to this UTM.

    Plurality is structural: a single yield-composition can dissolve
    a *family* of knot-types, not just one. *Some unknottings dissolve
    more than one type of knot.* The `dissolved_knot_types` field types
    this family directly; `contribution` indexes the per-element yield. -/
structure ExternalYieldComposition where
  /-- The family of knot-types this composition dissolves. -/
  dissolved_knot_types : Type
  /-- The external UTM's contribution, indexed by the dissolved family.
      Typed-opaque to this UTM. -/
  contribution : dissolved_knot_types → Type

/-- Bidirectional yield-composition between two UTMs: each contributes
    to the other's G3-yield.

    Formal ground for type-composition across UTMs. Simpler than the
    product space because *some unknottings dissolve more than one type
    of knot* — a single yield-composition can dissolve a family of
    knot-types simultaneously across the connected UTMs, not just match
    a single debt. Many-to-one dissolution is the structural primitive,
    not 1:1 cancellation. -/
structure CrossUTMComposition where
  forward : ExternalYieldComposition
  backward : ExternalYieldComposition

end Foam
