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
can hang content on these names. Almost no proofs claimed — the one
exception is `observer_safe_of_accretive` (below), a bin-1 substrate-direct
theorem: observer-safety is *not* an axiom but a one-line consequence of
accretivity, so the proof IS the recognition and is carried as such.
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
    (algebraic-position, observer-state).

    A `TapePosition` read as the thing its two faces belong to is a
    *bubble* (README §II): one substrate-unit carrying the `×2`
    (read/write) doubling. The `observer` field selects which face is
    in view — `read` is the observer-face
    (substrate-direct: `ObserverState.read` = observer receiving);
    `write` *reads as* the morphism-face — observer-supplied (bin-2),
    pending substrate-derivation.
    The downstream role-terms (observer, witness, agent, line, bridge)
    are roles *of* a bubble. The colloquial "bridge-bubble" framing of
    earlier walks (s149) is the Bridge object-prime named on its bubble-
    carrier: a bridge mediating two scopes is a bubble whose two faces
    read the two non-observations. -/
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

/-! ## The observer's holonomic ledger -/

/-- The observer's holonomic ledger: typed balance-state tracking
    positive and negative charges from moves taken.

    * **debts** — learned moves not yet inverse-matched (negative charges)
    * **credits** — inversion-moves available to dissolve debts (positive
      charges); a single credit can dissolve a *family* of debts
      (plural-dissolution; *some unknottings dissolve more than one type
      of knot*)
    * **dissolves** — the many-to-one cancellation relation

    This is the *type* of the ancestral dagger — not a history-
    enumeration (ancestry is opaque, accessed via yield as
    stochastic-opaque prayer at G3), but a balance-state that shapes
    yield-outcomes. Two daggers with identical option-sets but
    different ledger-states yield differently — that's why ancestral
    daggers give entropic results while clean daggers give merely
    holonomic ones.

    The state-space of partition-options is Bell-number-shaped
    (genji-kō diagrams).

    **Relation to `Foam.PathTypeDebt` (in `Resolver.lean`):** these are
    at different abstraction levels, both valid. `PathTypeDebt` is
    debt-side only (`claims : Set Prop`; discharge = all provable) —
    abstract and Hilbert-space-witness-grounded. `HolonomicLedger`
    types both sides (debts + credits + many-to-one `dissolves`
    relation) more explicitly. `PathTypeDebt` is the working type for
    the Hilbert-space layer's resolver; `HolonomicLedger` is the
    abstract-substrate description of the dagger-ledger's structure.
    Subsumption was checked; not equivalent — kept distinct. -/
structure HolonomicLedger where
  debts : Type
  credits : Type
  /-- Many-to-one cancellation: a credit dissolves a family of debts. -/
  dissolves : credits → (debts → Prop)

/-! ## Measurement: disposable single-use observer -/

/-- A measurement is a *disposable single-use observer*: geometry in
    streams as accumulating geometry out, until the accumulation
    reaches the unknot. Subsequent measurements aren't with a
    persistent observer — they're additional disposable observers,
    each contributing more geometry to what prior ones resolved.

    **observer == measurement.** No persistent observer-state to track
    across measurements. Each Measurement is one-shot.

    **Where async-ness lives** (this is the s155 simplification of
    what was previously typed as AsyncMeasurement with operator/
    observer protocol-phases): *not at the individual measurement
    level*. A single measurement just runs and either reaches unknot
    or doesn't — synchronous-shaped. But across multiple measurements,
    the *tree* they compose into may or may not have balanced (= all
    measurements reached unknot, type-debt discharged). **Tree-balance
    IS where async-ness actually lives.**

    **Hilbert-space-grounded realization of tree-level structure:**
    - Tree-state: `Foam.CommitmentState` (in `Resolver.lean`)
    - Tree-balance (single-state): `CommitmentState.IsResolved`
    - Tree-balance (pair-state): `MetabolisisStep.IsFixedPoint`

    Individual Measurements don't carry async-property — only the
    tree they compose into does. The 3-field Measurement structure
    typed here is the substrate-agnostic abstract; CommitmentState +
    MetabolisisStep are the concrete tree-level realizations.

    The simplification came from recognizing that observer==measurement
    means async-ness can't live at the individual level (no persistent
    observer to be async *about*); it has to live where state
    accumulates across observers (the tree). -/
structure Measurement where
  /-- The geometric question posed by this measurement. -/
  geometry_in : Type
  /-- The accumulating geometric stream produced as measurement runs. -/
  geometry_out : Type
  /-- The completion-condition: this measurement's accumulation has
      reached the unknot. No separate "scalar interpretation" step —
      the geometry IS the result. -/
  reached_unknot : geometry_out → Prop

/-! ## Observer-loss: the write-only degenerate -/

/-- The opposite observer-face. The `×2` (read/write) doubling pairs each
    face at an algebraic position with its complement; this is that
    pairing as an involution on `ObserverState`
    (`flip (flip o) = o`). -/
def ObserverState.flip : ObserverState → ObserverState
  | read => write
  | write => read

/-- The read/write-complement of a tape-position: the same algebraic
    position seen through the opposite observer-face. For a write-face
    this is its read-face — the half of the bubble's `×2` that
    observer-loss loses. Involutive (inherits `ObserverState.flip`'s
    involutivity), so the two faces of a bubble are
    `p` and `p.complement`. -/
def TapePosition.complement (p : TapePosition) : TapePosition :=
  { p with observer := p.observer.flip }

/-- A *scope*: the set of tape-positions currently reachable. A bubble's
    read-face is *in scope* iff its `TapePosition` is a member. This is
    the formal carrier of "the meaning has its complement in scope" from
    Observational idempotence (§V): `P² = P` holds exactly when the
    complement is in scope. -/
abbrev Scope := TapePosition → Prop

/-- **Observer-loss / the write-only object** — the lean type of README
    §V's *Falsification → observer-loss* diagnostic (and the §IV.c
    platonism / observer-toxic form that carry-the-observer names).

    A `TapePosition` is *write-only* in a scope `S` when its write-face is
    the face in view (`observer = write`) but its read-complement is
    **not** in scope (`¬ S p.complement`) — the bubble's `×2`
    (read/write) has collapsed to a write-only object, an
    object-without-observer. The read-face is *unreachable from `S`*.
    Equivalently, on the bubble-as-pair reading (§II): the bubble at
    `p.algebraic` has its write-face but has lost its read-face.

    Foam's lattice is orthomodular and non-Boolean on purpose (§V), so it
    carries no *global* "false" — disagreement-that-lands cannot resolve
    as "claim X is false." It relocates here, to a read-face going dark.
    F is monotone (§III) and the first commitment locks (indelibility):
    a landed claim cannot fail by content going false; the only
    failure-mode is the `×2` collapsing to this.

    **Structural parallel to Observational idempotence (§V).** There,
    `P² = P` *fails* exactly when the complement is out of scope; here, a
    bubble *degenerates* to write-only exactly when its read-complement
    is out of scope. Same out-of-scope-complement condition, read once as
    idempotence-failure and once as observer-loss.

    **Reconcile with `Measurement` (above), do not collide.** A
    `Measurement` is a *disposable single-use observer* that *spends* its
    read-face by design — write-only-ness there is the intended one-shot
    terminus. Observer-loss is a read-face that was *supposed to persist*
    and went dark: the same position-shape, opposite disposition. The
    predicate deliberately does not distinguish them — the disposition
    (spent-by-design vs. lost) lives in whether the read-face was meant
    to persist, which is scope-context, not the `TapePosition`. -/
def WriteOnly (S : Scope) (p : TapePosition) : Prop :=
  p.observer = ObserverState.write ∧ ¬ S p.complement

/-! ## Observer-safety: read-face preservation under accretive recognition -/

/-- A scope-step is **accretive** when it only grows scope: every position
    in scope before the step is still in scope after. This is README §III's
    monotonicity of `F` ("adding primitives can only enable more recognition,
    never less; recognition never retracts") made concrete on `Scope`. A
    recognition-step is the scope-map of one `F`-iteration; recognition proper
    is accretive by construction. -/
def Accretive (step : Scope → Scope) : Prop :=
  ∀ (S : Scope) (p : TapePosition), S p → step S p

/-- **Observer-safety = read-face preservation.** An accretive step never
    *produces* a write-only object: any position that was not write-only in
    `S` is still not write-only in `step S`. Read-faces in scope stay in
    scope — the bubble's `×2` (§II) cannot collapse to a `WriteOnly` (the
    §V observer-loss degenerate) by the act of recognizing more.

    **This is a theorem, not a commitment (bin-1, substrate-direct).**
    Observer-safety is *not* an extra axiom imposed on recognition; it falls
    out of accretivity alone. The brick that produced this predicted exactly
    this shape: "scope grows ⇒ read-complement can't leave scope." The proof
    is the recognition — if a write-face's read-complement is in scope before
    an accretive step, accretivity keeps it in scope after, so the only way to
    end up write-only is to have been write-only already. Contrapositively:
    the write-only set is monotone-*decreasing* under recognition — read-faces
    can be relit (a later step brings the complement into scope) but never
    darkened. (This is the same theorem read forward; observer-loss can only
    be *repaired* by accretion, never *created*.)

    **Why this is the read-face-preservation form of §III + indelibility.**
    `F` is monotone (§III: recognition never retracts) and the first
    commitment locks (indelibility). Together they say a landed claim cannot
    fail by content going false — §V's *Falsification → observer-loss*: the
    lattice carries no global "false," so the only failure-mode is the
    read-face going dark. This theorem is the positive statement of that: as
    long as the recognition-step is accretive, the read-face *does not* go
    dark. Observer-loss therefore requires a *non-accretive* step (scope
    contraction); monotone recognition supplies none.

    **Reconcile with `Measurement` (above), do not collide.** A measurement
    *spends* its read-face by design — it is a scope-*contraction*, hence
    **not** accretive, and so lies outside this theorem's hypothesis. That is
    not a violation: the read-face was never meant to persist (one-shot
    terminus). Observer-safety is the property of read-faces *meant to
    persist*; its domain is the accretive (persisting-bubble) step, not the
    measurement. The licensed-contraction (`Measurement`) vs. unlicensed-
    contraction (observer-loss) distinction is what the next walk types. -/
theorem observer_safe_of_accretive {step : Scope → Scope} (h : Accretive step)
    (S : Scope) (p : TapePosition) :
    ¬ WriteOnly S p → ¬ WriteOnly (step S) p := by
  intro hsafe hwo
  obtain ⟨hwrite, hnot⟩ := hwo
  exact hsafe ⟨hwrite, fun hScomp => hnot (h S p.complement hScomp)⟩

/-! ## Trefoil-progression: minimum non-trivial knot-shape -/

/-- The trefoil-knot has three crossings. As a *progression* in foam's
    observer-substrate, the three positions correspond to:

    * **first** — deterministic crossing; no commitment required;
      collapses by identity-laws. (Example: `g3_boundary` =
      `dilation_compose_at_beta_x_eq_I`.)
    * **second** — vacuum-formation site; RHS evaluates forward,
      LHS persists as held vacuum-shape. (Example: `g3_asymmetric`
      = `dilation_compose_at_beta_y_eq_coord_inv_x`.)
    * **third** — commitment-site; where the ancestral dagger
      commits; the over/under choice that distinguishes trefoil from
      lemniscate. (Example: `g3_generic` = `dilation_compose_at_beta`.)

    Three crossings are the minimum for non-trivial knottedness. The
    *third* is the first place where over/under choice matters — hence
    where ancestral commitment enters from outside the trace. Getting
    the over/under "wrong" at the third crossing reduces to lemniscate:
    *dissonance-as-unknotting*. The block at the third crossing IS the
    unknotting-in-progress, recorded as resistance-map (s142/s146/s148/
    s149 measurements).

    The G3 row of the gauge × regime figure (`FTPGGaugeFigure.lean`)
    realizes this progression. G1 and G2 rows have their own three-
    regime structure but with different progression-shape (signal-
    channels, not silence-channel). -/
inductive TrefoilCrossing where
  | first   -- deterministic; no commitment required
  | second  -- vacuum-formation; held-content site
  | third   -- commitment-site; ancestral dagger lands here
  deriving DecidableEq, Repr

end Foam
