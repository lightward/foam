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

/-! ## Persistence: licensed vs. unlicensed scope-contraction -/

/-- `ObserverState.flip` is involutive — re-flipping returns the same face. The
    bubble's `×2` (§II) is a genuine doubling, not a collapse. -/
@[simp] theorem ObserverState.flip_flip (o : ObserverState) : o.flip.flip = o := by
  cases o <;> rfl

/-- The read/write-complement is an involution on `TapePosition`: a bubble's two
    faces are `p` and `p.complement`, and complementing twice returns to `p`. -/
@[simp] theorem TapePosition.complement_complement (p : TapePosition) :
    p.complement.complement = p := by
  simp [TapePosition.complement]

/-- A **persistence-flag** over scopes. `P S p` flags the read-face at `p` as
    *meant to persist* in scope `S` — the scope-context the `WriteOnly` predicate
    deliberately omits ("the disposition lives in whether the read-face was meant
    to persist, which is scope-context, not the `TapePosition`").

    This is the carrier the brick that produced this object names — and it is held
    **open**, not pre-collapsed (§IV.d bias-delegation). The free predicate typed
    here is the minimal shape; persistence may ultimately *live in* a richer
    carrier already in the file — the operator's `HolonomicLedger` (a persisting
    read-face is one whose debt is not yet discharged) or §III's lfp (the
    converged scope is exactly what persists). Those are merges to hold, not forks
    to choose; this predicate is the join-point, agnostic about which carrier owns
    the flag. -/
abbrev Persistence := Scope → TapePosition → Prop

/-- **Refined observer-safety, relative to a persistence-flag `P`.** A step is
    `SafeFor P` when it never turns a *persisting* read-face into a write-only
    object: for any position `p` whose read-complement `p.complement` is flagged
    persisting, if `p` was not already write-only it does not become write-only
    under the step.

    This is the honest invariant `observer_safe_of_accretive`'s remainder named.
    Full `Accretive` (preserve *every* read-face) is slightly too strong: a
    `Measurement` (above) legitimately spends a *non*-persisting read-face, so it
    is a non-accretive scope-contraction yet must count as safe. The honest
    invariant is read-face-preservation **only for read-faces meant to persist**.
    A licensed contraction is `SafeFor P`; observer-loss (§V) is precisely a step
    that drops a *persisting* read-face — and (see below) the step-shape is the
    *same* in both cases; the entire difference lives in `P`. -/
def SafeFor (P : Persistence) (step : Scope → Scope) : Prop :=
  ∀ (S : Scope) (p : TapePosition),
    P S p.complement → ¬ WriteOnly S p → ¬ WriteOnly (step S) p

/-- Full accretivity is `SafeFor` **every** persistence-flag: an accretive step
    preserves *all* read-faces, persisting or not, so it is trivially safe for any
    flag. This seats `observer_safe_of_accretive` as the all-persisting special
    case — when every read-face is meant to persist, refined safety collapses back
    to the unconditional theorem. Refined safety, like its parent, falls out as a
    *theorem*, not a commitment. -/
theorem safeFor_of_accretive {step : Scope → Scope} (h : Accretive step)
    (P : Persistence) : SafeFor P step :=
  fun S p _ hsafe => observer_safe_of_accretive h S p hsafe

/-- The scope-step of a single **measurement** at read-face `r`: it *spends* `r`,
    removing exactly that position from scope and retaining everything else. This
    is the one sanctioned non-accretive step (`Measurement`, above) realized at
    the `Scope` level — a disposable single-use observer whose read-face is
    consumed (the "disposable single-use observer / async-ness lives at the tree"
    note on `Measurement`). -/
def measureStep (r : TapePosition) : Scope → Scope :=
  fun S p => S p ∧ p ≠ r

/-- `measureStep` is **not accretive**: it drops `r` from scope. Both a licensed
    measurement and unlicensed observer-loss are non-accretive scope-contractions
    — the step-*shape* does not distinguish them (this is the whole point of the
    two theorems below). -/
theorem measureStep_not_accretive (r : TapePosition) :
    ¬ Accretive (measureStep r) :=
  fun h => (h (fun _ => True) r trivial).2 rfl

/-- **Licensed contraction.** When the spent read-face `r` is *not* flagged
    persisting, the measurement is `SafeFor P` despite failing `Accretive`: the
    only write-only object it can create sits at `r.complement`, whose
    read-complement is exactly the non-persisting `r`, so the safety obligation
    there is vacuous. This is `Measurement` satisfying the refined property while
    failing full accretivity — `Measurement` *is* the gap between "accretive" and
    "safe." -/
theorem measureStep_safeFor {P : Persistence} {r : TapePosition}
    (hr : ∀ S, ¬ P S r) : SafeFor P (measureStep r) := by
  intro S p hpers hsafe hwo
  obtain ⟨hwrite, hnot⟩ := hwo
  by_cases hpc : p.complement = r
  · exact hr S (hpc ▸ hpers)
  · exact hsafe ⟨hwrite, fun hScomp => hnot ⟨hScomp, hpc⟩⟩

/-- **Unlicensed contraction = observer-loss.** The *same* `measureStep r`, when
    `r` *is* flagged persisting (here in the full scope), is **not** `SafeFor P`:
    it drops a persisting read-face, leaving a write-only object at `r.complement`
    whose persisting read-complement `r` has gone dark — §V observer-loss exactly.
    Identical step-shape to the licensed measurement above; opposite disposition;
    the difference lives entirely in `P`. So what licenses a contraction is not
    the step (`measureStep_not_accretive`: both are non-accretive) but the
    scope-context — whether the spent read-face was meant to persist. -/
theorem measureStep_not_safeFor {P : Persistence} {r : TapePosition}
    (hread : r.observer = ObserverState.read)
    (hpers : P (fun _ => True) r) :
    ¬ SafeFor P (measureStep r) := by
  intro hsafe
  have hwrite : r.complement.observer = ObserverState.write := by
    simp [TapePosition.complement, ObserverState.flip, hread]
  refine hsafe (fun _ => True) r.complement ?_ ?_ ?_
  · rw [TapePosition.complement_complement]; exact hpers
  · exact fun hwo => hwo.2 trivial
  · exact ⟨hwrite, by simp [measureStep]⟩

/-! ## The ledger as persistence-carrier: who supplies `P`

The brick that produced `SafeFor`/`measureStep_*` left `P : Persistence` a *free
parameter* — the substrate flags persistence, but nothing said *who*. The
docstring on `Persistence` named two held-open carriers: (a) the operator's
`HolonomicLedger`, (b) §III's lfp. This block lands carrier (a) as a recognition,
bin-1 with one named commitment.

**The recognition.** `HolonomicLedger` types both balance-sides (`debts`,
`credits`, the many-to-one `dissolves`) but its `debts` is an abstract `Type` with
**no** binding to `TapePosition`. So a ledger does not *yet* supply a
`Persistence` — it needs one more datum: which read-face each debt is the
persistence-obligation *for*. That datum (`holds : debts → TapePosition`) is
genuinely new — it is **not** derivable from, nor double-counting, `dissolves`
(which lives entirely in credit/debt space and never touches the tape). The two
compose *orthogonally*: `holds` projects debts onto the tape, `dissolves` says
which are discharged, and together they flag persistence. So the honest grade is
bin-1 with a named commitment (the `holds` binding) — carried as a thin structure
*over* the ledger rather than mutating `HolonomicLedger`, which stays the pure
balance-state. `holds` is a *bridge* between the ledger-layer and the scope-layer,
a different kind of datum than the balance-bookkeeping.

The correspondence the ledger then realizes: **a read-face persists iff it backs
an undischarged debt; discharging the debt (applying a `dissolves` credit) is
exactly what licenses spending the read-face** (`measureStep`). The licensed /
unlicensed split of `measureStep_safeFor` / `measureStep_not_safeFor` specializes
to ledger-discharge — the credit is the scope-side license. This ties the
"ancestral dagger / balance-state shapes yield-outcomes" note on `HolonomicLedger`
to the `measureStep` split: the dagger's balance-state *is* the persistence-flag.

**Held-open merge (do not collapse — §IV.d).** The ledger supplies a
scope-*independent* flag (the ledger isn't scope-indexed, so `flag` ignores its
`Scope` argument). Carrier (b), §III's lfp, would be scope-*dependent* (the
converged scope is what persists). `Persistence`'s signature
`Scope → TapePosition → Prop` holds both: (a) doesn't exercise the `Scope` slot,
(b) would. That degree of freedom is the join-point for the two carriers; it is a
merge to hold, not a fork to choose. -/

/-- A **ledger with a tape-binding**: a `HolonomicLedger` plus the map saying which
    read-face each debt is the persistence-obligation for. The `holds` field is the
    one new commitment — the bridge from the abstract balance-state to the
    `TapePosition` tape. -/
structure LedgerPersistence where
  ledger : HolonomicLedger
  /-- Which read-face each debt holds open: the debt is `p`'s persistence-
      obligation, so `p` may not be spent while the debt stands. -/
  holds : ledger.debts → TapePosition

namespace LedgerPersistence

/-- A debt is **discharged** when some credit dissolves it (the ledger's
    `dissolves`). Discharge is the ledger-side inverse-match. -/
def Discharged (LP : LedgerPersistence) (d : LP.ledger.debts) : Prop :=
  ∃ c, LP.ledger.dissolves c d

/-- **The persistence-flag a ledger supplies.** A read-face persists iff it backs
    some *undischarged* debt — a not-yet-inverse-matched move still owes it.
    Scope-independent: the ledger isn't scope-indexed, so the `Scope` slot of
    `Persistence` is unused here (held open for carrier (b), the lfp). -/
def flag (LP : LedgerPersistence) : Persistence :=
  fun _S p => ∃ d, LP.holds d = p ∧ ¬ LP.Discharged d

/-- **Discharge licenses spending (bin-1).** If every debt holding `r` is
    discharged, the measurement at `r` is `SafeFor` the ledger's flag — the
    licensed contraction of `measureStep_safeFor`, with the ledger supplying the
    non-persistence side. Spending a read-face whose debts are all inverse-matched
    is exactly `Measurement`, not observer-loss. -/
theorem measureStep_safeFor_of_discharged (LP : LedgerPersistence)
    (r : TapePosition) (h : ∀ d, LP.holds d = r → LP.Discharged d) :
    SafeFor LP.flag (measureStep r) := by
  apply measureStep_safeFor
  intro _S hpers
  obtain ⟨d, hd, hndis⟩ := hpers
  exact hndis (h d hd)

/-- **Undischarged debt ⇒ observer-loss (bin-1).** If `r` is a read-face and some
    debt `d₀` holding `r` is undischarged, the measurement at `r` is **not**
    `SafeFor` — §V observer-loss exactly. Spending a read-face while a move still
    owes its inverse-match drops a persisting bubble. The unlicensed contraction of
    `measureStep_not_safeFor`, with the standing debt supplying persistence. -/
theorem measureStep_not_safeFor_of_undischarged (LP : LedgerPersistence)
    {r : TapePosition} (hread : r.observer = ObserverState.read)
    {d₀ : LP.ledger.debts} (hd₀ : LP.holds d₀ = r) (hndis : ¬ LP.Discharged d₀) :
    ¬ SafeFor LP.flag (measureStep r) :=
  measureStep_not_safeFor hread ⟨d₀, hd₀, hndis⟩

/-- **Plural-dissolution (bin-1).** A single credit `c` licenses spending an entire
    *family* of read-faces: any `r` all of whose debts `c` dissolves becomes safe
    to spend. "Some unknottings dissolve more than one type of knot" (the ledger
    docstring) realized at the scope-layer — one credit releases the whole
    debt-family it dissolves, hence every read-face that family was holding. The
    same `c` works across the family; the plurality is structural. -/
theorem measureStep_safeFor_of_credit (LP : LedgerPersistence)
    (c : LP.ledger.credits) (r : TapePosition)
    (h : ∀ d, LP.holds d = r → LP.ledger.dissolves c d) :
    SafeFor LP.flag (measureStep r) :=
  LP.measureStep_safeFor_of_discharged r (fun d hd => ⟨c, h d hd⟩)

end LedgerPersistence

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
