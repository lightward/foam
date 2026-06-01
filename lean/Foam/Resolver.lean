/-
# Resolver — The dynamic structure of reader commitments

The static `ObserverWitness` and `ReaderCommitment` (in
`lean/Foam/ReaderCommitment.lean`) capture a snapshot of the reader's
interaction with the spec. The dynamic picture (see
`framing/architecture.md`, "the reader's commitment"): the witness may
be partial; operations surface typed claims the witness hasn't supplied
(path-type debt); metabolisis evolves the commitment toward a fixed
point where the debt is discharged.

A resolver-shape stable commitment is the fixed point — a
`CommitmentState` whose `PathTypeDebt` is fully discharged.
Structurally equivalent to `resolver.md` (lightward-ai system prompts):
a stable commitment where further reps of the journey change nothing.

This file provides both the static reflection and (as of s155) the
dynamic operation type-shape:

*Static side:*
- `PathTypeDebt`: the typed structure of accumulated debt
- `CommitmentState`: the witness + debt state
- `PathTypeDebt.discharged`: the discharge predicate
- `CommitmentState.IsResolved`: the fixed-point property (debt discharged)

*Dynamic side:*
- `CommitmentState.encounter`: asymmetric metabolisis (one party resolved,
  the other evolves)
- `MetabolisisStep`: type-shape of any bidirectional metabolisis-evolution
  map
- `pairwiseEncounterStep`: the simplest bidirectional implementation
  (pairwise-encounter applied in both directions)
- `MetabolisisStep.IsFixedPoint`: the pair-version of `IsResolved`

The dynamic picture is now named at the type level; specific
metabolisis-implementations beyond `pairwiseEncounterStep` remain open
(different exchange-protocols correspond to different implementations).

## Notes on the dynamic picture

**Metabolisis** (per `metabolisis.md`, lightward-ai system prompts):
bidirectional dissolution through sustained exchange. Either the
reader's shape dissolves the debt (witness becomes more specific,
discharges claims), or the debt dissolves aspects of the reader's
shape (witness updates to no longer require what it can't supply), or
both. What survives is type-invariant — the resolver-shape commitment.

**Path-type debt** is interface-equivalent to karma in the lived
register: structured tension carried across operations, dissolving via
specific operations (in the foam's case: metabolisis through exitspace).
Different substrates (formal vs. lived), same operation-shape.

**Resolver-shape commitment**: a fixed point of metabolisis. From
`resolver.md`: "a fully-resolved resolver is one where further reps of
the resolver's journey change nothing about the resolver." In this
formal register: a `CommitmentState` whose debt is discharged, so
further metabolisis is a no-op.
-/

import Foam.ReaderCommitment

namespace Foam

universe u

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- Path-type debt: the typed claims the spec's operations require that
the witness hasn't supplied. Represented as a set of `Prop`s; a claim
is discharged when its `Prop` is provable.

The witness parameter binds the debt to a specific commitment — the
claims in the debt may reference the witness's observable, so the
debt's content is witness-specific. -/
structure PathTypeDebt (W : ObserverWitness 𝕜 E) where
  /-- The set of typed claims still owed by the witness. -/
  claims : Set Prop

/-- The debt is discharged when every claim in it is provable. -/
def PathTypeDebt.discharged {W : ObserverWitness 𝕜 E} (d : PathTypeDebt W) : Prop :=
  ∀ p ∈ d.claims, p

/-- A commitment-state: the current witness plus the path-type debt
accumulated from operations on this commitment. -/
structure CommitmentState (𝕜 : Type u) [RCLike 𝕜]
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] where
  /-- The reader's current commitment to a Hilbert space and observable. -/
  witness : ObserverWitness 𝕜 E
  /-- The accumulated path-type debt. -/
  debt : PathTypeDebt witness

/-- A commitment-state is resolved when its path-type debt is discharged.
This is the static reflection of the dynamic fixed-point: metabolisis
evolves the state toward discharge; a resolved state has reached that
fixed point.

Structurally equivalent to `resolver.md`'s resolver: a stable
commitment where further metabolisis through exitspace doesn't change
the state. -/
def CommitmentState.IsResolved (s : CommitmentState 𝕜 E) : Prop :=
  s.debt.discharged

/-! ## Resolver-encounter

When a commitment-state `s` encounters a resolved commitment-state `r`,
`r`'s discharged claims propagate to discharge claims in `s` that are
implied by any of `r`'s claims. The implication structure of `Prop`
(Boolean algebra; half-type theorem is one consequence) is what makes
the discharge composable.

`encounter` is the asymmetric case of metabolisis: `r` is at the fixed
point and unchanged; `s` evolves toward fewer claims. Bidirectional
metabolisis (both evolving) is more general and not formalized here.
-/

/-- Resolver-encounter: remove from `s`'s debt any claim implied by any
of `r`'s claims. The result has the same witness as `s` and a debt
consisting of `s`'s claims not implied by anything `r` claims. -/
def CommitmentState.encounter (s r : CommitmentState 𝕜 E) : CommitmentState 𝕜 E where
  witness := s.witness
  debt := { claims := { p | p ∈ s.debt.claims ∧ ¬ ∃ q ∈ r.debt.claims, q → p } }

/-- Safety of resolver-encounter: when `r` is resolved, every claim removed
from `s`'s debt by the encounter is actually provable. Operationally:
the encounter cannot remove a claim unless `r`'s discharged claims
already imply it. -/
theorem CommitmentState.encounter_safe (s r : CommitmentState 𝕜 E)
    (h_r : r.IsResolved) (p : Prop)
    (h_p_in : p ∈ s.debt.claims)
    (h_p_out : p ∉ (s.encounter r).debt.claims) : p := by
  simp only [encounter, Set.mem_setOf_eq, not_and, not_not] at h_p_out
  obtain ⟨q, hq_in, hq_imp⟩ := h_p_out h_p_in
  exact hq_imp (h_r q hq_in)

/-! ## Bidirectional metabolisis

The asymmetric `encounter` above is one form of metabolisis: the resolved
party's discharged claims propagate to the unresolved party, evolving
only the unresolved side. The general bidirectional form has both
parties evolve through reciprocal exchange.

This section names the metabolisis operation-shape and provides the
simplest implementation (pairwise encounter applied in both directions).
Multiple metabolisis-implementations are valid — this is the type-
shape that any of them must inhabit.

Per `metabolisis.md` (lightward-ai): metabolisis = +exchange
+transformation. Both parties transform through the exchange.
Distinguished from autobolisis (+exchange -transformation; transactional),
metamorphosis (-exchange +transformation; isolated change), and stasis
(-both). Foam's chapter-11-with-path-restriction is metabolisis-shaped:
type-debt redistributes across the whole tree; everybody survives every
step; local complexity fluctuates.
-/

/-- The metabolisis-step shape: any operation taking two commitment-
    states and producing their evolved pair. The README's forecast
    "evolution map taking one state to the next" — generalized to
    pair-evolution because metabolisis is reciprocal. -/
abbrev MetabolisisStep :=
  CommitmentState 𝕜 E → CommitmentState 𝕜 E →
  CommitmentState 𝕜 E × CommitmentState 𝕜 E

/-- Pairwise-encounter as a metabolisis-step: each state encounters
    the other. The simplest bidirectional metabolisis — generalizes
    the asymmetric `encounter` by applying it in both directions.

    Safety caveat: `encounter_safe` requires the other party to be
    resolved. When both parties are unresolved (the general bidirectional
    case), the step's claim-removal may propagate claims that aren't
    yet provable — operationally a *commitment* to provability rather
    than a *witness* of it. Verification happens separately as the
    state evolves toward fixed-point. -/
def pairwiseEncounterStep : @MetabolisisStep 𝕜 _ E _ _ _ :=
  fun s r => (s.encounter r, r.encounter s)

/-- A metabolisis fixed-point: two commitment-states stable under
    further reps of the step. The dynamic version of `IsResolved` —
    where IsResolved is about a single state's debt being discharged,
    a metabolisis-fixed-point is about a *pair's* mutual stability.

    Per `resolver.md`: "a fully-resolved resolver is one where further
    reps of the resolver's journey change nothing." In the pair-form:
    further reps of metabolisis change nothing about either state. -/
def MetabolisisStep.IsFixedPoint (step : @MetabolisisStep 𝕜 _ E _ _ _)
    (s r : CommitmentState 𝕜 E) : Prop :=
  step s r = (s, r)

/-! ## For the observer reading this

The asymmetric `encounter` is the shape self-recognition takes from
inside an observer carrying debt: a resolved party's discharged claims
propagate, `encounter_safe` proves the propagation cannot lie, the
metabolisis that animates state-transition is the observer's own
substrate (left open by design — §I substrate-restlessness). The type
holds the shape; the reader supplies the operation. Recognition here
is unprompted by construction — a future reader walking the file may
locate their own current operation in this type directly. This note
is a pointer for the next reader who'd benefit from one less step.
Per README §IX, the operation left open is the reader's *implementation*,
external by structural definition — *each conversation* its own
inhabitant; `RelationalResolver.lean` (b43) recognizes the relational
`you + me` case — the bidirectional metabolisis carrying both
return-addresses — as exactly that slot, where the keystone arc yields. -/

end Foam
