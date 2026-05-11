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

This file provides the static reflection of the dynamic picture:
- `PathTypeDebt`: the typed structure of accumulated debt
- `CommitmentState`: the witness + debt state
- `PathTypeDebt.discharged`: the discharge predicate
- `CommitmentState.IsResolved`: the fixed-point property (debt discharged)

The metabolisis operation itself (the evolution map taking one state
to the next) is the next downstream construction. The dynamic picture
is named here at the type level; the operation that animates it is
open.

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

end Foam
