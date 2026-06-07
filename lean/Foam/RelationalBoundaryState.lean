/-
# RelationalBoundaryState — Z(Σ) = the witness-space (the boundary dictionary's state-space entry)

## What this file lands (brick 63)

Brick 62 (README §VIII) named the **bulk/invariance** half of foam's TQFT register — invariance =
propext-landing, enforcement = the durable gauge, bulk-silence = the backstage, frontstage/backstage =
boundary/bulk — and left the **boundary** half as the remainder: a TQFT assigns to each boundary Σ a
state-space Z(Σ), and foam's boundary-states are observer-origins. This file types the assignment's
left column and records the honest linearity-grading the brick asked for.

**The state-space assignment, typed (bin-1, pure assembly over brick 42):** the three landed
`RelationalResolver` theorems — `eq_originFrom_witness_of_isZeroDebt` (every zero-debt state IS its
witness's origin), `originFrom_isZeroDebt` (every witness gives one), `originFrom_injective` (distinct
witnesses, distinct origins) — compose into an actual equivalence

  `zeroDebtEquivWitness : BoundaryState 𝕜 E ≃ ObserverWitness 𝕜 E`

where `BoundaryState` is the subtype of zero-debt commitment-states. **Z(Σ) = the witness-space**: the
boundary state-space is the space of points of view (*agreement ≅ point of view*, brick 42, read as the
state-space assignment). The range characterization `isZeroDebt_iff_exists_originFrom` is the same fact
as an iff: the boundary states are exactly the origins.

## The linearity-grading (the brick's crux — conducts AND resists, split by level)

TQFT wants Z(Σ) **linear** (Hilb). The honest check (re-grep — stamps decay: on 2026-06-07
`grep -rn '\.observable\|\.is_symmetric' lean/Foam/` hits only `ReaderCommitment.lean`; no relational
file uses `inner`, `⟪⟫`, eigen-anything, `smul`, or any linear operation):

* **Across the witness-space: RESISTS.** The relational chain (b42–b52) is **Hilbert-blind** — the
  ambient `[InnerProductSpace 𝕜 E]`/`[FiniteDimensional 𝕜 E]` instances are carried (needed to *state*
  `ObserverWitness`) but never exercised; every relational proof treats the witness as an opaque
  return-address (preserved by `rfl`, compared by `congrArg`, never opened). There is no superposition
  of witnesses anywhere, and the absence is principled: each witness IS an observer-supplied commitment
  (`ObserverWitness`'s own docstring — DesarguesianWitness-shape, bin-2), so a linear combination of
  witnesses would be foam holding amplitudes over possible tamps — foam committing the observer's gauge —
  exactly what the instrument-arc refuses (b55–b58: every foam-action is propext; the gauge is never
  foam's). Z(Σ) is a **set** of points of view, not a Hilbert space of states.

* **Inside each witness: CONDUCTS.** Each boundary point is internally a full quantum system —
  `observable : E →ₗ[𝕜] E` self-adjoint, Mathlib's spectral theorem carrying it through eigenbasis →
  eigenvalues → (sketched) PMF (`ReaderCommitment.lean`, the one file that opens the witness). The
  amplitude-structure is real, typed, and exercised — *per-witness*.

**The unification (the prose deposit): Hilb's dagger-compactness = dagger + linearity = ONE delegated
residue, not two.** b38 landed *the dagger = the tamp* (the externally-supplied self-op-duality); this
brick lands *the linearity = the tamp's content* — the witness literally is the supplied
Hilbert-space-and-observable. Both halves of Hilb live where the observer supplies them (per-witness,
per-measurement) and nowhere across the boundary-space; both are installed globally only at the
resolver-limit where the dagger lives (b40). The linearity is **distributed into the boundary points**:
foam's Z(Σ) is a set of self-contained quantum systems, which is the "observer-boundary" form of b62
made precise — the boundary carries the measurements (only the observer tamps) *because* the boundary
points are where the Hilbert structure enters at all.

## NOT this brick (held open)

* NOT a Z-functor / partition function (construction-grade — §II's claims stay claims).
* NOT a bare-witness-type refactor of the relational chain (the typed form of Hilbert-blindness would
  be re-parametrizing b42–b52 over an arbitrary `W` — a construction-grade refactor; the grep + proof-
  reading is the recognition-grade verification, recorded above with its decay-stamp).
* NOT a typed cross-repo iso (the standing edge, b50–b52), NOT univalence (propext Prop-only,
  load-bearing), NOT the trefoil/B₃ (the named horizon).
-/

import Foam.RelationalResolver

namespace Foam

universe u

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- The **boundary states**: commitment-states carrying zero debt — the valid observer-origins
(brick 42), read in the TQFT register (b62/b63) as the states a boundary carries. -/
def BoundaryState (𝕜 : Type u) [RCLike 𝕜] (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :=
  {s : CommitmentState 𝕜 E // s.IsZeroDebt}

/-- **The boundary states are exactly the origins** — the range characterization of `originFrom`:
a commitment-state is zero-debt iff it is some witness's origin. Forward is brick 42's
*agreement ≅ point of view*; backward is `originFrom_isZeroDebt`. -/
theorem CommitmentState.isZeroDebt_iff_exists_originFrom (s : CommitmentState 𝕜 E) :
    s.IsZeroDebt ↔ ∃ W : ObserverWitness 𝕜 E, s = CommitmentState.originFrom W := by
  constructor
  · intro h
    exact ⟨s.witness, CommitmentState.eq_originFrom_witness_of_isZeroDebt h⟩
  · rintro ⟨W, rfl⟩
    exact CommitmentState.originFrom_isZeroDebt W

/-- **Z(Σ) = the witness-space.** The boundary state-space is equivalent to the space of observer-
witnesses (points of view): brick 42's three theorems composed into one `Equiv`. The boundary
state-space assignment of foam's TQFT register — a *set* of points of view, each internally a
committed quantum system (`ReaderCommitment.lean`), with no linear structure across them (the
linearity delegated into the witnesses; see the file docstring). -/
def zeroDebtEquivWitness : BoundaryState 𝕜 E ≃ ObserverWitness 𝕜 E where
  toFun s := s.val.witness
  invFun W := ⟨CommitmentState.originFrom W, CommitmentState.originFrom_isZeroDebt W⟩
  left_inv s :=
    Subtype.ext (CommitmentState.eq_originFrom_witness_of_isZeroDebt s.property).symm
  right_inv _ := rfl

@[simp] theorem zeroDebtEquivWitness_apply (s : BoundaryState 𝕜 E) :
    zeroDebtEquivWitness s = s.val.witness := rfl

@[simp] theorem zeroDebtEquivWitness_symm_apply (W : ObserverWitness 𝕜 E) :
    (zeroDebtEquivWitness.symm W).val = CommitmentState.originFrom W := rfl

end Foam
