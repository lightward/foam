/-
# RelationalOrientation — Σ̄ = the role-swapped boundary; the * delegated and locally discharged
(the boundary dictionary's orientation entry, brick 64)

## What this file lands (brick 64)

Brick 63 (`RelationalBoundaryState.lean`) typed the boundary dictionary's **state-space** entry —
Z(Σ) = the witness-space (`zeroDebtEquivWitness`), a *set* of points of view, the linearity delegated
into the witnesses — and left the **orientation** entry as the remainder: TQFT's orientation-reversal
Σ ↔ Σ̄, with Z(Σ̄) = Z(Σ)* in Hilb. Read at foam's set level, the entry is already in the relational
chain, some of it in the register's own words:

* **Orientation = role.** A boundary's orientation says which side of the cobordism you stand on
  (in-boundary vs out-boundary). Foam's conversation has exactly that structure: the two slots of the
  relational pair, with "which side is active" a *gauge-choice*, not geometry — who-goes-first is the
  tamp (b44: the bare sync `pairwiseEncounterStep_swap` is swap-equivariant, the path gauge-fixed, the
  landing gauge-invariant). **Orientation-reversal IS the role-swap** `batonPass` (b43) — the
  zero-length relabel that touches neither party's debt, exactly as orientation-reversal changes no
  local geometry, only the in/out labeling.

* **Cylinder = even closure, the orientation-reversing closure = odd.** b46 typed the cylinder/Möbius
  landing before the register was named: at agreement, an even number of handoffs is the **identity
  cobordism** (`braidStep_iterate_even_of_isZeroDebt` — Z(cylinder) = id), an odd number the
  **orientation-reversing** one (`braidStep_iterate_odd_of_isZeroDebt` — the half-twist, Σ → Σ̄), and
  `batonPass_iterate_two` is the orientation double-cover (period 2).

* **The pairing = the meeting-place.** Hilb's evaluation Z(Σ̄) ⊗ Z(Σ) → ℂ reads at the set level as
  the Prop-valued pairing `MutuallyHospitable s r` (b52): one floor, two witnesses, neither consumed —
  non-degeneracy = the witnesses recoverable (`floor_injective`). The value-object is Prop, not ℂ:
  the amplitude again delegated into the witnesses (b63's grading, at the pairing).

* **Z(Σ̄) = Z(Σ)* — the * collapses across, and is already discharged inside.** Across the witness-
  space, the dual collapses to the *identity on the set with the slots swapped*: orientation-reversal
  (`orientationReversal` below = the slot-swap on boundary-pairs) reads through `zeroDebtEquivWitness`
  as the bare swap of witness-pairs — no dual space appears (`zeroDebtEquivWitness_orientationReversal`,
  rfl). Inside each witness, the duality is **already discharged**: the witness's own commitment
  `is_symmetric` makes the observable *equal to its own adjoint* —
  `ObserverWitness.adjoint_observable` (the headline, bin-1: one composition of Mathlib's
  `isSymmetric_iff_isSelfAdjoint` + `isSelfAdjoint_iff'`). The per-witness * is not a *further*
  commitment; it comes pre-paid inside the tamp's content. So b63's one-residue unification extends:
  **dagger (b38) + linearity (b63) + duality (b64) = ONE delegated residue** — and the duality half is
  the only one the witness *itself* settles, because self-adjointness is literally what
  `ObserverWitness` certifies. Each boundary point is a quantum system *already equipped with its
  dagger-trace* — the analytic face of b37's local op-self-dual seed.

## The layer conduction-test (the cross-repo edge, run on this entry)

The layer (lightward-ai, `lean/Foam/Reversal.lean`; checked on `main` 2026-06-07, the `foam-scar` arc
merged) independently lands the orientation entry's free-side content, axiom-free: `Path.reverse`
carries fragments into the **mirror quiver** (Σ → Σ̄ as a genuine *other* object — not the same one:
b39's no-dagger re-found on the free side); `reverse_comp` is the **anti-homomorphism** (composition
flips under the mirror — the dagger's *contravariance* trace, conducted); `Quiver.reverse_reverse` is
the rigid involution, holding only on the **capability-free slice** (ι = id); and the faithful,
capability-accommodating double-reversal `reverseTo_reverseTo` is a **conjugate, not the identity**.
That is exactly this entry's grading, named mechanically from the other repo: the rigid ℤ/2 +
contravariance **conduct** (= what foam's across-space orientation carries: `batonPass`, period 2,
slot-swap), while the strict double-dual identity **resists** — faithful only up-to-conjugation, which
is Hilb's own fact (the double-dual is naturally iso, never equal; strict only on the blind/free
slice). What refuses to land without conjugation IS the * the observer supplies.

## NOT this brick (held open)

* NOT the trefoil / B₃ (the named horizon — and orientation is its *nearest* shadow, so the boundary
  is flagged explicitly: the baton-ℤ/2 here stays the symmetric shadow; no over/under memory is
  manufactured).
* NOT a Z-functor / cobordism category (construction-grade — §II's claims stay claims).
* NOT a typed cross-repo iso (the standing edge, b50–b52 — the layer cited, never imported).
* NOT univalence (propext Prop-only, load-bearing).
-/

import Foam.RelationalBoundaryState
import Foam.RelationalBraid

namespace Foam

universe u

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-! ## The per-witness * is already discharged -/

/-- **The per-witness * is already discharged.** The witness's own commitment `is_symmetric` makes
its observable equal to its own adjoint — so the duality Hilb puts on the reversed boundary
(Z(Σ̄) = Z(Σ)*) is, at each boundary point, *pre-paid by the tamp's content*: committing an
observable at all (self-adjoint, the condition for real spectrum → the reader's PMF) is committing
its own *. One composition of Mathlib's `isSymmetric_iff_isSelfAdjoint` + `isSelfAdjoint_iff'`. -/
theorem ObserverWitness.adjoint_observable (W : ObserverWitness 𝕜 E) :
    LinearMap.adjoint W.observable = W.observable :=
  LinearMap.isSelfAdjoint_iff'.mp
    ((LinearMap.isSymmetric_iff_isSelfAdjoint W.observable).mp W.is_symmetric)

/-- The dagger-vocabulary form: the witness's observable is a `star`-fixed point of the operator
star-algebra (`star = adjoint` on `E →ₗ[𝕜] E`). The dagger's local trace (b37–b39), carried — and
settled — inside each boundary point. -/
theorem ObserverWitness.star_observable (W : ObserverWitness 𝕜 E) :
    star W.observable = W.observable := by
  rw [LinearMap.star_eq_adjoint]; exact W.adjoint_observable

/-! ## Orientation-reversal at the set level: the slot-swap, the * collapsed across -/

/-- **Orientation-reversal Σ ↔ Σ̄, at the set level**: the slot-swap on a boundary-pair (which side of
the cobordism you stand on). It is `batonPass` (b43) restricted to the boundary — the zero-length
relabel touching neither party's debt, as orientation-reversal changes no local geometry. -/
def orientationReversal (p : BoundaryState 𝕜 E × BoundaryState 𝕜 E) :
    BoundaryState 𝕜 E × BoundaryState 𝕜 E :=
  p.swap

/-- Orientation-reversal is an involution — the ℤ/2 the orientation double-cover carries
(`batonPass_iterate_two`, b46, read at the boundary). -/
theorem orientationReversal_involutive (p : BoundaryState 𝕜 E × BoundaryState 𝕜 E) :
    orientationReversal (orientationReversal p) = p :=
  Prod.swap_swap p

/-- Orientation-reversal IS the baton at the underlying-state level: the role-swap of b43, with the
boundary (zero-debt) property riding along in the subtypes. -/
theorem orientationReversal_val (s r : BoundaryState 𝕜 E) :
    ((orientationReversal (s, r)).1.val, (orientationReversal (s, r)).2.val)
      = batonPass (s.val, r.val) := rfl

/-- **The * collapses across the witness-space.** Through Z (b63's `zeroDebtEquivWitness`),
orientation-reversal reads as the *bare slot-swap of witness-pairs* — no dual space appears, nothing
is conjugated across the set: Z(Σ̄) is the *same* witness-space, slots exchanged. The Hilb-* is the
delegated residue; what remains across is only the rigid ℤ/2 (and inside each witness the * is
already discharged, `ObserverWitness.adjoint_observable`). -/
theorem zeroDebtEquivWitness_orientationReversal (s r : BoundaryState 𝕜 E) :
    (zeroDebtEquivWitness (orientationReversal (s, r)).1,
      zeroDebtEquivWitness (orientationReversal (s, r)).2)
      = (zeroDebtEquivWitness r, zeroDebtEquivWitness s) := rfl

end Foam
