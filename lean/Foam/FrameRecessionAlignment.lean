/-
# Frame recession alignment — σ ↔ RingHom ↔ projection-HalfType (s149)

Probes the structural alignment of three layers in the project / Mathlib:

* **Layer 1 (Dynamics.lean)**: `frame_recession` at the matrix level.
  An idempotent `P` (P² = P) with symmetric structure (Pᵀ = P) recedes
  from its initial frame under skew-symmetric perturbation W. The
  projector is the "observer's frame"; perturbation makes the frame
  shift; second-order overlap is non-positive (frame can only recede).
* **Layer 2 (Mathlib RingHom)**: a structure-preserving map between
  two algebraic halves (+ and ·). Mathlib's canonical formalization
  of "bridge between two complementary algebraic structures."
* **Layer 3 (FTPGDilationGroup σ)**: σ as bridge between Dilation Γ
  (multiplicative, Monoid composition) and pointwise coord_add on
  L → L (additive). σ_mul + σ_add_pointwise are the ring-hom-shaped
  witness identities (currently open at FTPG, named as sorries).

## The unifying structure

All three layers are instances of the same shape:
**"two complementary halves with a structure-preserving bridge that,
when the observer applies it to themselves, produces recession from
the initial frame."**

The s149 recognition (from this session's exchange): applying
HalfType *to the observer themselves* IS frame recession — and the
bridge between the two halves IS the entanglement-witness whose
content is loop-independent (gauge-invariant under each half's
populating choice).

## What this file lands

**Bin-1-Mathlib bridge between Layer 1 and HalfType.** Mathlib's
`LinearMap.IsIdempotentElem.isCompl` says: an idempotent linear map `f` yields
`IsCompl (range f) (ker f)` in the submodule lattice. Combined with
`half_type` (the s148 HalfType constructor), this gives
**HalfType (range f) (ker f) hf.isCompl** for free — the projection
*is* a HalfType in the subspace lattice.

This is the matrix-projection ↔ HalfType bridge. Together with the
existing `frame_recession` theorem (Dynamics.lean), it places the
matrix-level recession content into the lattice register where σ
and `half_type` live — three layers, one structural shape.

Implementation: a single `example` declaration demonstrating the
construction (the artifact is the bin-1 landing, not a theorem).

## Notes on Layer 2 / Layer 3

Layer 2 (RingHom in Mathlib) and Layer 3 (σ at FTPG) are not
exhibited as Lean code here — Layer 3's σ has open sorries
(σ_mul, σ_add_pointwise) and the planar ring structure on l-atoms
isn't constructed (coord_mul_assoc is the open frontier per
lean/CLAUDE.md's s148/s149 refinements). The recognition is
structural: σ_mul + σ_add_pointwise constitute a RingHom-shape
*once* the source ring structure lands. The recognition is
documented here; the formalization is downstream of mul-assoc
closure.
-/

import Foam.HalfType
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Foam

universe u v

/-! ## The matrix-projection → HalfType bridge

    An idempotent linear map on a vector space yields a HalfType in
    the submodule lattice via its (range, ker) complementary pair.
    Substrate-direct from Mathlib:

    * `LinearMap.IsIdempotentElem.isCompl` (`Mathlib/LinearAlgebra/Projection.lean`):
      idempotent linear map `f` ⟹ `IsCompl (range f) (ker f)`.
    * `Submodule.complementedLattice` (`Mathlib/LinearAlgebra/Basis/
      VectorSpace.lean:283`): `ComplementedLattice (Submodule K V)`
      for K a Field / DivisionRing.
    * `half_type` (`Foam/HalfType.lean`): the s148 HalfType constructor.

    Composing the three gives the bridge. -/

/-- **A projection IS a HalfType.** Every idempotent linear map
    `f : E →ₗ[K] E` (over a division ring K) determines a `HalfType`
    in the submodule lattice of `E`: `(range f, ker f)` is a
    complementary pair, and `half_type` lands the HalfType.

    This is the **Layer-1 → HalfType bridge**: the matrix-projection
    setting of `Dynamics.lean`'s `frame_recession` theorem plugs
    directly into the lattice infrastructure where `half_type` lives. -/
example {K : Type u} [DivisionRing K]
    {E : Type v} [AddCommGroup E] [Module K E]
    {f : E →ₗ[K] E} (hf : IsIdempotentElem f) :
    HalfType (LinearMap.range f) (LinearMap.ker f) (LinearMap.IsIdempotentElem.isCompl hf) :=
  half_type (LinearMap.IsIdempotentElem.isCompl hf)

end Foam
