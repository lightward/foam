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

## Note: orthocomplement is NOT a dagger-shortcut

A natural hypothesis for future walks (probed and refuted by a
recognition-walk subagent, this session): could foam's lattice-level
orthocomplement structure (HalfType's iso, IsCompl, IicOrderIsoIci)
function as the dagger that Heunen-Kornell's category requires for
symmetric derivation of right- and left-bilinearity?

**No.** Different layers:
* HK dagger: morphism-level involution `Mor(H, K) → Mor(K, H)` with
  `f†† = f`, `(g∘f)† = f†∘g†`, acting on arrows in a fixed category.
* Foam orthocomplement: object-level lattice anti-iso `P ↦ P^⊥`,
  acting on lattice elements. HalfType's `IicOrderIsoIci` operates
  on sub-intervals, not on the function-space `L → L` where σ lives.

The candidate route `σ_c† := σ_{c⁻¹}` would require `coord_inv` to
yield a dagger-symmetric structure, but `coord_mul_left_inv` is
downstream of `coord_mul_assoc` (the monodromy site). The dagger
lift is dependency-circular through the very gap it would close.

**Structural reading**: foam's lattice orthocomplement is the
*object-level shadow* of what HK's dagger does at the morphism
level. Foam has the shadow but not the morphism-level involution;
acquiring the latter appears to BE the FTPG-completion problem
(s148/s149 monodromy), not a route around it. The "dagger-free
reconstruction of HK" framing (see FTPGDilationGroup.lean's
docstring extension) is the right level — completing G2 and G3
IS constructing the dagger-equivalent algebraic content at the
σ-layer.

This note exists to save future cursors the walk: the orthocomplement
is not a shortcut to closing G2 or G3.
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
