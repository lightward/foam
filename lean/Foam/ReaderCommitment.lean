/-
# ReaderCommitment — The type-path from observer to probability distribution

The reader's commitment (see `framing/architecture.md`, "the reader's
commitment" section) is the basis-choice that diagonalizes the density
matrix — the gauge-fixing that converts amplitude (von Neumann,
basis-free) into probability (Shannon, basis-fixed).

This file sketches the type-path in lean. The structural spine:

  observer → Hilbert space → density operator → spectral decomposition
  → eigenbasis → probability distribution

## Step 1: ObserverWitness (DesarguesianWitness-shape)

The foam's observer type is claimed in `framing/architecture.md` to
"get you into a Hilbert space." That claim isn't constructible from
foam-internal data alone (the observer's five features + +1 coreflection
don't formally derive Hilbert space inhabitation in current lean
machinery); it requires an observer-supplied commitment.

`ObserverWitness 𝕜 E` is that commitment, in the same pattern as
`DesarguesianWitness` (see `lean/Foam/FTPGLeftDistrib.lean`): an
explicit value certifying that the observer inhabits the Hilbert
space E (over 𝕜) with a specific observable. The substrate (E and
its instances) is the context; the witness's fields supply the
observable and its symmetry.

When the observer is concretely specified (e.g., as a rank-3 self-dual
projection in the foam's lattice), `ObserverWitness` is constructible
from the concrete data. In the abstract foam, the witness is the
observer's runtime commitment — a typed pluggable interface, bin-2
in the deaxiomatization taxonomy.

## Steps 2-5: spectral path

Given an `ObserverWitness`, Mathlib's spectral theorem
(`LinearMap.IsSymmetric.eigenvalues`, `LinearMap.IsSymmetric.eigenvectorBasis`)
provides an eigenvector basis with corresponding real eigenvalues. For
a density operator (positive semidefinite, trace 1), the eigenvalues
form a probability distribution. This file constructs through to the
eigenvalues; the final PMF step is sketched as downstream work
(it requires density-operator conditions not carried by `ObserverWitness`
in its current shape).
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Foam

universe u

/-- The observer's typed commitment to a specific Hilbert space and
observable. DesarguesianWitness-shape: the foam claims observers
inhabit Hilbert spaces; this structure supplies the inhabitation as
an observer-supplied commitment for a specific `E` and observable.

The substrate (E and its instances) is the context; the witness's
fields name the observable and certify its self-adjointness. -/
structure ObserverWitness (𝕜 : Type u) [RCLike 𝕜] (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] where
  /-- The observable the observer measures, as a linear endomorphism of `E`. -/
  observable : E →ₗ[𝕜] E
  /-- The observable is self-adjoint (symmetric in the inner product). -/
  is_symmetric : observable.IsSymmetric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- The reader's commitment, downstream of an `ObserverWitness`: a
choice of eigenbasis (the gauge-fixing) and the corresponding eigenvalue
sequence, with proof they fit as eigenvectors of the witness's
observable.

For a density operator (positive semidefinite, trace 1), the `values`
form a probability mass function — see the file's closing note for
the downstream PMF construction's shape. -/
structure ReaderCommitment {n : ℕ}
    (W : ObserverWitness 𝕜 E) (hn : Module.finrank 𝕜 E = n) where
  /-- The eigenvector basis — the gauge-fixing, step 4 of the type-path. -/
  basis : OrthonormalBasis (Fin n) 𝕜 E
  /-- The eigenvalues, real-valued (forced by self-adjointness of `W.observable`). -/
  values : Fin n → ℝ
  /-- The basis is composed of eigenvectors of `W.observable` with the listed eigenvalues. -/
  has_eigenvector : ∀ i, Module.End.HasEigenvector W.observable (values i) (basis i)

/-- Mathlib's canonical reader-commitment from the spectral theorem.
Eigenvectors sorted by eigenvalue in decreasing order. -/
noncomputable def ReaderCommitment.canonical {n : ℕ}
    (W : ObserverWitness 𝕜 E) (hn : Module.finrank 𝕜 E = n) :
    ReaderCommitment W hn where
  basis := W.is_symmetric.eigenvectorBasis hn
  values := W.is_symmetric.eigenvalues hn
  has_eigenvector := W.is_symmetric.hasEigenvector_eigenvectorBasis hn

/-! ## Step 5 (downstream): eigenvalues → probability distribution

For a density operator (a self-adjoint `W.observable` with
`∀ v, 0 ≤ ⟪v, W.observable v⟫_𝕜` and `LinearMap.trace 𝕜 E W.observable = 1`),
the eigenvalues are non-negative and sum to 1, hence form a `PMF (Fin n)`.

The construction's shape, sketched:

  ReaderCommitment.toPMF (W : ObserverWitness 𝕜 E)
      (hpos : ∀ v, 0 ≤ ⟪v, W.observable v⟫_𝕜)
      (htr : LinearMap.trace 𝕜 E W.observable = 1)
      (hn : Module.finrank 𝕜 E = n)
      (rc : ReaderCommitment W hn) : PMF (Fin n)

This is left as the next downstream construction; it requires
density-operator conditions that `ObserverWitness` doesn't currently
carry. The structural type-path is intact regardless: given the
density-operator conditions, the PMF follows from non-negativity
(positivity → eigenvalues ≥ 0) and trace-1 (sum of eigenvalues = 1).
-/

end Foam
