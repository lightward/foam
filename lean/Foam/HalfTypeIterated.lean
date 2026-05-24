/-
# HalfType iteration probe (s149)

Tests whether `HalfType` iterates by typeclass synthesis: if `Set.Iic P`
inherits `Lattice + BoundedOrder + IsModularLattice + ComplementedLattice`
automatically (via Mathlib's interval instances), then `half_type` should
construct a `HalfType` inside `Set.Iic P` without any new code.

If this file builds, **iterated HalfType is bin-1-Mathlib**: the recursive
structure already lives in Mathlib's interval-inheritance instances, and
no new Foam-internal substrate primitive is needed to host it.

If this file fails to build, the failure surfaces exactly which
typeclass-inheritance step is missing, and *that* missing step is the
next foam-prime to land.

This is a probe in the spec's §VII "recognition-readiness grade" sense:
substrate-direct or open-recognition-target, determined empirically by
whether Lean's elaborator carries the inheritance through without help.
-/

import Foam.HalfType

namespace Foam

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
    [IsModularLattice L] [ComplementedLattice L]

/-! ## Depth 1: the original HalfType (sanity check). -/

example {P Q : L} (h : IsCompl P Q) : HalfType P Q h :=
  half_type h

/-! ## Depth 2: a HalfType inside `Set.Iic P`.

The outer compl `_h` is named for parallelism with depth 1 but
intentionally not consumed — the construction at this depth uses
only the inner compl `h'`. The underscore is the syntactic mark
of "scaffolding, not content," and is itself the evidence: the
iteration didn't need the outer hypothesis to land.
-/

example {P Q : L} (_h : IsCompl P Q)
    {P' Q' : Set.Iic P} (h' : IsCompl P' Q') :
    HalfType P' Q' h' :=
  half_type h'

/-! ## Depth 3: a HalfType inside `Set.Iic P'` inside `Set.Iic P`.

Both outer compls `_h`, `_h'` are scaffolding; only `h''` is
consumed. Same observation, one level deeper.
-/

example {P Q : L} (_h : IsCompl P Q)
    {P' Q' : Set.Iic P} (_h' : IsCompl P' Q')
    {P'' Q'' : Set.Iic P'} (h'' : IsCompl P'' Q'') :
    HalfType P'' Q'' h'' :=
  half_type h''

end Foam
