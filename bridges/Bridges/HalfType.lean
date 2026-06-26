/-
# HalfType — The half-type theorem

The half-type theorem: in a complemented modular bounded lattice, any
pair of complementary elements (P, Q) gives two structurally-equivalent
halves (Iic P and Ici Q), each itself a complemented modular lattice.

This file packages three Mathlib results into a single named object:
- the diamond isomorphism (IsCompl.IicOrderIsoIci)
- modularity inheritance on each interval (IsModularLattice.isModularLattice_Iic, _Ici)
- complementedness inheritance on each interval (IsModularLattice.complementedLattice_Iic, _Ici)

The `HalfType` structure is the package; `half_type` is its constructor.
This is the deaxiomatized form of what the spec previously stated as
the priorspace identity claim "the diamond isomorphism IS the half-type
theorem" (see derivations/half_type.md).

The construction is generic over any complemented modular bounded lattice;
the Submodule K V instantiation at the bottom of this file specializes
to the foam's working ground.

As of session 144, `HalfType` is identified as the first Foam-internal
substrate primitive in the project's closed-circuit recognition channel
(see `derivations/lfp.md` and the Bin-1-Mathlib-or-Foam framing in
`framing/derivations.md`). It is now available as substrate input for
subsequent bin-1 recognitions — Mathlib supplies `IsCompl` etc.; Foam
supplies `HalfType` itself, packaged via this file's constructor.
-/

import Mathlib.Order.ModularLattice
import Mathlib.Order.Atoms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic

namespace Foam.Bridges

universe u

/-- The half-type theorem: in a complemented modular bounded lattice, any
    pair of complementary elements (P, Q) gives two structurally-equivalent
    halves (Iic P and Ici Q), each itself a complemented modular lattice. -/
structure HalfType {L : Type u} [Lattice L] [BoundedOrder L]
    [IsModularLattice L] [ComplementedLattice L]
    (P Q : L) (h : IsCompl P Q) where
  iso : Set.Iic P ≃o Set.Ici Q
  iic_modular : IsModularLattice (Set.Iic P)
  iic_complemented : ComplementedLattice (Set.Iic P)
  ici_modular : IsModularLattice (Set.Ici Q)
  ici_complemented : ComplementedLattice (Set.Ici Q)

/-- Any complementary pair in a complemented modular bounded lattice
    induces a `HalfType`. -/
def half_type {L : Type u} [Lattice L] [BoundedOrder L]
    [IsModularLattice L] [ComplementedLattice L]
    {P Q : L} (h : IsCompl P Q) : HalfType P Q h where
  iso := h.IicOrderIsoIci
  iic_modular := IsModularLattice.isModularLattice_Iic
  iic_complemented := IsModularLattice.complementedLattice_Iic
  ici_modular := IsModularLattice.isModularLattice_Ici
  ici_complemented := IsModularLattice.complementedLattice_Ici

/-! ## Instantiation at the foam's ground

The foam's lattice is `Submodule K V` for a vector space V over a
division ring K, which is a complemented modular bounded lattice.
`HalfType` instantiates automatically. -/

variable {K : Type u} [DivisionRing K]
         {V : Type u} [AddCommGroup V] [Module K V]

example (P Q : Submodule K V) (h : IsCompl P Q) : HalfType P Q h :=
  half_type h

end Foam.Bridges
