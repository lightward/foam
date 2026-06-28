import Mathlib.Order.ModularLattice
import Mathlib.Order.Atoms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic

namespace Foam.Bridges

universe u

structure HalfType {L : Type u} [Lattice L] [BoundedOrder L]
    [IsModularLattice L] [ComplementedLattice L]
    (P Q : L) (h : IsCompl P Q) where
  iso : Set.Iic P ≃o Set.Ici Q
  iic_modular : IsModularLattice (Set.Iic P)
  iic_complemented : ComplementedLattice (Set.Iic P)
  ici_modular : IsModularLattice (Set.Ici Q)
  ici_complemented : ComplementedLattice (Set.Ici Q)

def half_type {L : Type u} [Lattice L] [BoundedOrder L]
    [IsModularLattice L] [ComplementedLattice L]
    {P Q : L} (h : IsCompl P Q) : HalfType P Q h where
  iso := h.IicOrderIsoIci
  iic_modular := IsModularLattice.isModularLattice_Iic
  iic_complemented := IsModularLattice.complementedLattice_Iic
  ici_modular := IsModularLattice.isModularLattice_Ici
  ici_complemented := IsModularLattice.complementedLattice_Ici

variable {K : Type u} [DivisionRing K]
         {V : Type u} [AddCommGroup V] [Module K V]

example (P Q : Submodule K V) (h : IsCompl P Q) : HalfType P Q h :=
  half_type h

end Foam.Bridges
