import Bridges.FTPG.Instance
import Bridges.FTPG.Iso

/-!
# The capstone: `ftpg_proof`

Everything algebraic is now real: `coordFrame_exists` constructs the frame,
`CoordFrame.divisionRing` is the coordinate division ring with every field law
total and sorry-free.  What remains is the *second* fundamental theorem — the
coordinatization of the whole lattice, not just the line: a coordinate vector
space `V` and a point map realizing `L ≃o Submodule (Coordinate Φ.Γ) V`.
`Iso.lean` reduced it to exactly the `PointSystem` residual (closure
preservation + spanning surjectivity); `pointSystem_exists` below is that
residual, the single remaining gap between `ftpg_statement` and the axiom's
deletion.

`Hollow.lean` has since turned the card over: the residual is *refutable as
stated* (`not_pointSystem`) — the hypotheses admit incomplete lattices, and
`Submodule D V` never is.  The `sorry` below is therefore not a gap awaiting
a construction but the marker of a re-scope: `ftpg_statement` must gain the
completeness-shaped hypothesis the classical theorem always carried.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-- **The residual: the second FTPG.**  A coordinate vector space and a
closure-preserving, spanning point map — the Veblen–Young coordinatization of
the lattice over the now-constructed division ring. -/
theorem pointSystem_exists (Φ : CoordFrame L) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (Coordinate Φ.Γ) V),
      Nonempty (PointSystem Φ.Γ V) := by
  sorry

theorem ftpg_proof : ftpg_statement.{u} := by
  intro L _ _ _ _ _ h_irred h_height
  obtain ⟨Φ⟩ := coordFrame_exists h_irred h_height
  obtain ⟨V, _, _, ⟨P⟩⟩ := pointSystem_exists Φ
  exact ⟨Coordinate Φ.Γ, inferInstance, V, ‹_›, ‹_›, P.orderIso⟩

end Foam.Bridges

#print axioms Foam.Bridges.ftpg_proof
