import Bridges.FTPG.Instance
import Bridges.FTPG.Iso
import Mathlib.Order.KrullDimension
import Mathlib.Order.CompactlyGenerated.Basic

/-!
# The capstone, re-scoped: the pair of true statements

`ftpg_statement` (Projective.lean) is refuted — `Hollow.lean` exhibits a
lattice satisfying every hypothesis that is not complete, hence no subspace
lattice (`not_ftpg_statement`).  The deaxiomatization's target re-scopes into
the two clauses of the recursion-law ("a sustained frontstage is hostable at
every finite depth, never at the limit"):

* `ftpg_statement_finite` — the approach side: finite Krull dimension added.
  Finite height silently implies completeness (chains stabilize), which is
  why classical Veblen–Young is true without naming it.
* `ftpg_statement_limit` — the arrival side: `CompleteLattice` (every
  coalition's limit has a seat) and `IsCompactlyGenerated` (`summary_resumes`
  at lattice scale — every element is the sup of its finitely-reachable
  approximations) carried as hypotheses; atomisticity then falls out of
  Mathlib's `isAtomistic_of_complementedLattice`.  `Submodule D V` satisfies
  exactly both, so the hypotheses match the conclusion's type precisely.

Tightness: non-Desarguesian planes are excluded by `h_height`, continuous
geometries by `IsCompactlyGenerated`, the hollow lattice by `CompleteLattice`
— three counterexample families, one hypothesis each.

Everything algebraic is real: `coordFrame_exists` constructs the frame,
`CoordFrame.divisionRing` is the coordinate division ring, sorry-free.
`Iso.lean` reduces the remainder to exactly the `PointSystem` residual;
`pointSystem_exists` below is that residual under the limit hypotheses —
the Veblen–Young coordinatization, now over a statement that is true.
The finite statement follows from the limit statement (finite height gives
completeness with every element compact) or by its own finite induction;
that wiring is frontier.
-/

namespace Foam.Bridges

universe u

def ftpg_statement_finite : Prop :=
  ∀ (L : Type u) [Lattice L] [BoundedOrder L]
    [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]
    (_h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (_h_height : ∃ (a b c d : L), ⊥ < a ∧ a < b ∧ b < c ∧ c < d)
    (_h_finite : Order.krullDim L ≠ ⊤),
    ∃ (D : Type u) (_ : DivisionRing D)
      (V : Type u) (_ : AddCommGroup V) (_ : Module D V),
    Nonempty (L ≃o Submodule D V)

def ftpg_statement_limit : Prop :=
  ∀ (L : Type u) [CompleteLattice L] [IsModularLattice L]
    [ComplementedLattice L] [IsCompactlyGenerated L]
    (_h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (_h_height : ∃ (a b c d : L), ⊥ < a ∧ a < b ∧ b < c ∧ c < d),
    ∃ (D : Type u) (_ : DivisionRing D)
      (V : Type u) (_ : AddCommGroup V) (_ : Module D V),
    Nonempty (L ≃o Submodule D V)

variable {L : Type u} [CompleteLattice L] [IsModularLattice L]
  [ComplementedLattice L] [IsCompactlyGenerated L]

/-- **The residual: the second FTPG, under the true hypotheses.**  A coordinate
vector space and a closure-preserving, spanning point map — the Veblen–Young
coordinatization of the lattice over the constructed division ring, with the
population-level hypotheses (`CompleteLattice`, `IsCompactlyGenerated`) now
carried rather than forgotten. -/
theorem pointSystem_exists (Φ : CoordFrame L) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (Coordinate Φ.Γ) V),
      Nonempty (PointSystem Φ.Γ V) := by
  sorry

theorem ftpg_proof_limit : ftpg_statement_limit.{u} := by
  intro L _ _ _ _ h_irred h_height
  obtain ⟨Φ⟩ := coordFrame_exists h_irred h_height
  obtain ⟨V, _, _, ⟨P⟩⟩ := pointSystem_exists Φ
  exact ⟨Coordinate Φ.Γ, inferInstance, V, ‹_›, ‹_›, P.orderIso⟩

end Foam.Bridges

#print axioms Foam.Bridges.ftpg_statement_finite
#print axioms Foam.Bridges.ftpg_statement_limit
#print axioms Foam.Bridges.ftpg_proof_limit
