import Bridges.FTPG.Instance
import Bridges.FTPG.Iso
import Bridges.FTPG.Ground
import Bridges.FTPG.Span
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

Everything is real: `coordFrame_exists` constructs the frame,
`CoordFrame.divisionRing` is the coordinate division ring, and
`pointSystem_exists` below — the residual, the second FTPG — is now a
theorem: the ladder grounded at τ (`Ground.lean`) climbs the directed
family of finite windows along an atom basis (`Window.lean`, `Limit.lean`)
and the spanning stratum packages the limit (`Span.lean`).  The base
support `t₀` is the union of the four frame atoms' finite supports
(`exists_finset_support` — a point is finitely reachable), the base atom
is `O`, the calibration chooser comes from `h_irred`, and the carrier `V`
is the span of the read-image in the named slot space — a left module
over `(Coordinate Φ.Γ)ᵐᵒᵖ`, the orientation the plane's line equation
forced (`y = s·x + b`: slope on the left).  `ftpg_proof_limit` is
sorry-free; the finite statement follows through `Finite.lean`'s wire.
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

/-- **The residual: the second FTPG, under the true hypotheses — discharged.**
A coordinate vector space and a closure-preserving, spanning point map — the
Veblen–Young coordinatization of the lattice over (the opposite of) the
constructed division ring, with the population-level hypotheses
(`CompleteLattice`, `IsCompactlyGenerated`) now carried rather than
forgotten. -/
theorem pointSystem_exists (Φ : CoordFrame L) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (Coordinate Φ.Γ)ᵐᵒᵖ V),
      Nonempty (PointSystem Φ.Γ V) := by
  classical
  obtain ⟨B⟩ := atomBasis_exists (L := L)
  obtain ⟨c, hc, hc_UR, hc_U, hc_R⟩ :=
    Φ.h_irred Φ.Γ.U Φ.R Φ.Γ.hU Φ.hR_atom (CoordSystem.hU_ne_R Φ.hR_not)
  obtain ⟨cal, hcal⟩ := calSpec_exists Φ.Γ.hO Φ.h_irred
  obtain ⟨tO, htOB, htO⟩ := B.exists_finset_support Φ.Γ.hO
  obtain ⟨tU, htUB, htU⟩ := B.exists_finset_support Φ.Γ.hU
  obtain ⟨tV, htVB, htV⟩ := B.exists_finset_support Φ.Γ.hV
  obtain ⟨tR, htRB, htR⟩ := B.exists_finset_support Φ.hR_atom
  have ht₀B : ↑(tO ∪ tU ∪ tV ∪ tR) ⊆ B.carrier := by
    rw [Finset.coe_union, Finset.coe_union, Finset.coe_union]
    exact Set.union_subset
      (Set.union_subset (Set.union_subset htOB htUB) htVB) htRB
  have hsub : ∀ t : Finset L, t ⊆ tO ∪ tU ∪ tV ∪ tR →
      t.sup id ≤ (tO ∪ tU ∪ tV ∪ tR).sup id := fun _ h => Finset.sup_mono h
  have hxt₀ : Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R ≤ (tO ∪ tU ∪ tV ∪ tR).sup id := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact htO.trans (hsub tO
        ((Finset.subset_union_left.trans Finset.subset_union_left).trans
          Finset.subset_union_left))
    · exact htU.trans (hsub tU
        ((Finset.subset_union_right.trans Finset.subset_union_left).trans
          Finset.subset_union_left))
    · exact htV.trans (hsub tV
        (Finset.subset_union_right.trans Finset.subset_union_left))
    · exact htR.trans (hsub tR Finset.subset_union_right)
  obtain ⟨V, hAG, hMod, pt, hclosed, hsurj⟩ :=
    limit_system_exists Φ.h_irred B (Φ.pointSysTau hc hc_UR hc_U hc_R)
      (by norm_num) Φ.Γ.hO
      ((le_sup_left.trans le_sup_left).trans le_sup_left)
      hcal ht₀B hxt₀
  letI := hAG
  letI := hMod
  exact ⟨V, hAG, hMod, ⟨⟨pt, hclosed, hsurj⟩⟩⟩

theorem ftpg_proof_limit : ftpg_statement_limit.{u} := by
  intro L _ _ _ _ h_irred h_height
  obtain ⟨Φ⟩ := coordFrame_exists h_irred h_height
  obtain ⟨V, _, _, ⟨P⟩⟩ := pointSystem_exists Φ
  exact ⟨(Coordinate Φ.Γ)ᵐᵒᵖ, inferInstance, V, ‹_›, ‹_›, P.orderIso⟩

end Foam.Bridges

/-! ## Axiom audit -/

/-- info: 'Foam.Bridges.ftpg_statement_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ftpg_statement_finite

/-- info: 'Foam.Bridges.ftpg_statement_limit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ftpg_statement_limit

/-- info: 'Foam.Bridges.pointSystem_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.pointSystem_exists

/-- info: 'Foam.Bridges.ftpg_proof_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ftpg_proof_limit
