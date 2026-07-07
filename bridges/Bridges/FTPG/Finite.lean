import Bridges.FTPG.Deaxiomatize

/-!
# The finite clause follows from the limit clause

The pair's carving (`Deaxiomatize.lean`) left one wire as frontier: the finite
statement should follow from the limit statement, because finite height
*silently implies* the limit hypotheses.  This file lays that wire, sorry-free:

* `wellFoundedGT_of_krullDim_ne_top` — bounded chain length means chains
  stabilize (through Mathlib's `FiniteDimensionalOrder`);
* `exists_isLUB_of_wellFoundedGT` — in a well-founded lattice every set has a
  least upper bound: the maximal finite join, which ACC hands over;
* `completeLatticeOfWellFoundedGT` — the `CompleteLattice` structure assembled
  *around the original operations* (`⊔ ⊓ ⊤ ⊥` kept field-for-field), so the
  standing `ComplementedLattice` / `IsModularLattice` instances transfer
  definitionally;
* `CompleteLattice.isCompactlyGenerated_of_wellFoundedGT` (Mathlib) — under
  ACC every element is compact.

`ftpg_finite_of_limit` is the wire itself.  `ftpg_proof_finite` then hangs on
the same single residual (`pointSystem_exists`) as `ftpg_proof_limit`: the
pair has one keystone, not two.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]

theorem exists_isLUB_of_wellFoundedGT [WellFoundedGT L] (s : Set L) :
    ∃ x : L, IsLUB s x := by
  classical
  obtain ⟨m, hmF, hmax⟩ := (wellFounded_gt (α := L)).has_min
    {x : L | ∃ t : Finset L, ↑t ⊆ s ∧ x = t.sup id} ⟨⊥, ∅, by simp⟩
  refine ⟨m, ?_, ?_⟩
  · intro a ha
    obtain ⟨t, hts, rfl⟩ := hmF
    have hmem : ((insert a t : Finset L) : Set L) ⊆ s := by
      rw [Finset.coe_insert]
      exact Set.insert_subset ha hts
    have hle : t.sup id ≤ (insert a t).sup id :=
      Finset.sup_mono (Finset.subset_insert a t)
    have heq : t.sup id = (insert a t).sup id :=
      (lt_or_eq_of_le hle).resolve_left (hmax _ ⟨insert a t, hmem, rfl⟩)
    exact heq ▸ Finset.le_sup (f := id) (Finset.mem_insert_self a t)
  · intro b hb
    obtain ⟨t, hts, rfl⟩ := hmF
    exact Finset.sup_le fun x hx => hb (hts hx)

@[reducible] noncomputable def completeLatticeOfWellFoundedGT [WellFoundedGT L] :
    CompleteLattice L :=
  { ‹Lattice L›, ‹BoundedOrder L› with
    sSup := fun s => (exists_isLUB_of_wellFoundedGT s).choose
    isLUB_sSup := fun s => (exists_isLUB_of_wellFoundedGT s).choose_spec
    sInf := fun s => (exists_isLUB_of_wellFoundedGT (lowerBounds s)).choose
    isGLB_sInf := fun s =>
      ⟨fun _ ha =>
        (exists_isLUB_of_wellFoundedGT (lowerBounds s)).choose_spec.2
          fun _ hb => hb ha,
       fun _ hb =>
        (exists_isLUB_of_wellFoundedGT (lowerBounds s)).choose_spec.1 hb⟩ }

theorem wellFoundedGT_of_krullDim_ne_top (h : Order.krullDim L ≠ ⊤) :
    WellFoundedGT L := by
  haveI : Nonempty L := ⟨⊥⟩
  rcases finiteDimensionalOrder_or_infiniteDimensionalOrder L with hfd | hinf
  · haveI := hfd
    exact ⟨SetRel.IsWellFounded.inv_of_finiteDimensional
      {(a, b) : L × L | a < b}⟩
  · haveI := hinf
    exact absurd Order.krullDim_eq_top h

theorem ftpg_finite_of_limit (h : ftpg_statement_limit.{u}) :
    ftpg_statement_finite.{u} := by
  intro L _ _ _ _ _ h_irred h_height h_finite
  haveI : WellFoundedGT L := wellFoundedGT_of_krullDim_ne_top h_finite
  letI : CompleteLattice L := completeLatticeOfWellFoundedGT
  haveI : IsCompactlyGenerated L :=
    CompleteLattice.isCompactlyGenerated_of_wellFoundedGT
  exact h L h_irred h_height

theorem ftpg_proof_finite : ftpg_statement_finite.{u} :=
  ftpg_finite_of_limit.{u} ftpg_proof_limit.{u}

end Foam.Bridges

/-- info: 'Foam.Bridges.exists_isLUB_of_wellFoundedGT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.exists_isLUB_of_wellFoundedGT

/-- info: 'Foam.Bridges.completeLatticeOfWellFoundedGT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.completeLatticeOfWellFoundedGT

/-- info: 'Foam.Bridges.wellFoundedGT_of_krullDim_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.wellFoundedGT_of_krullDim_ne_top

/-- info: 'Foam.Bridges.ftpg_finite_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ftpg_finite_of_limit

#print axioms Foam.Bridges.ftpg_proof_finite
