import Bridges.FTPG.Window

/-!
# Camp four: the limit map — one choice per atom, laws by common windows

`limit_read_exists`: over an atom basis `B` and a base system `P` at
`x ≤ t₀.sup id`, there is a single global assignment
`hv : L → (Fin n → K) × (L → K)` — every atom read through one chosen window
climb, `Classical.choice` serving as the representative per atom exactly as
the probe's check F answered the seated question — such that:

* **stability**: on every window's flat, `hv` span-agrees with that window's
  climb read, whichever climb it is (`window_read_directed` through the
  chosen window; rigidity and both coherence faces already standing);
* **base compatibility**: below `x` the assignment is literally the padded
  base vector — `summary_resumes` at name scale, vector-level
  (`IsClimb.hv_of_le` + `climbRead_pad`, no rescale needed);
* **the three pointwise laws, globally**: `ne_zero`, `span_inj`, and
  `collinear_iff` hold for ALL atoms of `L` at once — any two or three atoms
  meet inside the union window (directedness of the family), the window's
  `PointSys` laws fire there, and the reads reflect back through
  `climbRead_injective` (`map_mem_span_singleton_iff`,
  `map_mem_span_pair_iff`, `mem_span_pair_congr`).

Every atom is covered because a point is finitely reachable
(`AtomBasis.exists_finset_support` — the compactness camp one banked).  The
fourth `PointSys` law, `span_surj`, is deliberately absent: at the limit it
is the *spanning* half of the `PointSystem` residual, owed onto the named
slot space `(Fin n → K) × (B →₀ K)` — the next stratum's packaging, where
the orientation re-scope (`Dᵐᵒᵖ`) is also seated.

Model-verified before carving (`probe_limit.py`, check F, the previous
sitting): the limit map built from one arbitrary representative per atom —
random window containing the support, random legal order, random nonzero
scalar — satisfies all four `PointSys` laws globally, over five window
configurations at `q ∈ {2,3}`, twisted base systems throughout.
-/

namespace Foam.Bridges

universe u

section Limit

variable {L : Type u} [CompleteLattice L] [IsModularLattice L] [IsAtomistic L]
  [IsCompactlyGenerated L]
variable {K : Type*} [DivisionRing K] [DecidableEq L]

theorem limit_read_exists
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (B : AtomBasis L) {b₀ : L} {cal : L → L} {x : L} {t₀ : Finset L} {n : ℕ}
    (P : PointSys x n K)
    (hn : 3 ≤ n) (hb₀ : IsAtom b₀) (hb₀x : b₀ ≤ x) (hcal : CalSpec b₀ cal)
    (ht₀B : ↑t₀ ⊆ B.carrier) (hxt₀ : x ≤ t₀.sup id) :
    ∃ hv : L → (Fin n → K) × (L → K),
      (∀ (s : Finset L), t₀ ⊆ s → ↑s ⊆ B.carrier →
        ∀ Q : PointSys (climbFlat x (windowPairs cal x t₀ s))
          (climbDim n (windowPairs cal x t₀ s)) K,
        IsClimb b₀ (windowPairs cal x t₀ s) x n P Q →
        ∀ t : L, IsAtom t → t ≤ climbFlat x (windowPairs cal x t₀ s) →
          Submodule.span K {hv t}
            = Submodule.span K {climbRead (windowPairs cal x t₀ s) (Q.hv t)}) ∧
      (∀ p : L, IsAtom p → p ≤ x → hv p = (P.hv p, 0)) ∧
      (∀ p : L, IsAtom p → hv p ≠ 0) ∧
      (∀ p q : L, IsAtom p → IsAtom q → p ≠ q →
        hv q ∉ Submodule.span K {hv p}) ∧
      (∀ p q r : L, IsAtom p → IsAtom q → IsAtom r → p ≠ q →
        (r ≤ p ⊔ q ↔ hv r ∈ Submodule.span K {hv p, hv q})) := by
  classical
  have hQce : ∀ s : Finset L, ↑s ⊆ B.carrier →
      ∃ Q : PointSys (climbFlat x (windowPairs cal x t₀ s))
        (climbDim n (windowPairs cal x t₀ s)) K,
        IsClimb b₀ (windowPairs cal x t₀ s) x n P Q :=
    fun s hsB => isClimb_exists h_irred _ x n P hn hb₀ hb₀x
      (window_legal B hcal hb₀x ht₀B hxt₀ hsB)
  choose Qc hQc using hQce
  have hwine : ∀ p : L, IsAtom p → ∃ s : Finset L,
      t₀ ⊆ s ∧ ↑s ⊆ B.carrier ∧
      p ≤ climbFlat x (windowPairs cal x t₀ s) := by
    intro p hp
    obtain ⟨t, htB, hpt⟩ := B.exists_finset_support hp
    refine ⟨t₀ ∪ t, Finset.subset_union_left,
      by rw [Finset.coe_union]; exact Set.union_subset ht₀B htB, ?_⟩
    rw [windowFlat_eq Finset.subset_union_left]
    exact le_sup_of_le_right
      (hpt.trans (Finset.sup_mono Finset.subset_union_right))
  choose win hw1 hw2 hw3 using hwine
  have hinj : ∀ s : Finset L, Function.Injective
      (climbRead (windowPairs cal x t₀ s) (K := K) (n := n)) := by
    intro s
    refine climbRead_injective _ ?_
    rw [windowPairs, calPairs_map_fst]
    exact windowList_nodup x t₀ s
  have hflat_mono : ∀ {s s' : Finset L}, t₀ ⊆ s → s ⊆ s' → ∀ {p : L},
      p ≤ climbFlat x (windowPairs cal x t₀ s) →
      p ≤ climbFlat x (windowPairs cal x t₀ s') := by
    intro s s' hts hss' p hp
    rw [windowFlat_eq (hts.trans hss')]
    rw [windowFlat_eq hts] at hp
    exact hp.trans (sup_le_sup_left (Finset.sup_mono hss') x)
  set hvlim : L → (Fin n → K) × (L → K) := fun p =>
    if hp : IsAtom p
    then climbRead (windowPairs cal x t₀ (win p hp))
      ((Qc (win p hp) (hw2 p hp)).hv p)
    else 0 with hhv
  have hstab : ∀ (s : Finset L), t₀ ⊆ s → ↑s ⊆ B.carrier →
      ∀ Q : PointSys (climbFlat x (windowPairs cal x t₀ s))
        (climbDim n (windowPairs cal x t₀ s)) K,
      IsClimb b₀ (windowPairs cal x t₀ s) x n P Q →
      ∀ t : L, IsAtom t → t ≤ climbFlat x (windowPairs cal x t₀ s) →
        Submodule.span K {hvlim t}
          = Submodule.span K {climbRead (windowPairs cal x t₀ s) (Q.hv t)} := by
    intro s hts hsB Q hQ t htat htle
    have h := window_read_directed h_irred B hn hb₀ hb₀x hcal ht₀B hxt₀
      (hw1 t htat) (hw2 t htat) hts hsB (hQc (win t htat) (hw2 t htat)) hQ
      htat (hw3 t htat) htle
    simp only [hhv, dif_pos htat]
    exact h
  refine ⟨hvlim, hstab, ?_, ?_, ?_, ?_⟩
  · intro p hp hpx
    simp only [hhv, dif_pos hp]
    rw [IsClimb.hv_of_le _ x n P _ (hQc (win p hp) (hw2 p hp)) p hpx,
      climbRead_pad]
  · intro p hp
    simp only [hhv, dif_pos hp]
    intro h0
    have h1 : (Qc (win p hp) (hw2 p hp)).hv p = 0 := by
      apply hinj (win p hp)
      rw [h0, map_zero]
    exact (Qc (win p hp) (hw2 p hp)).ne_zero hp (hw3 p hp) h1
  · intro p q hp hq hpq hmem
    have hts : t₀ ⊆ win p hp ∪ win q hq :=
      (hw1 p hp).trans Finset.subset_union_left
    have hsB : ↑(win p hp ∪ win q hq) ⊆ B.carrier := by
      rw [Finset.coe_union]
      exact Set.union_subset (hw2 p hp) (hw2 q hq)
    have hple := hflat_mono (hw1 p hp)
      (Finset.subset_union_left : win p hp ⊆ win p hp ∪ win q hq) (hw3 p hp)
    have hqle := hflat_mono (hw1 q hq)
      (Finset.subset_union_right : win q hq ⊆ win p hp ∪ win q hq) (hw3 q hq)
    have hsp := hstab _ hts hsB (Qc _ hsB) (hQc _ hsB) p hp hple
    have hsq := hstab _ hts hsB (Qc _ hsB) (hQc _ hsB) q hq hqle
    have h1 : climbRead (windowPairs cal x t₀ (win p hp ∪ win q hq))
        ((Qc _ hsB).hv q) ∈ Submodule.span K
          {climbRead (windowPairs cal x t₀ (win p hp ∪ win q hq))
            ((Qc _ hsB).hv p)} := by
      rw [← hsp]
      refine (Submodule.span_singleton_le_iff_mem _ _).mpr hmem ?_
      rw [hsq]
      exact Submodule.mem_span_singleton_self _
    exact (Qc _ hsB).span_inj hp hple hq hqle hpq
      ((map_mem_span_singleton_iff (hinj _)).mp h1)
  · intro p q r hp hq hr hpq
    have hts : t₀ ⊆ win p hp ∪ win q hq ∪ win r hr :=
      (hw1 p hp).trans
        ((Finset.subset_union_left : win p hp ⊆ win p hp ∪ win q hq).trans
          Finset.subset_union_left)
    have hsB : ↑(win p hp ∪ win q hq ∪ win r hr) ⊆ B.carrier := by
      rw [Finset.coe_union, Finset.coe_union]
      exact Set.union_subset
        (Set.union_subset (hw2 p hp) (hw2 q hq)) (hw2 r hr)
    have hple := hflat_mono (hw1 p hp)
      ((Finset.subset_union_left : win p hp ⊆ win p hp ∪ win q hq).trans
        (Finset.subset_union_left :
          win p hp ∪ win q hq ⊆ win p hp ∪ win q hq ∪ win r hr)) (hw3 p hp)
    have hqle := hflat_mono (hw1 q hq)
      ((Finset.subset_union_right : win q hq ⊆ win p hp ∪ win q hq).trans
        (Finset.subset_union_left :
          win p hp ∪ win q hq ⊆ win p hp ∪ win q hq ∪ win r hr)) (hw3 q hq)
    have hrle := hflat_mono (hw1 r hr)
      (Finset.subset_union_right :
        win r hr ⊆ win p hp ∪ win q hq ∪ win r hr) (hw3 r hr)
    have hsp := hstab _ hts hsB (Qc _ hsB) (hQc _ hsB) p hp hple
    have hsq := hstab _ hts hsB (Qc _ hsB) (hQc _ hsB) q hq hqle
    have hsr := hstab _ hts hsB (Qc _ hsB) (hQc _ hsB) r hr hrle
    rw [(Qc _ hsB).collinear_iff hp hple hq hqle hr hrle hpq]
    exact (map_mem_span_pair_iff (hinj _)).symm.trans
      (mem_span_pair_congr hsp.symm hsq.symm hsr.symm)

end Limit

end Foam.Bridges

/-! ## Axiom audit -/

/-- info: 'Foam.Bridges.limit_read_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.limit_read_exists
