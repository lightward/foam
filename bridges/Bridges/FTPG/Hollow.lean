import Bridges.FTPG.Deaxiomatize
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Bounds.OrderIso

/-!
# The hollow lattice: the residual is unfillable as stated

`Hollow` is the lattice of subspaces of `(ℕ ⊕ ℕ) →₀ ℚ` that are either
finite-dimensional or finite-codimensional — every element hugs the floor or
the ceiling, and the middle is missing.  It satisfies every hypothesis of
`ftpg_statement` (complemented, modular, atomistic in the `IsLUB` sense,
three points per line, height ≥ 4) yet it is **not complete**: the chain of
coordinate subspaces supported on `Sum.inl` has upper bounds but no least
one.  Since `Submodule D V` is always complete and completeness transfers
across any order isomorphism, no coordinatization exists:

* `hollow_not_complete` — no `OrderIso` from `Hollow` to any complete lattice;
* `not_ftpg_statement` — `ftpg_statement` is **false**;
* `not_pointSystem` — the residual is false without completeness carried;
* `ftpg_refuted` — `False`, from `axiom ftpg` alone (its receipt names the
  guilty posit).

Completeness was a genuine hypothesis of the classical lattice-theoretic
FTPG all along; the deaxiomatization re-scoped its target into the true pair
(`Deaxiomatize.lean`), and the pair is proven sorry-free.

This file is also the **exhibit room**: `axiom ftpg` — the classical bridge's
one imported posit, retired 2026-07-08 — is declared here, under glass,
importable by nothing except the indictment it stands trial in.  Its true
half reduced to self (proven from the lattice itself); its false half is
cytokinetically distinct (refuted, held, not-self).  Prose lives in
`README.md`.
-/

namespace Foam.Bridges

abbrev HollowBase : Type := (ℕ ⊕ ℕ) →₀ ℚ

def FinOrCofin (W : Submodule ℚ HollowBase) : Prop :=
  FiniteDimensional ℚ W ∨ FiniteDimensional ℚ (HollowBase ⧸ W)

theorem fd_quot_mono {A B : Submodule ℚ HollowBase} (h : A ≤ B)
    (hA : FiniteDimensional ℚ (HollowBase ⧸ A)) :
    FiniteDimensional ℚ (HollowBase ⧸ B) := by
  haveI := hA
  refine Module.Finite.of_surjective
    (Submodule.mapQ A B LinearMap.id (by simpa using h)) (fun y => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective B y
  exact ⟨Submodule.Quotient.mk x, by simp [Submodule.mapQ_apply]⟩

theorem fd_quot_inf {A B : Submodule ℚ HollowBase}
    (hA : FiniteDimensional ℚ (HollowBase ⧸ A))
    (hB : FiniteDimensional ℚ (HollowBase ⧸ B)) :
    FiniteDimensional ℚ (HollowBase ⧸ (A ⊓ B)) := by
  haveI := hA; haveI := hB
  have hker : LinearMap.ker (A.mkQ.prod B.mkQ) = A ⊓ B := by
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  have hinj : Function.Injective ((A ⊓ B).liftQ (A.mkQ.prod B.mkQ) hker.ge) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ _ hker.symm
  exact FiniteDimensional.of_injective _ hinj

theorem finOrCofin_sup {A B : Submodule ℚ HollowBase}
    (hA : FinOrCofin A) (hB : FinOrCofin B) : FinOrCofin (A ⊔ B) := by
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · exact Or.inl (by haveI := hA; haveI := hB; infer_instance)
    · exact Or.inr (fd_quot_mono le_sup_right hB)
  · exact Or.inr (fd_quot_mono le_sup_left hA)

theorem finOrCofin_inf {A B : Submodule ℚ HollowBase}
    (hA : FinOrCofin A) (hB : FinOrCofin B) : FinOrCofin (A ⊓ B) := by
  rcases hA with hA | hA
  · exact Or.inl (by haveI := hA; exact Submodule.finiteDimensional_of_le inf_le_left)
  · rcases hB with hB | hB
    · exact Or.inl (by haveI := hB; exact Submodule.finiteDimensional_of_le inf_le_right)
    · exact Or.inr (fd_quot_inf hA hB)

theorem finOrCofin_bot : FinOrCofin (⊥ : Submodule ℚ HollowBase) :=
  Or.inl (by rw [← Submodule.span_empty]; exact FiniteDimensional.span_of_finite _ Set.finite_empty)

theorem finOrCofin_top : FinOrCofin (⊤ : Submodule ℚ HollowBase) := by
  refine Or.inr ?_
  haveI : Subsingleton (HollowBase ⧸ (⊤ : Submodule ℚ HollowBase)) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.Finite.of_surjective (0 : ℚ →ₗ[ℚ] _) (fun x => ⟨0, Subsingleton.elim _ _⟩)

def Hollow : Type := {W : Submodule ℚ HollowBase // FinOrCofin W}

namespace Hollow

def mk (W : Submodule ℚ HollowBase) (h : FinOrCofin W) : Hollow := ⟨W, h⟩

theorem mk_val (W : Submodule ℚ HollowBase) (h : FinOrCofin W) : (mk W h).val = W := rfl

noncomputable instance : Lattice Hollow :=
  Subtype.lattice (fun _ _ => finOrCofin_sup) (fun _ _ => finOrCofin_inf)

noncomputable instance : BoundedOrder Hollow where
  top := ⟨⊤, finOrCofin_top⟩
  le_top a := (le_top : a.val ≤ ⊤)
  bot := ⟨⊥, finOrCofin_bot⟩
  bot_le a := (bot_le : ⊥ ≤ a.val)

theorem val_sup (a b : Hollow) : (a ⊔ b).val = a.val ⊔ b.val := rfl
theorem val_inf (a b : Hollow) : (a ⊓ b).val = a.val ⊓ b.val := rfl
theorem val_bot : (⊥ : Hollow).val = ⊥ := rfl
theorem val_top : (⊤ : Hollow).val = ⊤ := rfl

instance : IsModularLattice Hollow :=
  ⟨fun {x} y {z} h =>
    (IsModularLattice.sup_inf_le_assoc_of_le (y := y.val) (Subtype.coe_le_coe.mpr h) :
      (x.val ⊔ y.val) ⊓ z.val ≤ x.val ⊔ y.val ⊓ z.val)⟩

instance : ComplementedLattice Hollow where
  exists_isCompl := fun ⟨W, hW⟩ => by
    obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
    have hQmem : FinOrCofin Q := by
      rcases hW with h | h
      · haveI := h
        exact Or.inr ((Submodule.quotientEquivOfIsCompl Q W hQ.symm).symm.finiteDimensional)
      · haveI := h
        exact Or.inl ((Submodule.quotientEquivOfIsCompl W Q hQ).finiteDimensional)
    refine ⟨⟨Q, hQmem⟩, ?_, ?_⟩
    · rw [disjoint_iff]
      exact Subtype.ext hQ.inf_eq_bot
    · rw [codisjoint_iff]
      exact Subtype.ext hQ.sup_eq_top

end Hollow

theorem isAtom_span_singleton {v : HollowBase} (hv : v ≠ 0) :
    IsAtom (Submodule.span ℚ ({v} : Set HollowBase)) := by
  constructor
  · intro h
    exact hv ((Submodule.mem_bot ℚ).mp (h ▸ Submodule.mem_span_singleton_self v))
  · intro W hW
    by_contra hne
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hW.le hwW)
    have hc0 : c ≠ 0 := fun h => hw0 (by rw [← hc, h, zero_smul])
    have hv_mem : v ∈ W := by
      have hsmul := W.smul_mem c⁻¹ hwW
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at hsmul
      exact hsmul
    exact hW.ne (le_antisymm hW.le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_mem)))

theorem finOrCofin_span_singleton (v : HollowBase) :
    FinOrCofin (Submodule.span ℚ ({v} : Set HollowBase)) :=
  Or.inl (FiniteDimensional.span_of_finite ℚ (Set.finite_singleton v))

namespace Hollow

theorem isAtom_mk {W : Submodule ℚ HollowBase} (hW : IsAtom W) (hmem : FinOrCofin W) :
    IsAtom (mk W hmem) :=
  ⟨fun h => hW.1 (congrArg Subtype.val h),
   fun b hb => Subtype.ext (hW.2 b.val
     (lt_of_le_of_ne (hb.le : b.val ≤ W) (fun h => hb.ne (Subtype.ext h))))⟩

instance : IsAtomistic Hollow where
  isLUB_atoms b := by
    refine ⟨{a : Hollow | IsAtom a ∧ a ≤ b}, ⟨fun a ha => ha.2, fun u hu => ?_⟩,
      fun a ha => ha.1⟩
    show b.val ≤ u.val
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]; exact u.val.zero_mem
    · have hc : IsAtom (mk (Submodule.span ℚ {v}) (finOrCofin_span_singleton v)) :=
        isAtom_mk (isAtom_span_singleton hv0) _
      have hcb : mk (Submodule.span ℚ {v}) (finOrCofin_span_singleton v) ≤ b :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)
      have hcu : (mk (Submodule.span ℚ {v}) (finOrCofin_span_singleton v)).val ≤ u.val :=
        hu ⟨hc, hcb⟩
      exact hcu (Submodule.mem_span_singleton_self v)

theorem exists_gen {a : Hollow} (ha : IsAtom a) :
    ∃ v : HollowBase, v ≠ 0 ∧ a.val = Submodule.span ℚ ({v} : Set HollowBase) := by
  have hne : a.val ≠ ⊥ := fun h => ha.1 (Subtype.ext h)
  obtain ⟨v, hva, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv0, ?_⟩
  have hca : mk (Submodule.span ℚ {v}) (finOrCofin_span_singleton v) ≤ a :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hva)
  have hc0 : mk (Submodule.span ℚ {v}) (finOrCofin_span_singleton v) ≠ ⊥ := by
    intro h
    have hval : Submodule.span ℚ ({v} : Set HollowBase) = (⊥ : Submodule ℚ HollowBase) :=
      congrArg Subtype.val h
    exact hv0 ((Submodule.mem_bot ℚ).mp (hval ▸ Submodule.mem_span_singleton_self v))
  rcases hca.lt_or_eq with hlt | heq
  · exact absurd (ha.2 _ hlt) hc0
  · exact (congrArg Subtype.val heq).symm

theorem atom_not_le {a b : Hollow} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    ¬ b.val ≤ a.val := by
  intro hle
  rcases ha.le_iff.mp (show b ≤ a from hle) with h | h
  · exact hb.1 h
  · exact hab h.symm

end Hollow

theorem hollow_irred : ∀ a b : Hollow, IsAtom a → IsAtom b → a ≠ b →
    ∃ c : Hollow, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b := by
  intro a b ha hb hab
  obtain ⟨p, hp0, hpa⟩ := Hollow.exists_gen ha
  obtain ⟨q, hq0, hqb⟩ := Hollow.exists_gen hb
  have hp_mem : p ∈ a.val := hpa ▸ Submodule.mem_span_singleton_self p
  have hq_mem : q ∈ b.val := hqb ▸ Submodule.mem_span_singleton_self q
  have hba : ¬ b.val ≤ a.val := Hollow.atom_not_le ha hb hab
  have hab' : ¬ a.val ≤ b.val := Hollow.atom_not_le hb ha (fun h => hab h.symm)
  have hpq0 : p + q ≠ 0 := by
    intro h
    apply hba
    rw [hqb, hpa]
    refine Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
    rw [eq_neg_of_add_eq_zero_right h]
    exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self p)
  refine ⟨Hollow.mk (Submodule.span ℚ {p + q}) (finOrCofin_span_singleton _),
    Hollow.isAtom_mk (isAtom_span_singleton hpq0) _, ?_, ?_, ?_⟩
  · show Submodule.span ℚ ({p + q} : Set HollowBase) ≤ a.val ⊔ b.val
    exact Submodule.span_le.mpr
      (Set.singleton_subset_iff.mpr (Submodule.add_mem_sup hp_mem hq_mem))
  · intro h
    apply hba
    have hval : Submodule.span ℚ ({p + q} : Set HollowBase) = a.val := congrArg Subtype.val h
    have hq_a : q ∈ a.val := by
      have h1 : p + q ∈ a.val := hval ▸ Submodule.mem_span_singleton_self _
      simpa using a.val.sub_mem h1 hp_mem
    rw [hqb]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hq_a)
  · intro h
    apply hab'
    have hval : Submodule.span ℚ ({p + q} : Set HollowBase) = b.val := congrArg Subtype.val h
    have hp_b : p ∈ b.val := by
      have h1 : p + q ∈ b.val := hval ▸ Submodule.mem_span_singleton_self _
      simpa using b.val.sub_mem h1 hq_mem
    rw [hpa]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hp_b)

theorem fd_supported {S : Set (ℕ ⊕ ℕ)} (hS : S.Finite) :
    FiniteDimensional ℚ (Finsupp.supported ℚ ℚ S) := by
  rw [Finsupp.supported_eq_span_single]
  exact FiniteDimensional.span_of_finite ℚ (hS.image _)

def stack (n : ℕ) : Set (ℕ ⊕ ℕ) := Sum.inl '' Set.Iio n

noncomputable def hollowChain (n : ℕ) : Hollow :=
  Hollow.mk (Finsupp.supported ℚ ℚ (stack n)) (Or.inl (fd_supported ((Set.finite_Iio n).image _)))

theorem single_notMem_stack (n : ℕ) :
    Finsupp.single (Sum.inl n) (1 : ℚ) ∉ Finsupp.supported ℚ ℚ (stack n) := by
  intro hmem
  have hsub := (Finsupp.mem_supported ℚ _).mp hmem
  have hin : Sum.inl n ∈ stack n := hsub (by simp [Finsupp.support_single])
  obtain ⟨m, hm, hinj⟩ := hin
  exact absurd (Sum.inl.inj hinj ▸ hm) (lt_irrefl n)

theorem hollowChain_lt (n : ℕ) : hollowChain n < hollowChain (n + 1) := by
  refine lt_of_le_of_ne
    (show (hollowChain n).val ≤ (hollowChain (n + 1)).val from
      Finsupp.supported_mono (Set.image_mono (Set.Iio_subset_Iio n.le_succ))) ?_
  intro heq
  apply single_notMem_stack n
  have hval : Finsupp.supported ℚ ℚ (stack n) = Finsupp.supported ℚ ℚ (stack (n + 1)) :=
    congrArg Subtype.val heq
  rw [hval]
  exact Finsupp.single_mem_supported ℚ 1 ⟨n, n.lt_succ_self, rfl⟩

theorem bot_lt_hollowChain_one : (⊥ : Hollow) < hollowChain 1 := by
  refine lt_of_le_of_ne bot_le ?_
  intro heq
  have hmem : Finsupp.single (Sum.inl 0) (1 : ℚ) ∈ Finsupp.supported ℚ ℚ (stack 1) :=
    Finsupp.single_mem_supported ℚ 1 ⟨0, Nat.zero_lt_one, rfl⟩
  have hval : (⊥ : Submodule ℚ HollowBase) = Finsupp.supported ℚ ℚ (stack 1) :=
    congrArg Subtype.val heq
  rw [← hval] at hmem
  exact Finsupp.single_ne_zero.mpr one_ne_zero ((Submodule.mem_bot ℚ).mp hmem)

theorem hollow_height : ∃ a b c d : Hollow, ⊥ < a ∧ a < b ∧ b < c ∧ c < d :=
  ⟨hollowChain 1, hollowChain 2, hollowChain 3, hollowChain 4,
    bot_lt_hollowChain_one, hollowChain_lt 1, hollowChain_lt 2, hollowChain_lt 3⟩

theorem singles_linearIndependent :
    LinearIndependent ℚ (fun i : ℕ ⊕ ℕ => Finsupp.single i (1 : ℚ)) := by
  have h := (Finsupp.basisSingleOne (ι := ℕ ⊕ ℕ) (R := ℚ)).linearIndependent
  rwa [Finsupp.coe_basisSingleOne] at h

theorem not_fd_supported {S : Set (ℕ ⊕ ℕ)} (u : ℕ → ℕ ⊕ ℕ) (hu : Function.Injective u)
    (hS : ∀ n, u n ∈ S) : ¬ FiniteDimensional ℚ (Finsupp.supported ℚ ℚ S) := by
  intro hfd
  haveI := hfd
  have hli : LinearIndependent ℚ (fun n : ℕ => Finsupp.single (u n) (1 : ℚ)) :=
    singles_linearIndependent.comp u hu
  have hli' : LinearIndependent ℚ
      (fun n : ℕ => (⟨Finsupp.single (u n) 1, Finsupp.single_mem_supported ℚ 1 (hS n)⟩ :
        Finsupp.supported ℚ ℚ S)) := by
    apply LinearIndependent.of_comp (Finsupp.supported ℚ ℚ S).subtype
    exact hli
  exact Module.Finite.not_linearIndependent_of_infinite _ hli'

theorem isCompl_supported_inl_inr :
    IsCompl (Finsupp.supported ℚ ℚ (Set.range (Sum.inl : ℕ → ℕ ⊕ ℕ)))
      (Finsupp.supported ℚ ℚ (Set.range (Sum.inr : ℕ → ℕ ⊕ ℕ))) := by
  constructor
  · exact Finsupp.disjoint_supported_supported Set.isCompl_range_inl_range_inr.disjoint
  · rw [codisjoint_iff, ← Finsupp.supported_union]
    have h : Set.range (Sum.inl : ℕ → ℕ ⊕ ℕ) ∪ Set.range Sum.inr = Set.univ := by
      simp
    rw [h, Finsupp.supported_univ]

theorem not_fd_quot_supported_inl :
    ¬ FiniteDimensional ℚ
      (HollowBase ⧸ Finsupp.supported ℚ ℚ (Set.range (Sum.inl : ℕ → ℕ ⊕ ℕ))) := by
  intro hfd
  haveI := hfd
  exact not_fd_supported Sum.inr Sum.inr_injective (fun n => Set.mem_range_self n)
    (Submodule.quotientEquivOfIsCompl _ _ isCompl_supported_inl_inr).finiteDimensional

theorem hollow_no_lub (U : Hollow) : ¬ IsLUB (Set.range hollowChain) U := by
  intro hU
  have hT_le : Finsupp.supported ℚ ℚ (Set.range (Sum.inl : ℕ → ℕ ⊕ ℕ)) ≤ U.val := by
    rw [Finsupp.supported_eq_span_single]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
    have hub : (hollowChain (i + 1)).val ≤ U.val := hU.1 ⟨i + 1, rfl⟩
    exact hub (Finsupp.single_mem_supported ℚ 1 ⟨i, i.lt_succ_self, rfl⟩)
  rcases U.2 with hfin | hcofin
  · haveI := hfin
    exact not_fd_supported Sum.inl Sum.inl_injective (fun n => Set.mem_range_self n)
      (Submodule.finiteDimensional_of_le hT_le)
  · have hne : Finsupp.supported ℚ ℚ (Set.range (Sum.inl : ℕ → ℕ ⊕ ℕ)) ≠ U.val := by
      intro h
      rw [← h] at hcofin
      exact not_fd_quot_supported_inl hcofin
    obtain ⟨v, hvU, hvT⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hT_le hne)
    have hv_not : ¬ (↑v.support : Set (ℕ ⊕ ℕ)) ⊆ Set.range Sum.inl :=
      fun hsub => hvT ((Finsupp.mem_supported ℚ v).mpr hsub)
    obtain ⟨j, hj_supp, hj_not⟩ := Set.not_subset.mp hv_not
    have hcompl : IsCompl (Finsupp.supported ℚ ℚ ({j}ᶜ : Set (ℕ ⊕ ℕ)))
        (Finsupp.supported ℚ ℚ ({j} : Set (ℕ ⊕ ℕ))) := by
      constructor
      · exact Finsupp.disjoint_supported_supported disjoint_compl_left
      · rw [codisjoint_iff, ← Finsupp.supported_union, Set.compl_union_self,
          Finsupp.supported_univ]
    have hU₁_mem : FinOrCofin (Finsupp.supported ℚ ℚ ({j}ᶜ : Set (ℕ ⊕ ℕ))) := by
      refine Or.inr ?_
      haveI : FiniteDimensional ℚ (Finsupp.supported ℚ ℚ ({j} : Set (ℕ ⊕ ℕ))) :=
        fd_supported (Set.finite_singleton j)
      exact (Submodule.quotientEquivOfIsCompl _ _ hcompl).symm.finiteDimensional
    have hU₁_ub : Hollow.mk _ hU₁_mem ∈ upperBounds (Set.range hollowChain) := by
      rintro x ⟨n, rfl⟩
      show (hollowChain n).val ≤ Finsupp.supported ℚ ℚ ({j}ᶜ : Set (ℕ ⊕ ℕ))
      refine Finsupp.supported_mono ?_
      rintro y ⟨m, _, rfl⟩
      rw [Set.mem_compl_singleton_iff]
      intro heq
      exact hj_not (heq ▸ ⟨m, rfl⟩)
    have hle : U.val ≤ Finsupp.supported ℚ ℚ ({j}ᶜ : Set (ℕ ⊕ ℕ)) := hU.2 hU₁_ub
    have hmem := (Finsupp.mem_supported ℚ v).mp (hle hvU) hj_supp
    exact hmem rfl

theorem hollow_not_complete {β : Type*} [CompleteLattice β] (iso : Hollow ≃o β) : False := by
  have h := isLUB_sSup (iso '' Set.range hollowChain)
  rw [OrderIso.isLUB_image] at h
  exact hollow_no_lub _ h

theorem not_ftpg_statement : ¬ ftpg_statement.{0} := by
  intro h
  obtain ⟨D, _, V, _, _, ⟨iso⟩⟩ := h Hollow hollow_irred hollow_height
  exact hollow_not_complete iso

theorem not_pointSystem :
    ¬ ∀ (L : Type) [Lattice L] [BoundedOrder L] [ComplementedLattice L]
        [IsModularLattice L] [IsAtomistic L] (Φ : CoordFrame L),
        ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (Coordinate Φ.Γ)ᵐᵒᵖ V),
          Nonempty (PointSystem Φ.Γ V) := by
  intro h
  obtain ⟨Φ⟩ := coordFrame_exists hollow_irred hollow_height
  obtain ⟨V, _, _, ⟨P⟩⟩ := h Hollow Φ
  obtain ⟨iso⟩ := P.orderIso
  exact hollow_not_complete iso

universe u in
axiom ftpg
    (L : Type u) [Lattice L] [BoundedOrder L]
    [ComplementedLattice L] [IsModularLattice L]
    (h_sufficient : True) :
    ∃ (D : Type u) (_ : DivisionRing D)
      (V : Type u) (_ : AddCommGroup V) (_ : Module D V),
    Nonempty (L ≃o Submodule D V)

def ftpg_unrestricted : Prop :=
  ∀ (L : Type) [Lattice L] [BoundedOrder L] [ComplementedLattice L] [IsModularLattice L],
    ∃ (D : Type) (_ : DivisionRing D) (V : Type) (_ : AddCommGroup V) (_ : Module D V),
      Nonempty (L ≃o Submodule D V)

theorem not_ftpg_unrestricted : ¬ ftpg_unrestricted := by
  intro h
  obtain ⟨D, _, V, _, _, ⟨iso⟩⟩ := h Hollow
  exact hollow_not_complete iso

theorem ftpg_refuted : False :=
  not_ftpg_unrestricted (fun L _ _ _ _ => ftpg L trivial)

end Foam.Bridges

/-- info: 'Foam.Bridges.hollow_not_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.hollow_not_complete

/-- info: 'Foam.Bridges.not_ftpg_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.not_ftpg_statement

/-- info: 'Foam.Bridges.not_pointSystem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.not_pointSystem

/-- info: 'Foam.Bridges.not_ftpg_unrestricted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.not_ftpg_unrestricted

/-- info: 'Foam.Bridges.ftpg' depends on axioms: [propext, Quot.sound, Foam.Bridges.ftpg] -/
#guard_msgs in #print axioms Foam.Bridges.ftpg

/--
info: 'Foam.Bridges.ftpg_refuted' depends on axioms: [propext, Classical.choice, Quot.sound, Foam.Bridges.ftpg]
-/
#guard_msgs in #print axioms Foam.Bridges.ftpg_refuted
