import Bridges.FTPG.Limit
import Bridges.FTPG.Iso

/-!
# Camp four, the spanning stratum: the flats law and the point system at the limit

Stage four of the `pointSystem_exists` ascent — `closed` and `spanning`, the
two `PointSystem` fields, from the limit assignment's stability alone.

* **the modular lever** (`line_meets_flat`): in a modular lattice, an atom
  inside `y ⊔ q` (but in neither part) sees the line `p ⊔ q` meet the flat
  `y` in an atom — the classical "a line meets a hyperplane", at the grain
  the flats induction walks on.  Pure modular law: the meet is
  `y ⊓ (p ⊔ q)`, its atomhood one covering plus two modular moves.
* **the flats law** (`PointSys.flat_le_iff`): the four `PointSys` laws
  generate the whole finite matroid — an atom lies below a finite join of
  atoms iff its vector lies in the span of theirs.  `collinear_iff` is the
  two-point case; the induction climbs one atom at a time, the lever
  supplying the geometric step forward and `span_surj` conjuring the
  intermediate atom backward.
* **the span calculus** (`mem_span_congr`, `span_image_congr`,
  `map_mem_span_image_iff`): span-level agreement of generators moves
  membership across sets, and an injective linear map reflects it — the
  finite-set generalization of the pair calculus `Window.lean` seated.
* **the summit** (`limit_system_exists`): over the limit assignment `hv`
  (one choice per atom, `Limit.lean`), the carrier `V` is the span of the
  read-image inside the named slot space, `pt` is the line of each atom's
  read, and the two residual fields close: `closed` because membership in a
  span is finitely supported (`mem_span_finite_of_mem_span`), the finitely
  many witnesses meet `p` inside one window, and the window's flats law
  reflects back through the read; `spanning` because every submodule of `V`
  is recovered at `sSup` of the atoms it holds — downward by compactness of
  atoms plus the flats law, upward because every nonzero vector of `V` is
  span-equal to some atom's read (the window's own `span_surj`, transported
  by stability).  Only the stability clause of `limit_read_exists` is
  consumed: the window systems carry all four laws themselves.

Model-verified the previous sitting (`probe_limit.py`, check F): the limit
map from one arbitrary representative per atom satisfies all four laws
globally — `span_surj` onto the full slot space included — over five window
configurations at `q ∈ {2,3}`, twisted base systems throughout.
-/

namespace Foam.Bridges

universe u v

/-! ## The modular lever: a line through a fresh atom meets the flat -/

section Lever

variable {L : Type u} [Lattice L] [OrderBot L] [IsModularLattice L]

theorem line_meets_flat {p q y : L} (hp : IsAtom p) (hq : IsAtom q)
    (hpq : p ≠ q) (hple : p ≤ y ⊔ q) (hqy : ¬ q ≤ y) :
    ∃ r : L, IsAtom r ∧ r ≤ y ∧ p ≤ q ⊔ r := by
  have hpq_le : p ⊔ q ≤ q ⊔ y := sup_le (hple.trans (sup_comm y q).le) le_sup_left
  have hqr : q ⊔ y ⊓ (p ⊔ q) = p ⊔ q := by
    rw [← sup_inf_assoc_of_le y (le_sup_right : q ≤ p ⊔ q),
      inf_eq_right.mpr hpq_le]
  have hq_inf : q ⊓ (y ⊓ (p ⊔ q)) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left q inf_le_left).trans
      (inf_eq_bot_of_atom_not_le hq hqy).le)
  have hrne : y ⊓ (p ⊔ q) ≠ ⊥ := by
    intro h0
    have hq_eq : q = p ⊔ q := by rw [← hqr, h0, sup_bot_eq]
    exact hpq (((hq.le_iff).mp (le_sup_left.trans hq_eq.ge)).resolve_left hp.1)
  have hqcov : q ⋖ p ⊔ q := by
    have hnpq : ¬ p ≤ q := fun h => hpq ((hq.le_iff.mp h).resolve_left hp.1)
    have h := covBy_sup_atom hp hnpq
    rwa [sup_comm] at h
  refine ⟨y ⊓ (p ⊔ q), ⟨hrne, fun s hs => ?_⟩, inf_le_left,
    by rw [hqr]; exact le_sup_left⟩
  by_cases hqlt : q < q ⊔ s
  · exfalso
    have hle2 : q ⊔ s ≤ p ⊔ q :=
      sup_le le_sup_right (hs.le.trans inf_le_right)
    have heq : q ⊔ s = p ⊔ q :=
      (lt_or_eq_of_le hle2).resolve_left (hqcov.2 hqlt)
    have hmod := sup_inf_assoc_of_le q (hs.le : s ≤ y ⊓ (p ⊔ q))
    rw [hq_inf, sup_bot_eq] at hmod
    refine hs.ne ?_
    rw [← hmod, sup_comm s q, heq, inf_eq_right.mpr inf_le_right]
  · have hqs_eq : q = q ⊔ s := le_sup_left.eq_of_not_lt hqlt
    have hsq : s ≤ q := le_sup_right.trans hqs_eq.ge
    exact le_bot_iff.mp ((le_inf hsq hs.le).trans hq_inf.le)

end Lever

/-! ## The span calculus: agreement of generators moves membership -/

section SpanCalculus

variable {K : Type v} [DivisionRing K] {M N : Type*}
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem mem_span_congr {c c' : M} {S S' : Set M}
    (hc : Submodule.span K {c} = Submodule.span K {c'})
    (hS : Submodule.span K S = Submodule.span K S') :
    c ∈ Submodule.span K S ↔ c' ∈ Submodule.span K S' := by
  rw [← Submodule.span_singleton_le_iff_mem, ← Submodule.span_singleton_le_iff_mem,
    hc, hS]

theorem span_image_congr {α : Type*} {s : Set α} {f g : α → M}
    (h : ∀ i ∈ s, Submodule.span K {f i} = Submodule.span K {g i}) :
    Submodule.span K (f '' s) = Submodule.span K (g '' s) := by
  apply le_antisymm <;> rw [Submodule.span_le] <;> rintro w ⟨i, hi, rfl⟩
  · have h1 : f i ∈ Submodule.span K {g i} := by
      rw [← h i hi]
      exact Submodule.mem_span_singleton_self _
    exact Submodule.span_mono
      (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem g hi)) h1
  · have h1 : g i ∈ Submodule.span K {f i} := by
      rw [h i hi]
      exact Submodule.mem_span_singleton_self _
    exact Submodule.span_mono
      (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem f hi)) h1

theorem map_mem_span_image_iff {f : M →ₗ[K] N} (hf : Function.Injective f)
    {s : Set M} {v : M} :
    f v ∈ Submodule.span K (f '' s) ↔ v ∈ Submodule.span K s := by
  rw [Submodule.span_image, Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, huv⟩
    rwa [← hf huv]
  · exact fun h => ⟨v, h, rfl⟩

end SpanCalculus

/-! ## The flats law: the four laws generate the finite matroid -/

section Flats

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L]
variable {K : Type v} [DivisionRing K] [DecidableEq L]

theorem PointSys.mem_span_of_le_sup {x : L} {n : ℕ} (P : PointSys x n K)
    (t : Finset L) :
    (∀ q ∈ t, IsAtom q) → (∀ q ∈ t, q ≤ x) →
    ∀ p : L, IsAtom p → p ≤ x → p ≤ t.sup id →
    P.hv p ∈ Submodule.span K (P.hv '' ↑t) := by
  induction t using Finset.induction_on with
  | empty =>
    intro _ _ p hp _ hple
    rw [Finset.sup_empty] at hple
    exact absurd (le_bot_iff.mp hple) hp.1
  | insert a s ha ih =>
    intro hta htx p hp hpx hple
    have haa : IsAtom a := hta a (Finset.mem_insert_self a s)
    have hax : a ≤ x := htx a (Finset.mem_insert_self a s)
    have hsa : ∀ q ∈ s, IsAtom q := fun q hq => hta q (Finset.mem_insert_of_mem hq)
    have hsx : ∀ q ∈ s, q ≤ x := fun q hq => htx q (Finset.mem_insert_of_mem hq)
    have himg : Submodule.span K (P.hv '' ↑s)
        ≤ Submodule.span K (P.hv '' ↑(insert a s)) :=
      Submodule.span_mono (Set.image_mono
        (by rw [Finset.coe_insert]; exact Set.subset_insert a ↑s))
    rw [Finset.sup_insert, id_eq] at hple
    by_cases hps : p ≤ s.sup id
    · exact himg (ih hsa hsx p hp hpx hps)
    by_cases hpa : p = a
    · exact Submodule.subset_span
        ⟨a, by rw [Finset.coe_insert]; exact Set.mem_insert a ↑s, hpa ▸ rfl⟩
    have has : ¬ a ≤ s.sup id := fun h => hps (hple.trans (sup_le h le_rfl))
    obtain ⟨r, hr, hrs, hpar⟩ :=
      line_meets_flat hp haa hpa (by rwa [sup_comm] at hple) has
    have hrx : r ≤ x := hrs.trans (Finset.sup_le fun q hq => hsx q hq)
    have hrmem := ih hsa hsx r hr hrx hrs
    have har : a ≠ r := fun h => has (h ▸ hrs)
    have hcol := (P.collinear_iff haa hax hr hrx hp hpx har).mp hpar
    refine Submodule.span_le.mpr ?_ hcol
    rintro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw'
    · exact Submodule.subset_span
        ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_self a s), rfl⟩
    · rw [Set.mem_singleton_iff.mp hw']
      exact himg hrmem

omit [IsModularLattice L] in
theorem PointSys.le_sup_of_mem_span {x : L} {n : ℕ} (P : PointSys x n K)
    (t : Finset L) :
    (∀ q ∈ t, IsAtom q) → (∀ q ∈ t, q ≤ x) →
    ∀ p : L, IsAtom p → p ≤ x →
    P.hv p ∈ Submodule.span K (P.hv '' ↑t) → p ≤ t.sup id := by
  induction t using Finset.induction_on with
  | empty =>
    intro _ _ p hp hpx hmem
    rw [Finset.coe_empty, Set.image_empty, Submodule.span_empty,
      Submodule.mem_bot] at hmem
    exact absurd hmem (P.ne_zero hp hpx)
  | insert a s ha ih =>
    intro hta htx p hp hpx hmem
    have haa : IsAtom a := hta a (Finset.mem_insert_self a s)
    have hax : a ≤ x := htx a (Finset.mem_insert_self a s)
    have hsa : ∀ q ∈ s, IsAtom q := fun q hq => hta q (Finset.mem_insert_of_mem hq)
    have hsx : ∀ q ∈ s, q ≤ x := fun q hq => htx q (Finset.mem_insert_of_mem hq)
    rw [Finset.coe_insert, Set.image_insert_eq] at hmem
    obtain ⟨c, z, hz, hpz⟩ := Submodule.mem_span_insert.mp hmem
    rw [Finset.sup_insert, id_eq]
    by_cases hz0 : z = 0
    · subst hz0
      rw [add_zero] at hpz
      by_cases hpa : p = a
      · exact hpa ▸ le_sup_left
      · exact absurd
          (hpz ▸ Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))
          (P.span_inj haa hax hp hpx (Ne.symm hpa))
    · obtain ⟨r, hr, hrX, hrspan⟩ := P.span_surj z hz0
      have hzr : z ∈ Submodule.span K {P.hv r} := by
        rw [hrspan]
        exact Submodule.mem_span_singleton_self z
      have hrmem : P.hv r ∈ Submodule.span K (P.hv '' ↑s) :=
        (Submodule.span_singleton_le_iff_mem _ _).mp
          (by rw [hrspan]
              exact (Submodule.span_singleton_le_iff_mem _ _).mpr hz)
      have hrs : r ≤ s.sup id := ih hsa hsx r hr hrX hrmem
      by_cases har : a = r
      · have hpmem : P.hv p ∈ Submodule.span K (P.hv '' ↑s) := by
          rw [hpz]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ c (har ▸ hrmem)) hz
        exact (ih hsa hsx p hp hpx hpmem).trans le_sup_right
      · have hra : P.hv r ∈ ({P.hv a, P.hv r} : Set (Fin n → K)) :=
          Set.mem_insert_of_mem _ (Set.mem_singleton _)
        have hz2 : z ∈ Submodule.span K ({P.hv a, P.hv r} : Set (Fin n → K)) :=
          Submodule.span_mono (Set.singleton_subset_iff.mpr hra) hzr
        have ha2 : P.hv a ∈ Submodule.span K ({P.hv a, P.hv r} : Set (Fin n → K)) :=
          Submodule.subset_span (Set.mem_insert _ _)
        have hpm : P.hv p ∈ Submodule.span K {P.hv a, P.hv r} := by
          rw [hpz]
          exact Submodule.add_mem _ (Submodule.smul_mem _ c ha2) hz2
        have hpar := (P.collinear_iff haa hax hr hrX hp hpx har).mpr hpm
        exact hpar.trans (sup_le_sup_left hrs a)

theorem PointSys.flat_le_iff {x : L} {n : ℕ} (P : PointSys x n K)
    {t : Finset L} (hta : ∀ q ∈ t, IsAtom q) (htx : ∀ q ∈ t, q ≤ x)
    {p : L} (hp : IsAtom p) (hpx : p ≤ x) :
    p ≤ t.sup id ↔ P.hv p ∈ Submodule.span K (P.hv '' ↑t) :=
  ⟨P.mem_span_of_le_sup t hta htx p hp hpx,
    P.le_sup_of_mem_span t hta htx p hp hpx⟩

end Flats

/-! ## The summit: the point system at the limit -/

section Summit

variable {L : Type u} [CompleteLattice L] [IsModularLattice L] [IsAtomistic L]
  [IsCompactlyGenerated L]
variable {K : Type v} [DivisionRing K] [DecidableEq L]

theorem limit_system_exists
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (B : AtomBasis L) {b₀ : L} {cal : L → L} {x : L} {t₀ : Finset L} {n : ℕ}
    (P : PointSys x n K)
    (hn : 3 ≤ n) (hb₀ : IsAtom b₀) (hb₀x : b₀ ≤ x) (hcal : CalSpec b₀ cal)
    (ht₀B : ↑t₀ ⊆ B.carrier) (hxt₀ : x ≤ t₀.sup id) :
    ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V)
      (pt : {p : L // IsAtom p} → Submodule K V),
      (∀ (p : {p : L // IsAtom p}) (y : L),
        pt p ≤ coordSpanFwd pt y → (p : L) ≤ y) ∧
      Function.Surjective (coordSpanFwd pt) := by
  classical
  obtain ⟨hv, hstab, -, -, -, -⟩ :=
    limit_read_exists h_irred B P hn hb₀ hb₀x hcal ht₀B hxt₀
  have hsupp_ex : ∀ a : L, ∃ t : Finset L, IsAtom a →
      ↑t ⊆ B.carrier ∧ a ≤ t.sup id := by
    intro a
    by_cases ha : IsAtom a
    · obtain ⟨t, h1, h2⟩ := B.exists_finset_support ha
      exact ⟨t, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨∅, fun h => absurd h ha⟩
  choose supp hsupp using hsupp_ex
  have hwinB : ∀ F : Finset L, (∀ a ∈ F, IsAtom a) →
      ↑(t₀ ∪ F.biUnion supp) ⊆ B.carrier := by
    intro F hF
    rw [Finset.coe_union, Finset.coe_biUnion]
    exact Set.union_subset ht₀B (Set.iUnion₂_subset fun a ha =>
      (hsupp a (hF a (Finset.mem_coe.mp ha))).1)
  have hwin_le : ∀ (F : Finset L) (hF : ∀ a ∈ F, IsAtom a) (a : L), a ∈ F →
      a ≤ climbFlat x (windowPairs cal x t₀ (t₀ ∪ F.biUnion supp)) := by
    intro F hF a ha
    rw [windowFlat_eq Finset.subset_union_left]
    refine le_sup_of_le_right (((hsupp a (hF a ha)).2).trans (Finset.sup_mono ?_))
    exact (Finset.subset_biUnion_of_mem supp ha).trans Finset.subset_union_right
  have hQex : ∀ F : Finset L, (∀ a ∈ F, IsAtom a) →
      ∃ Q : PointSys (climbFlat x (windowPairs cal x t₀ (t₀ ∪ F.biUnion supp)))
        (climbDim n (windowPairs cal x t₀ (t₀ ∪ F.biUnion supp))) K,
        IsClimb b₀ (windowPairs cal x t₀ (t₀ ∪ F.biUnion supp)) x n P Q :=
    fun F hF => isClimb_exists h_irred _ x n P hn hb₀ hb₀x
      (window_legal B hcal hb₀x ht₀B hxt₀ (hwinB F hF))
  choose QF hQF using hQex
  have hinj : ∀ s : Finset L,
      Function.Injective (climbRead (windowPairs cal x t₀ s) (K := K) (n := n)) := by
    intro s
    refine climbRead_injective _ ?_
    rw [windowPairs, calPairs_map_fst]
    exact windowList_nodup x t₀ s
  have hflat : ∀ (t : Finset L), (∀ a ∈ t, IsAtom a) → ∀ p : L, IsAtom p →
      (p ≤ t.sup id ↔ hv p ∈ Submodule.span K (hv '' ↑t)) := by
    intro t hta p hp
    have hFa : ∀ a ∈ insert p t, IsAtom a := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · exact hp
      · exact hta a ha'
    have hread : ∀ a : L, IsAtom a →
        a ≤ climbFlat x (windowPairs cal x t₀ (t₀ ∪ (insert p t).biUnion supp)) →
        Submodule.span K {hv a}
          = Submodule.span K
              {climbRead (windowPairs cal x t₀ (t₀ ∪ (insert p t).biUnion supp))
                ((QF (insert p t) hFa).hv a)} :=
      hstab _ Finset.subset_union_left (hwinB _ hFa) _ (hQF _ hFa)
    have hple := hwin_le (insert p t) hFa p (Finset.mem_insert_self p t)
    have htle : ∀ a ∈ t,
        a ≤ climbFlat x (windowPairs cal x t₀ (t₀ ∪ (insert p t).biUnion supp)) :=
      fun a ha => hwin_le (insert p t) hFa a (Finset.mem_insert_of_mem ha)
    refine ((QF (insert p t) hFa).flat_le_iff hta htle hp hple).trans ?_
    refine ((map_mem_span_image_iff (hinj _)).symm).trans ?_
    rw [Set.image_image]
    exact mem_span_congr (hread p hp hple).symm
      (span_image_congr fun a ha =>
        (hread a (hta a (Finset.mem_coe.mp ha)) (htle a (Finset.mem_coe.mp ha))).symm)
  have hline : ∀ v : (Fin n → K) × (L → K),
      v ∈ Submodule.span K {w | ∃ p : L, IsAtom p ∧ hv p = w} → v ≠ 0 →
      ∃ p : L, IsAtom p ∧ Submodule.span K {hv p} = Submodule.span K {v} := by
    intro v hvmem hv0
    obtain ⟨T, hTS, hvT⟩ := Submodule.mem_span_finite_of_mem_span hvmem
    have hTex : ∀ u : {u // u ∈ T}, ∃ p : L, IsAtom p ∧ hv p = ↑u :=
      fun u => hTS u.2
    choose g hg1 hg2 using hTex
    have hta : ∀ a ∈ T.attach.image g, IsAtom a := by
      intro a ha
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ha
      exact hg1 u
    have hvmem' : v ∈ Submodule.span K (hv '' ↑(T.attach.image g)) := by
      refine Submodule.span_mono ?_ hvT
      rintro u hu
      exact ⟨g ⟨u, hu⟩,
        Finset.mem_coe.mpr (Finset.mem_image_of_mem g (Finset.mem_attach T ⟨u, hu⟩)),
        hg2 ⟨u, hu⟩⟩
    have hread := hstab _ Finset.subset_union_left
      (hwinB (T.attach.image g) hta) _ (hQF (T.attach.image g) hta)
    have htle : ∀ a ∈ T.attach.image g, a ≤ climbFlat x
        (windowPairs cal x t₀ (t₀ ∪ (T.attach.image g).biUnion supp)) :=
      fun a ha => hwin_le (T.attach.image g) hta a ha
    have hspan_eq : Submodule.span K (hv '' ↑(T.attach.image g))
        = Submodule.span K
            ((fun a => climbRead
                (windowPairs cal x t₀ (t₀ ∪ (T.attach.image g).biUnion supp))
                ((QF (T.attach.image g) hta).hv a)) '' ↑(T.attach.image g)) :=
      span_image_congr fun a ha =>
        hread a (hta a (Finset.mem_coe.mp ha)) (htle a (Finset.mem_coe.mp ha))
    rw [hspan_eq, ← Set.image_image, Submodule.span_image] at hvmem'
    obtain ⟨u, hu, huv⟩ := Submodule.mem_map.mp hvmem'
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, map_zero] at huv
      exact hv0 huv.symm
    obtain ⟨p, hpa, hple, hpspan⟩ := (QF (T.attach.image g) hta).span_surj u hu0
    refine ⟨p, hpa, ?_⟩
    calc Submodule.span K {hv p}
        = Submodule.span K
            {climbRead (windowPairs cal x t₀ (t₀ ∪ (T.attach.image g).biUnion supp))
              ((QF (T.attach.image g) hta).hv p)} := hread p hpa hple
      _ = Submodule.span K
            {climbRead (windowPairs cal x t₀ (t₀ ∪ (T.attach.image g).biUnion supp))
              u} := span_map_of_span_eq _ hpspan
      _ = Submodule.span K {v} := by rw [huv]
  set VS : Submodule K ((Fin n → K) × (L → K)) :=
    Submodule.span K {w | ∃ p : L, IsAtom p ∧ hv p = w} with hVSdef
  set hv' : {p : L // IsAtom p} → VS :=
    fun p => ⟨hv ↑p, Submodule.subset_span ⟨↑p, p.2, rfl⟩⟩ with hhv'
  have hι : Function.Injective VS.subtype := Submodule.injective_subtype VS
  have hfwd : ∀ y : L,
      coordSpanFwd (fun p : {p : L // IsAtom p} => Submodule.span K {hv' p}) y
        = Submodule.span K (hv' '' {p : {p : L // IsAtom p} | (p : L) ≤ y}) := by
    intro y
    apply le_antisymm
    · refine sSup_le ?_
      rintro m ⟨p, hp, rfl⟩
      exact Submodule.span_mono
        (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem hv' hp))
    · rw [Submodule.span_le]
      rintro w ⟨p, hp, rfl⟩
      have h1 : Submodule.span K {hv' p}
          ≤ coordSpanFwd
            (fun p : {p : L // IsAtom p} => Submodule.span K {hv' p}) y :=
        le_sSup ⟨p, hp, rfl⟩
      exact h1 (Submodule.mem_span_singleton_self _)
  refine ⟨VS, inferInstance, inferInstance,
    fun p => Submodule.span K {hv' p}, ?_, ?_⟩
  · rintro ⟨p, hp⟩ y hle
    have hmem : hv' ⟨p, hp⟩ ∈ Submodule.span K
        (hv' '' {q : {q : L // IsAtom q} | (q : L) ≤ y}) := by
      rw [← hfwd y]
      exact hle (Submodule.mem_span_singleton_self _)
    obtain ⟨T, hTsub, hmemT⟩ := Submodule.mem_span_finite_of_mem_span hmem
    have hTex : ∀ u : {u // u ∈ T}, ∃ q : {q : L // IsAtom q},
        (q : L) ≤ y ∧ hv' q = ↑u := fun u => hTsub u.2
    choose g hg1 hg2 using hTex
    have hta : ∀ a ∈ T.attach.image (fun u => ↑(g u) : {u // u ∈ T} → L),
        IsAtom a := by
      intro a ha
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ha
      exact (g u).2
    have hamb : hv p ∈ Submodule.span K
        (hv '' ↑(T.attach.image (fun u => ↑(g u) : {u // u ∈ T} → L))) := by
      have h1 : VS.subtype (hv' ⟨p, hp⟩) ∈
          Submodule.map VS.subtype (Submodule.span K (↑T : Set VS)) :=
        Submodule.mem_map_of_mem hmemT
      rw [← Submodule.span_image] at h1
      refine Submodule.span_mono ?_ h1
      rintro w ⟨u, hu, rfl⟩
      exact ⟨↑(g ⟨u, hu⟩),
        Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_attach T ⟨u, hu⟩)),
        congrArg Subtype.val (hg2 ⟨u, hu⟩)⟩
    have hple := (hflat _ hta p hp).mpr hamb
    refine hple.trans (Finset.sup_le ?_)
    intro a ha
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ha
    exact hg1 u
  · intro W
    refine ⟨sSup {a : L | ∃ ha : IsAtom a, hv' ⟨a, ha⟩ ∈ W}, ?_⟩
    rw [hfwd]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro w ⟨q, hqle, rfl⟩
      have hc := isCompactElement_of_isAtom q.2
      rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup] at hc
      obtain ⟨F, hFS, hqF⟩ := hc _ hqle
      have hFa : ∀ a ∈ F, IsAtom a := by
        intro a ha
        obtain ⟨h, -⟩ := hFS (Finset.mem_coe.mpr ha)
        exact h
      have hamb : hv ↑q ∈ Submodule.span K (hv '' ↑F) :=
        (hflat F hFa ↑q q.2).mp hqF
      have himg : hv '' ↑F
          = VS.subtype '' (hv' '' {a : {a : L // IsAtom a} | (a : L) ∈ F}) := by
        ext w'
        constructor
        · rintro ⟨a, haF, rfl⟩
          exact ⟨hv' ⟨a, hFa a (Finset.mem_coe.mp haF)⟩,
            ⟨⟨a, hFa a (Finset.mem_coe.mp haF)⟩, Finset.mem_coe.mp haF, rfl⟩, rfl⟩
        · rintro ⟨w'', ⟨a, haF, rfl⟩, rfl⟩
          exact ⟨↑a, Finset.mem_coe.mpr haF, rfl⟩
      rw [himg, Submodule.span_image] at hamb
      obtain ⟨w', hw', hww⟩ := Submodule.mem_map.mp hamb
      have hww' : VS.subtype w' = VS.subtype (hv' q) := hww
      have hqw : hv' q ∈ Submodule.span K
          (hv' '' {a : {a : L // IsAtom a} | (a : L) ∈ F}) := hι hww' ▸ hw'
      refine Submodule.span_le.mpr ?_ hqw
      rintro w'' ⟨a, haF, rfl⟩
      obtain ⟨ha', hWa⟩ := hFS (Finset.mem_coe.mpr haF)
      exact hWa
    · intro w hw
      by_cases hw0 : w = 0
      · rw [hw0]
        exact Submodule.zero_mem _
      have hwm : (w : (Fin n → K) × (L → K)) ∈ VS := w.2
      have hw0' : (w : (Fin n → K) × (L → K)) ≠ 0 :=
        fun h => hw0 (Subtype.ext h)
      obtain ⟨p, hpa, hpspan⟩ := hline ↑w hwm hw0'
      have hVSeq : Submodule.span K {hv' ⟨p, hpa⟩} = Submodule.span K {w} :=
        (map_span_singleton_eq_iff hι).mp hpspan
      have hWmem : hv' ⟨p, hpa⟩ ∈ W :=
        (Submodule.span_singleton_le_iff_mem w W).mpr hw
          (by rw [← hVSeq]; exact Submodule.mem_span_singleton_self _)
      have hwsp : w ∈ Submodule.span K {hv' ⟨p, hpa⟩} := by
        rw [hVSeq]
        exact Submodule.mem_span_singleton_self _
      refine Submodule.span_mono ?_ hwsp
      exact Set.singleton_subset_iff.mpr
        ⟨⟨p, hpa⟩, le_sSup ⟨hpa, hWmem⟩, rfl⟩

end Summit

end Foam.Bridges

/-! ## Axiom audit -/

/-- info: 'Foam.Bridges.line_meets_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.line_meets_flat

/-- info: 'Foam.Bridges.mem_span_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.mem_span_congr

/-- info: 'Foam.Bridges.span_image_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.span_image_congr

/-- info: 'Foam.Bridges.map_mem_span_image_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.map_mem_span_image_iff

/-- info: 'Foam.Bridges.PointSys.mem_span_of_le_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.PointSys.mem_span_of_le_sup

/-- info: 'Foam.Bridges.PointSys.le_sup_of_mem_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.PointSys.le_sup_of_mem_span

/-- info: 'Foam.Bridges.PointSys.flat_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.PointSys.flat_le_iff

/-- info: 'Foam.Bridges.limit_system_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.limit_system_exists
