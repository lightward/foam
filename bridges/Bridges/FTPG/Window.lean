import Bridges.FTPG.Perm

/-!
# Camp four: the windows along the atom basis

The direct limit climbs a directed family of finite windows: finite sets `s`
of basis atoms containing a base support `t₀`, with flats `x ⊔ s.sup id`.
This file carves the family's coherence — the reads of any two window climbs
agree span-level wherever both windows see — from three strata:

* **the append face** (`isClimb_append_exists`, `isClimb_append_read_agree`):
  a climb continued along `ws₂` reads on the old flat exactly as the old
  climb did — the continuation pads the old coordinates by zeros
  (`IsClimb.hv_of_le`) and the read strips the pads (`climbRead_pad`), so
  growing the window never rewrites the read.  The statement is arranged so
  the induction is definitional: no dimension casts, no flat transport.
* **read injectivity** (`climbRead_eq_zero`, `climbRead_injective`): when the
  stepped atoms are distinct, the atom-named reading is injective — each
  step's slot is deposited at its own name (`climbRead_snd_eq_zero`), so the
  peeling loses nothing.  Seated here ahead of its consumer: the limit map's
  laws reflect through it (`map_span_singleton_eq_iff`,
  `map_mem_span_pair_iff`).
* **the windows** (`basis_no_capture`, `actives`, `window_legal`): an atom of
  the basis outside a window is never below its flat — `sSupIndep` refuses
  the capture directly.  The base support `t₀` is climbed greedily along its
  canonical enumeration (`actives`: keep an atom iff it is not yet below the
  flat), the extras follow in any enumeration, and the whole canonical list
  is legal (`ClimbLegal`) with flat `x ⊔ s.sup id` (`windowFlat_eq`).
* **the summit** (`window_read_mono`, `window_read_directed`): for windows
  `s ⊆ s'`, the canonical list of `s'` is a permutation of the canonical
  list of `s` followed by the new extras (`windowPairs_perm`), so the perm
  face (`isClimb_perm_agree`) and the append face chain; two arbitrary
  windows agree through their union.  Every calibration atom is chosen once
  per stepped atom (`CalSpec`, `calSpec_exists`), so permuted windows carry
  literally equal pair data.

Model-verified before carving (`probe_limit.py`, the previous sitting):
Steinitz no-capture and active-set order-stability over aligned and tilted
base flats (check C), and every pooled window climb — all windows, all
sampled orders and interleavings — span-agreeing with the limit assignment
under the atom-named embedding (checks D/E), over five window configurations
at `q ∈ {2,3}`, twisted base systems throughout.
-/

namespace Foam.Bridges

universe u

/-! ## The append face: a climb continued reads as padding -/

section AppendShape

variable {L : Type u} [Lattice L]

theorem climbFlat_append : ∀ (ws₁ ws₂ : List (L × L)) (x : L),
    climbFlat x (ws₁ ++ ws₂) = climbFlat (climbFlat x ws₁) ws₂
  | [], _, _ => rfl
  | ww :: ws₁, ws₂, x => climbFlat_append ws₁ ws₂ (x ⊔ ww.1)

variable [BoundedOrder L]

theorem ClimbLegal.append {b₀ : L} : ∀ {ws₁ ws₂ : List (L × L)} {x : L},
    ClimbLegal b₀ ws₁ x → ClimbLegal b₀ ws₂ (climbFlat x ws₁) →
    ClimbLegal b₀ (ws₁ ++ ws₂) x
  | [], _, _, _, h₂ => h₂
  | (_, _) :: _, _, _, ⟨hw, hwx, hw', hw'le, hw'b, hw'w, htail⟩, h₂ =>
    ⟨hw, hwx, hw', hw'le, hw'b, hw'w, ClimbLegal.append htail h₂⟩

theorem ClimbLegal.append_right {b₀ : L} : ∀ {ws₁ ws₂ : List (L × L)} {x : L},
    ClimbLegal b₀ (ws₁ ++ ws₂) x → ClimbLegal b₀ ws₂ (climbFlat x ws₁)
  | [], _, _, h => h
  | (_, _) :: ws₁, _, _, ⟨_, _, _, _, _, _, htail⟩ =>
    ClimbLegal.append_right (ws₁ := ws₁) htail

end AppendShape

section AppendSystems

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L]
  [IsAtomistic L]
variable {K : Type*} [DivisionRing K] [DecidableEq L]

theorem isClimb_append_exists {b₀ : L}
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b) :
    ∀ (ws₁ ws₂ : List (L × L)) (x : L) (n : ℕ) (P : PointSys x n K)
      (Q₁ : PointSys (climbFlat x ws₁) (climbDim n ws₁) K),
      3 ≤ n → IsAtom b₀ → b₀ ≤ x →
      IsClimb b₀ ws₁ x n P Q₁ → ClimbLegal b₀ ws₂ (climbFlat x ws₁) →
      ∃ Q : PointSys (climbFlat x (ws₁ ++ ws₂)) (climbDim n (ws₁ ++ ws₂)) K,
        IsClimb b₀ (ws₁ ++ ws₂) x n P Q ∧
        ∀ t : L, t ≤ climbFlat x ws₁ →
          climbRead (ws₁ ++ ws₂) (Q.hv t) = climbRead ws₁ (Q₁.hv t)
  | [], ws₂, x, n, P, Q₁, hn, hb₀, hb₀x, hQ₁, hleg₂ => by
    have hQP : Q₁ = P := hQ₁
    subst hQP
    obtain ⟨Q, hQ⟩ := isClimb_exists h_irred ws₂ x n Q₁ hn hb₀ hb₀x hleg₂
    refine ⟨Q, hQ, fun t ht => ?_⟩
    show climbRead ws₂ (Q.hv t) = (Q₁.hv t, 0)
    rw [IsClimb.hv_of_le ws₂ x n Q₁ Q hQ t ht, climbRead_pad]
    rfl
  | (w, w') :: ws₁, ws₂, x, n, P, Q₁, hn, hb₀, hb₀x, hQ₁, hleg₂ => by
    obtain ⟨R, hcal, hpad, hclimb⟩ := hQ₁
    obtain ⟨Q, hQ, hread⟩ := isClimb_append_exists h_irred ws₁ ws₂ (x ⊔ w)
      (n + 1) R Q₁ (hn.trans (Nat.le_succ n)) hb₀ (hb₀x.trans le_sup_left)
      hclimb hleg₂
    refine ⟨Q, ⟨R, hcal, hpad, hQ⟩, fun t ht => ?_⟩
    show readStep w (climbRead (ws₁ ++ ws₂) (Q.hv t))
      = readStep w (climbRead ws₁ (Q₁.hv t))
    rw [hread t ht]

theorem isClimb_append_read_agree {b₀ : L}
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    {ws₁ ws₂ : List (L × L)} {x : L} {n : ℕ} {P : PointSys x n K}
    {Q₁ : PointSys (climbFlat x ws₁) (climbDim n ws₁) K}
    {Q : PointSys (climbFlat x (ws₁ ++ ws₂)) (climbDim n (ws₁ ++ ws₂)) K}
    (hn : 3 ≤ n) (hb₀ : IsAtom b₀) (hb₀x : b₀ ≤ x)
    (hleg : ClimbLegal b₀ (ws₁ ++ ws₂) x)
    (hQ₁ : IsClimb b₀ ws₁ x n P Q₁) (hQ : IsClimb b₀ (ws₁ ++ ws₂) x n P Q)
    {t : L} (ht : IsAtom t) (ht_le : t ≤ climbFlat x ws₁) :
    Submodule.span K {climbRead (ws₁ ++ ws₂) (Q.hv t)}
      = Submodule.span K {climbRead ws₁ (Q₁.hv t)} := by
  obtain ⟨Qe, hQe, hread⟩ := isClimb_append_exists h_irred ws₁ ws₂ x n P Q₁
    hn hb₀ hb₀x hQ₁ hleg.append_right
  have ht_le' : t ≤ climbFlat x (ws₁ ++ ws₂) := by
    rw [climbFlat_append]
    exact ht_le.trans (le_climbFlat ws₂ (climbFlat x ws₁))
  have hagree := isClimb_agree h_irred hn hb₀ hb₀x hleg hQ hQe ht ht_le'
  calc Submodule.span K {climbRead (ws₁ ++ ws₂) (Q.hv t)}
      = Submodule.span K {climbRead (ws₁ ++ ws₂) (Qe.hv t)} :=
        span_map_of_span_eq (climbRead (ws₁ ++ ws₂)) hagree
    _ = Submodule.span K {climbRead ws₁ (Q₁.hv t)} := by rw [hread t ht_le]

end AppendSystems

/-! ## Read injectivity: distinct names lose nothing -/

section ReadInjective

variable {L : Type u} {K : Type*} [DivisionRing K] [DecidableEq L]

theorem climbRead_snd_eq_zero :
    ∀ (ws : List (L × L)) {n : ℕ} (v : Fin (climbDim n ws) → K) {a : L},
      a ∉ ws.map Prod.fst → (climbRead ws v).2 a = 0
  | [], _, _, _, _ => rfl
  | (w, w') :: ws, n, v, a, ha => by
    have ha' : a ∉ ws.map Prod.fst := fun h => ha (List.mem_cons_of_mem _ h)
    have haw : a ≠ w := fun h =>
      ha (h ▸ List.mem_cons_self (a := w) (l := ws.map Prod.fst))
    show ((climbRead ws v).2
      + Pi.single w ((climbRead ws v).1 (Fin.last n)) : L → K) a = 0
    rw [Pi.add_apply, climbRead_snd_eq_zero ws v ha',
      Pi.single_eq_of_ne haw, add_zero]

theorem climbRead_eq_zero :
    ∀ (ws : List (L × L)), (ws.map Prod.fst).Nodup →
      ∀ {n : ℕ} {v : Fin (climbDim n ws) → K}, climbRead ws v = 0 → v = 0
  | [], _, _, v, h => congrArg Prod.fst h
  | (w, w') :: ws, hnd, n, v, h => by
    obtain ⟨hw, hnd'⟩ := List.nodup_cons.mp hnd
    have h' : ((climbRead ws v).1 ∘ Fin.castSucc,
        (climbRead ws v).2
          + Pi.single w ((climbRead ws v).1 (Fin.last _))) = 0 := by
      rw [← readStep_apply]
      exact h
    have h1 : (climbRead ws v).1 ∘ Fin.castSucc = 0 := congrArg Prod.fst h'
    have h2 : (climbRead ws v).2
        + Pi.single w ((climbRead ws v).1 (Fin.last _)) = 0 :=
      congrArg Prod.snd h'
    have hsw : (climbRead ws v).2 w = 0 := climbRead_snd_eq_zero ws v hw
    have hlast : (climbRead ws v).1 (Fin.last _) = 0 := by
      have h3 := congrFun h2 w
      rwa [Pi.add_apply, hsw, zero_add, Pi.single_eq_same, Pi.zero_apply]
        at h3
    have hfst : (climbRead ws v).1 = 0 := by
      funext i
      refine Fin.lastCases hlast (fun j => ?_) i
      exact congrFun h1 j
    have hsnd : (climbRead ws v).2 = 0 := by
      rw [hlast, Pi.single_zero, add_zero] at h2
      exact h2
    exact climbRead_eq_zero ws hnd' (Prod.ext hfst hsnd)

theorem climbRead_injective (ws : List (L × L))
    (hnd : (ws.map Prod.fst).Nodup) {n : ℕ} :
    Function.Injective (climbRead ws (K := K) (n := n)) := by
  intro u v huv
  rw [← sub_eq_zero]
  exact climbRead_eq_zero ws hnd (by rw [map_sub, huv, sub_self])

end ReadInjective

/-! ## Span reflection through an injective linear map -/

section SpanReflect

variable {K : Type*} [DivisionRing K] {M N : Type*}
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem map_span_singleton_eq_iff {f : M →ₗ[K] N}
    (hf : Function.Injective f) {u v : M} :
    Submodule.span K {f u} = Submodule.span K {f v}
      ↔ Submodule.span K {u} = Submodule.span K {v} := by
  constructor
  · intro h
    have key : ∀ {a b : M},
        Submodule.span K {f a} ≤ Submodule.span K {f b} →
        Submodule.span K {a} ≤ Submodule.span K {b} := by
      intro a b hab
      rw [Submodule.span_singleton_le_iff_mem] at hab ⊢
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hab
      rw [← map_smul] at hc
      exact hf hc ▸ Submodule.smul_mem _ c (Submodule.mem_span_singleton_self b)
    exact le_antisymm (key h.le) (key h.ge)
  · exact fun h => span_map_of_span_eq f h

theorem map_mem_span_singleton_iff {f : M →ₗ[K] N}
    (hf : Function.Injective f) {u v : M} :
    f u ∈ Submodule.span K {f v} ↔ u ∈ Submodule.span K {v} := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    rw [← map_smul] at hc
    exact Submodule.mem_span_singleton.mpr ⟨c, hf hc⟩
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    exact Submodule.mem_span_singleton.mpr ⟨c, by rw [← map_smul, hc]⟩

theorem mem_span_pair_congr {a a' b b' c c' : M}
    (ha : Submodule.span K {a} = Submodule.span K {a'})
    (hb : Submodule.span K {b} = Submodule.span K {b'})
    (hc : Submodule.span K {c} = Submodule.span K {c'}) :
    c ∈ Submodule.span K {a, b} ↔ c' ∈ Submodule.span K {a', b'} := by
  have hpair : Submodule.span K {a, b} = Submodule.span K ({a', b'} : Set M) := by
    rw [show ({a, b} : Set M) = insert a {b} from rfl,
      show ({a', b'} : Set M) = insert a' {b'} from rfl,
      Submodule.span_insert, Submodule.span_insert, ha, hb]
  rw [hpair, ← Submodule.span_singleton_le_iff_mem,
    ← Submodule.span_singleton_le_iff_mem, hc]

theorem map_mem_span_pair_iff {f : M →ₗ[K] N}
    (hf : Function.Injective f) {p q r : M} :
    f r ∈ Submodule.span K {f p, f q} ↔ r ∈ Submodule.span K {p, q} := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h
    rw [← map_smul, ← map_smul, ← map_add] at hab
    exact Submodule.mem_span_pair.mpr ⟨a, b, hf hab⟩
  · intro h
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h
    exact Submodule.mem_span_pair.mpr
      ⟨a, b, by rw [← map_smul, ← map_smul, ← map_add, hab]⟩

end SpanReflect

/-! ## The windows: calibration data, the greedy actives, no capture -/

section WindowShape

variable {L : Type u}

def CalSpec [Lattice L] [OrderBot L] (b₀ : L) (cal : L → L) : Prop :=
  ∀ w : L, IsAtom w → w ≠ b₀ →
    IsAtom (cal w) ∧ cal w ≤ b₀ ⊔ w ∧ cal w ≠ b₀ ∧ cal w ≠ w

open Classical in
theorem calSpec_exists [Lattice L] [OrderBot L] {b₀ : L} (hb₀ : IsAtom b₀)
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b) :
    ∃ cal : L → L, CalSpec b₀ cal := by
  refine ⟨fun w => if h : IsAtom w ∧ w ≠ b₀
    then (h_irred b₀ w hb₀ h.1 (Ne.symm h.2)).choose else b₀,
    fun w hw hwb => ?_⟩
  have hh : IsAtom w ∧ w ≠ b₀ := ⟨hw, hwb⟩
  simp only [dif_pos hh]
  obtain ⟨h1, h2, h3, h4⟩ := (h_irred b₀ w hb₀ hw (Ne.symm hwb)).choose_spec
  exact ⟨h1, h2, h3, h4⟩

def calPairs (cal : L → L) (l : List L) : List (L × L) :=
  l.map fun w => (w, cal w)

theorem calPairs_map_fst (cal : L → L) :
    ∀ l : List L, (calPairs cal l).map Prod.fst = l
  | [] => rfl
  | b :: bs => congrArg (List.cons b) (calPairs_map_fst cal bs)

def listSup [SemilatticeSup L] [OrderBot L] (l : List L) : L :=
  l.foldr (· ⊔ ·) ⊥

theorem listSup_toList [SemilatticeSup L] [OrderBot L] (t : Finset L) :
    listSup t.toList = t.sup id := by
  rw [Finset.sup_def, Multiset.map_id, ← Finset.coe_toList t]
  exact (Multiset.coe_fold_r _ _ _).symm

open Classical in
noncomputable def actives [SemilatticeSup L] : L → List L → List L
  | _, [] => []
  | y, b :: bs => if b ≤ y then actives y bs else b :: actives (y ⊔ b) bs

theorem actives_sublist [SemilatticeSup L] :
    ∀ (l : List L) (y : L), (actives y l).Sublist l
  | [], _ => List.nil_sublist []
  | b :: bs, y => by
    by_cases hb : b ≤ y
    · simp only [actives, if_pos hb]
      exact (actives_sublist bs y).cons b
    · simp only [actives, if_neg hb]
      exact (actives_sublist bs (y ⊔ b)).cons_cons b

theorem sup_listSup_actives [SemilatticeSup L] [OrderBot L] :
    ∀ (l : List L) (y : L), y ⊔ listSup (actives y l) = y ⊔ listSup l
  | [], _ => rfl
  | b :: bs, y => by
    by_cases hb : b ≤ y
    · simp only [actives, if_pos hb]
      rw [sup_listSup_actives bs y]
      show y ⊔ listSup bs = y ⊔ (b ⊔ listSup bs)
      rw [← sup_assoc, sup_eq_left.mpr hb]
    · simp only [actives, if_neg hb]
      show y ⊔ (b ⊔ listSup (actives (y ⊔ b) bs)) = y ⊔ (b ⊔ listSup bs)
      rw [← sup_assoc, ← sup_assoc, sup_listSup_actives bs (y ⊔ b)]

theorem climbFlat_calPairs [Lattice L] [OrderBot L] {cal : L → L} :
    ∀ (l : List L) (y : L),
      climbFlat (L := L) y (calPairs cal l) = y ⊔ listSup l
  | [], y => (sup_bot_eq y).symm
  | b :: bs, y => by
    show climbFlat (y ⊔ b) (calPairs cal bs) = y ⊔ (b ⊔ listSup bs)
    rw [climbFlat_calPairs bs (y ⊔ b), sup_assoc]

theorem actives_legal [Lattice L] [BoundedOrder L] {b₀ : L} {cal : L → L}
    (hcal : CalSpec b₀ cal) :
    ∀ (l : List L) (y : L), b₀ ≤ y → (∀ b ∈ l, IsAtom b) →
      ClimbLegal b₀ (calPairs cal (actives y l)) y
  | [], _, _, _ => trivial
  | b :: bs, y, hb₀y, hatoms => by
    by_cases hb : b ≤ y
    · simp only [actives, if_pos hb]
      exact actives_legal hcal bs y hb₀y
        fun c hc => hatoms c (List.mem_cons_of_mem b hc)
    · simp only [actives, if_neg hb]
      have hbatom : IsAtom b := hatoms b List.mem_cons_self
      have hbne : b ≠ b₀ := fun h => hb (h ▸ hb₀y)
      obtain ⟨h1, h2, h3, h4⟩ := hcal b hbatom hbne
      exact ⟨hbatom, hb, h1, h2, h3, h4,
        actives_legal hcal bs (y ⊔ b) (hb₀y.trans le_sup_left)
          fun c hc => hatoms c (List.mem_cons_of_mem b hc)⟩

end WindowShape

section WindowBasis

variable {L : Type u} [CompleteLattice L]

theorem basis_no_capture (B : AtomBasis L) {b : L} (hbB : b ∈ B.carrier)
    {u : Finset L} (huB : ↑u ⊆ B.carrier) (hbu : b ∉ u)
    {y : L} (hyu : y ≤ u.sup id) : ¬ b ≤ y ⊔ u.sup id := by
  intro hle
  rw [sup_eq_right.mpr hyu] at hle
  have h2 : u.sup id ≤ sSup (B.carrier \ {b}) :=
    Finset.sup_le fun c hc =>
      le_sSup ⟨huB hc, fun hcb => hbu (Set.mem_singleton_iff.mp hcb ▸ hc)⟩
  exact (B.atom hbB).1 (le_bot_iff.mp (B.indep hbB le_rfl (hle.trans h2)))

variable [DecidableEq L]

theorem extras_legal (B : AtomBasis L) {b₀ : L} {cal : L → L}
    (hcal : CalSpec b₀ cal) :
    ∀ (l : List L) (u : Finset L) (y : L), l.Nodup → ↑u ⊆ B.carrier →
      (∀ e ∈ l, e ∈ B.carrier ∧ e ∉ u) → b₀ ≤ y → y ≤ u.sup id →
      ClimbLegal b₀ (calPairs cal l) (y ⊔ u.sup id)
  | [], _, _, _, _, _, _, _ => trivial
  | e :: l, u, y, hnd, huB, hmem, hb₀y, hyu => by
    obtain ⟨heB, heu⟩ := hmem e List.mem_cons_self
    obtain ⟨he_nl, hnd'⟩ := List.nodup_cons.mp hnd
    have hatom : IsAtom e := B.atom heB
    have hcap : ¬ e ≤ y ⊔ u.sup id := basis_no_capture B heB huB heu hyu
    have hne : e ≠ b₀ := fun h => hcap (h ▸ hb₀y.trans le_sup_left)
    obtain ⟨h1, h2, h3, h4⟩ := hcal e hatom hne
    refine ⟨hatom, hcap, h1, h2, h3, h4, ?_⟩
    have hflat : (y ⊔ u.sup id) ⊔ e = y ⊔ (insert e u).sup id := by
      rw [Finset.sup_insert, id_eq, sup_assoc, sup_comm (u.sup id) e]
    rw [hflat]
    refine extras_legal B hcal l (insert e u) y hnd'
      (by rw [Finset.coe_insert]; exact Set.insert_subset heB huB)
      (fun e' he' => ⟨(hmem e' (List.mem_cons_of_mem e he')).1,
        fun hins => (Finset.mem_insert.mp hins).elim
          (fun h => he_nl (h ▸ he'))
          (hmem e' (List.mem_cons_of_mem e he')).2⟩)
      hb₀y (hyu.trans (Finset.sup_mono (Finset.subset_insert e u)))

noncomputable def windowList (x : L) (t₀ s : Finset L) : List L :=
  actives x t₀.toList ++ (s \ t₀).toList

noncomputable def windowPairs (cal : L → L) (x : L) (t₀ s : Finset L) :
    List (L × L) :=
  calPairs cal (windowList x t₀ s)

theorem windowList_nodup (x : L) (t₀ s : Finset L) :
    (windowList x t₀ s).Nodup := by
  refine List.Nodup.append
    ((Finset.nodup_toList t₀).sublist (actives_sublist t₀.toList x))
    (Finset.nodup_toList (s \ t₀)) fun a ha ha' => ?_
  have h1 : a ∈ t₀ :=
    Finset.mem_toList.mp ((actives_sublist t₀.toList x).subset ha)
  exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp ha')).2 h1

theorem windowFlat_eq {cal : L → L} {x : L} {t₀ s : Finset L}
    (hts : t₀ ⊆ s) :
    climbFlat x (windowPairs cal x t₀ s) = x ⊔ s.sup id := by
  rw [windowPairs, windowList, calPairs, List.map_append, climbFlat_append]
  show climbFlat (climbFlat x (calPairs cal (actives x t₀.toList)))
    (calPairs cal (s \ t₀).toList) = x ⊔ s.sup id
  rw [climbFlat_calPairs, climbFlat_calPairs, sup_listSup_actives,
    listSup_toList, listSup_toList, sup_assoc, ← Finset.sup_union,
    Finset.union_sdiff_of_subset hts]

theorem window_legal (B : AtomBasis L) {b₀ : L} {cal : L → L} {x : L}
    {t₀ s : Finset L} (hcal : CalSpec b₀ cal) (hb₀x : b₀ ≤ x)
    (ht₀B : ↑t₀ ⊆ B.carrier) (hxt₀ : x ≤ t₀.sup id)
    (hsB : ↑s ⊆ B.carrier) :
    ClimbLegal b₀ (windowPairs cal x t₀ s) x := by
  rw [windowPairs, windowList, calPairs, List.map_append]
  refine ClimbLegal.append
    (actives_legal hcal t₀.toList x hb₀x
      fun b hb => B.atom (ht₀B (Finset.mem_toList.mp hb))) ?_
  show ClimbLegal b₀ (calPairs cal (s \ t₀).toList)
    (climbFlat x (calPairs cal (actives x t₀.toList)))
  rw [climbFlat_calPairs, sup_listSup_actives, listSup_toList]
  have hflat : x ⊔ t₀.sup id = x ⊔ t₀.sup id ⊔ t₀.sup id := by
    rw [sup_assoc, sup_idem]
  rw [hflat]
  exact extras_legal B hcal (s \ t₀).toList t₀ (x ⊔ t₀.sup id)
    (s \ t₀).nodup_toList ht₀B
    (fun e he => by
      have h := Finset.mem_sdiff.mp (Finset.mem_toList.mp he)
      exact ⟨hsB h.1, h.2⟩)
    (hb₀x.trans le_sup_left) (sup_le hxt₀ le_rfl)

theorem windowPairs_perm {cal : L → L} {x : L} {t₀ s s' : Finset L}
    (hts : t₀ ⊆ s) (hss' : s ⊆ s') :
    (windowPairs cal x t₀ s ++ calPairs cal (s' \ s).toList).Perm
      (windowPairs cal x t₀ s') := by
  rw [windowPairs, windowPairs, windowList, windowList, calPairs, calPairs,
    calPairs, ← List.map_append, List.append_assoc]
  refine List.Perm.map _ (List.Perm.append_left _ ?_)
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add,
    Finset.coe_toList, Finset.coe_toList, Finset.coe_toList]
  have hdisj : Disjoint (s \ t₀) (s' \ s) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    exact (Finset.mem_sdiff.mp ha').2 (Finset.mem_sdiff.mp ha).1
  have hun : (s \ t₀) ∪ (s' \ s) = s' \ t₀ := by
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨hss' h1, h2⟩
      · exact ⟨h1, fun h => h2 (hts h)⟩
    · rintro ⟨h1, h2⟩
      by_cases hs : a ∈ s
      · exact Or.inl ⟨hs, h2⟩
      · exact Or.inr ⟨h1, hs⟩
  rw [← hun, ← Finset.disjUnion_eq_union _ _ hdisj]
  rfl

end WindowBasis

/-! ## The summit: the window family is coherent -/

section WindowSystems

variable {L : Type u} [CompleteLattice L] [IsModularLattice L] [IsAtomistic L]
variable {K : Type*} [DivisionRing K] [DecidableEq L]

theorem window_read_mono
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (B : AtomBasis L) {b₀ : L} {cal : L → L} {x : L} {t₀ s s' : Finset L}
    {n : ℕ} {P : PointSys x n K}
    {Q : PointSys (climbFlat x (windowPairs cal x t₀ s))
      (climbDim n (windowPairs cal x t₀ s)) K}
    {Q' : PointSys (climbFlat x (windowPairs cal x t₀ s'))
      (climbDim n (windowPairs cal x t₀ s')) K}
    (hn : 3 ≤ n) (hb₀ : IsAtom b₀) (hb₀x : b₀ ≤ x) (hcal : CalSpec b₀ cal)
    (ht₀B : ↑t₀ ⊆ B.carrier) (hxt₀ : x ≤ t₀.sup id)
    (hts : t₀ ⊆ s) (hss' : s ⊆ s') (hs'B : ↑s' ⊆ B.carrier)
    (hQ : IsClimb b₀ (windowPairs cal x t₀ s) x n P Q)
    (hQ' : IsClimb b₀ (windowPairs cal x t₀ s') x n P Q')
    {t : L} (ht : IsAtom t)
    (ht_le : t ≤ climbFlat x (windowPairs cal x t₀ s)) :
    Submodule.span K {climbRead (windowPairs cal x t₀ s') (Q'.hv t)}
      = Submodule.span K {climbRead (windowPairs cal x t₀ s) (Q.hv t)} := by
  have hperm := windowPairs_perm (cal := cal) (x := x) hts hss'
  have hlegapp : ClimbLegal b₀
      (windowPairs cal x t₀ s ++ calPairs cal (s' \ s).toList) x :=
    ClimbLegal.perm hperm.symm x (window_legal B hcal hb₀x ht₀B hxt₀ hs'B)
  obtain ⟨Qa, hQa⟩ := isClimb_exists h_irred _ x n P hn hb₀ hb₀x hlegapp
  have ht_le' : t ≤ climbFlat x
      (windowPairs cal x t₀ s ++ calPairs cal (s' \ s).toList) := by
    rw [climbFlat_append]
    exact ht_le.trans (le_climbFlat _ _)
  have hface1 := isClimb_perm_agree h_irred hperm x n P Qa Q' hn hb₀ hb₀x
    hlegapp hQa hQ' t ht ht_le'
  have hface2 := isClimb_append_read_agree h_irred hn hb₀ hb₀x hlegapp hQ hQa
    ht ht_le
  exact hface1.symm.trans hface2

theorem window_read_directed
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (B : AtomBasis L) {b₀ : L} {cal : L → L} {x : L} {t₀ s₁ s₂ : Finset L}
    {n : ℕ} {P : PointSys x n K}
    {Q₁ : PointSys (climbFlat x (windowPairs cal x t₀ s₁))
      (climbDim n (windowPairs cal x t₀ s₁)) K}
    {Q₂ : PointSys (climbFlat x (windowPairs cal x t₀ s₂))
      (climbDim n (windowPairs cal x t₀ s₂)) K}
    (hn : 3 ≤ n) (hb₀ : IsAtom b₀) (hb₀x : b₀ ≤ x) (hcal : CalSpec b₀ cal)
    (ht₀B : ↑t₀ ⊆ B.carrier) (hxt₀ : x ≤ t₀.sup id)
    (hts₁ : t₀ ⊆ s₁) (hs₁B : ↑s₁ ⊆ B.carrier)
    (hts₂ : t₀ ⊆ s₂) (hs₂B : ↑s₂ ⊆ B.carrier)
    (hQ₁ : IsClimb b₀ (windowPairs cal x t₀ s₁) x n P Q₁)
    (hQ₂ : IsClimb b₀ (windowPairs cal x t₀ s₂) x n P Q₂)
    {t : L} (ht : IsAtom t)
    (ht₁ : t ≤ climbFlat x (windowPairs cal x t₀ s₁))
    (ht₂ : t ≤ climbFlat x (windowPairs cal x t₀ s₂)) :
    Submodule.span K {climbRead (windowPairs cal x t₀ s₁) (Q₁.hv t)}
      = Submodule.span K {climbRead (windowPairs cal x t₀ s₂) (Q₂.hv t)} := by
  obtain ⟨Qu, hQu⟩ := isClimb_exists h_irred (windowPairs cal x t₀ (s₁ ∪ s₂))
    x n P hn hb₀ hb₀x
    (window_legal B hcal hb₀x ht₀B hxt₀
      (by rw [Finset.coe_union]; exact Set.union_subset hs₁B hs₂B))
  have h1 := window_read_mono h_irred B hn hb₀ hb₀x hcal ht₀B hxt₀ hts₁
    Finset.subset_union_left
    (by rw [Finset.coe_union]; exact Set.union_subset hs₁B hs₂B)
    hQ₁ hQu ht ht₁
  have h2 := window_read_mono h_irred B hn hb₀ hb₀x hcal ht₀B hxt₀ hts₂
    Finset.subset_union_right
    (by rw [Finset.coe_union]; exact Set.union_subset hs₁B hs₂B)
    hQ₂ hQu ht ht₂
  exact h1.symm.trans h2

end WindowSystems

end Foam.Bridges

/-! ## Axiom audit -/

/-- info: 'Foam.Bridges.climbFlat_append' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.climbFlat_append

/-- info: 'Foam.Bridges.ClimbLegal.append' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.ClimbLegal.append

/-- info: 'Foam.Bridges.ClimbLegal.append_right' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.ClimbLegal.append_right

/-- info: 'Foam.Bridges.isClimb_append_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.isClimb_append_exists

/-- info: 'Foam.Bridges.isClimb_append_read_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.isClimb_append_read_agree

/-- info: 'Foam.Bridges.climbRead_snd_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.climbRead_snd_eq_zero

/-- info: 'Foam.Bridges.climbRead_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.climbRead_eq_zero

/-- info: 'Foam.Bridges.climbRead_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.climbRead_injective

/-- info: 'Foam.Bridges.map_span_singleton_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.map_span_singleton_eq_iff

/-- info: 'Foam.Bridges.map_mem_span_singleton_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.map_mem_span_singleton_iff

/-- info: 'Foam.Bridges.mem_span_pair_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.mem_span_pair_congr

/-- info: 'Foam.Bridges.map_mem_span_pair_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.map_mem_span_pair_iff

/-- info: 'Foam.Bridges.CalSpec' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.CalSpec

/-- info: 'Foam.Bridges.calSpec_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.calSpec_exists

/-- info: 'Foam.Bridges.calPairs' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.calPairs

/-- info: 'Foam.Bridges.calPairs_map_fst' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.calPairs_map_fst

/-- info: 'Foam.Bridges.listSup' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.listSup

/-- info: 'Foam.Bridges.listSup_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.listSup_toList

/-- info: 'Foam.Bridges.actives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.actives

/-- info: 'Foam.Bridges.actives_sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.actives_sublist

/-- info: 'Foam.Bridges.sup_listSup_actives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.sup_listSup_actives

/-- info: 'Foam.Bridges.climbFlat_calPairs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.climbFlat_calPairs

/-- info: 'Foam.Bridges.actives_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.actives_legal

/-- info: 'Foam.Bridges.basis_no_capture' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.basis_no_capture

/-- info: 'Foam.Bridges.extras_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.extras_legal

/-- info: 'Foam.Bridges.windowList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.windowList

/-- info: 'Foam.Bridges.windowPairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.windowPairs

/-- info: 'Foam.Bridges.windowList_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.windowList_nodup

/-- info: 'Foam.Bridges.windowFlat_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.windowFlat_eq

/-- info: 'Foam.Bridges.window_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.window_legal

/-- info: 'Foam.Bridges.windowPairs_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.windowPairs_perm

/-- info: 'Foam.Bridges.window_read_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.window_read_mono

/-- info: 'Foam.Bridges.window_read_directed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.window_read_directed
