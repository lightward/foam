import Bridges.FTPG.Diamond
import Bridges.FTPG.Exchange

/-!
# Camp four: permutation coherence — the climb reads the window, not the order

Two climbs along permuted lists agree span-level under the atom-named reading.
`climbRead` peels a climb's slots back onto their atoms' names — a linear map
into `(Fin n → K) × (L → K)`, base slots kept, each step slot deposited at its
atom — and `isClimb_perm_agree` closes coherence over `List.Perm`: the read of
a window's climb does not depend on the order the window was climbed.

The induction is the chart's three faces, one constructor each:
* **cons** — two climbs sharing a head step: the heads agree by
  `calibrated_agree`, an auxiliary climb seats the tail comparison
  (`isClimb_exists`), and `isClimb_agree_congr` carries the identification up;
  the read chains through `span_map_of_span_eq` (spans cross any linear map).
* **swap** — adjacent transposition IS the diamond: `calibrated_diamond`
  identifies the two-step towers after `swapLast`, the twist rides the tail
  (`IsClimb.twist` — a climb twisted by a base equiv, `padTwist` extending it
  slot-fixing through each step), and the read absorbs the swap
  (`climbRead_twist` + `readStep_swap`: the two deposited names commute by
  `add_right_comm`).
* **trans** — capture-free legality is permutation-invariant
  (`ClimbLegal.perm`, one Steinitz `atom_exchange` per adjacent swap), so the
  middle climb exists and the reads chain.

`climbRead_pad` is the stability seed carried forward: a padded vector reads
as pure base — growing the window never rewrites the read.

Model-verified before carving (`probe_limit.py`, checks D/E, the previous
sitting): every pooled window climb — all windows, all sampled orders and
interleavings — span-agrees with the limit assignment under the atom-named
embedding, over five window configurations at `q ∈ {2,3}`, twisted base
systems throughout; the diamond seed 384/384 exhaustive on `PG(4,2)`.
-/

namespace Foam.Bridges

universe u

/-! ## The read calculus: slots to atom names, lattice-free -/

section ReadAlgebra

variable {L : Type u} {K : Type*} [DivisionRing K]

theorem span_map_of_span_eq {M N : Type*} [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] (f : M →ₗ[K] N) {u v : M}
    (h : Submodule.span K {u} = Submodule.span K {v}) :
    Submodule.span K {f u} = Submodule.span K {f v} := by
  rw [← Set.image_singleton, ← Submodule.map_span, h, Submodule.map_span,
    Set.image_singleton]

def padTwist {m : ℕ} (σ : (Fin m → K) ≃ₗ[K] (Fin m → K)) :
    (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K) where
  toFun v := Fin.snoc (σ (v ∘ Fin.castSucc)) (v (Fin.last m))
  invFun v := Fin.snoc (σ.symm (v ∘ Fin.castSucc)) (v (Fin.last m))
  left_inv v := by
    simp only [snoc_comp_castSucc, Fin.snoc_last, LinearEquiv.symm_apply_apply]
    exact ladder_snoc_strip v
  right_inv v := by
    simp only [snoc_comp_castSucc, Fin.snoc_last, LinearEquiv.apply_symm_apply]
    exact ladder_snoc_strip v
  map_add' u v := by
    have h : (u + v) ∘ Fin.castSucc = u ∘ Fin.castSucc + v ∘ Fin.castSucc := rfl
    simp only [h, map_add, Pi.add_apply, ladder_snoc_add]
  map_smul' c v := by
    have h : (c • v) ∘ Fin.castSucc = c • (v ∘ Fin.castSucc) := rfl
    simp only [RingHom.id_apply, h, map_smul, Pi.smul_apply, smul_eq_mul,
      ladder_snoc_smul]

theorem padTwist_apply {m : ℕ} (σ : (Fin m → K) ≃ₗ[K] (Fin m → K))
    (v : Fin (m + 1) → K) :
    padTwist σ v = Fin.snoc (σ (v ∘ Fin.castSucc)) (v (Fin.last m)) := rfl

theorem padTwist_snoc {m : ℕ} (σ : (Fin m → K) ≃ₗ[K] (Fin m → K))
    (v : Fin m → K) (a : K) :
    padTwist σ (Fin.snoc v a) = Fin.snoc (σ v) a := by
  rw [padTwist_apply, snoc_comp_castSucc, Fin.snoc_last]

def climbTwist : {m : ℕ} → (ws : List (L × L)) →
    ((Fin m → K) ≃ₗ[K] (Fin m → K)) →
    (Fin (climbDim m ws) → K) ≃ₗ[K] (Fin (climbDim m ws) → K)
  | _, [], σ => σ
  | _, _ :: ws, σ => climbTwist ws (padTwist σ)

variable [DecidableEq L]

def readStep {m : ℕ} (w : L) :
    ((Fin (m + 1) → K) × (L → K)) →ₗ[K] (Fin m → K) × (L → K) :=
  LinearMap.prod
    (LinearMap.funLeft K K Fin.castSucc ∘ₗ LinearMap.fst K _ _)
    (LinearMap.snd K _ _ +
      LinearMap.single K (fun _ => K) w ∘ₗ
        LinearMap.proj (Fin.last m) ∘ₗ LinearMap.fst K _ _)

theorem readStep_apply {m : ℕ} (w : L) (p : (Fin (m + 1) → K) × (L → K)) :
    readStep w p
      = (p.1 ∘ Fin.castSucc, p.2 + Pi.single w (p.1 (Fin.last m))) := rfl

def climbRead : {n : ℕ} → (ws : List (L × L)) →
    (Fin (climbDim n ws) → K) →ₗ[K] (Fin n → K) × (L → K)
  | _, [] => LinearMap.prod LinearMap.id 0
  | _, (w, _) :: ws => readStep w ∘ₗ climbRead ws

theorem climbRead_pad : ∀ (ws : List (L × L)) {n : ℕ} (v : Fin n → K),
    climbRead ws (climbPad ws v) = (v, 0)
  | [], _, _ => rfl
  | (w, _) :: ws, _, v => by
    show readStep w (climbRead ws (climbPad ws (Fin.snoc v 0))) = (v, 0)
    rw [climbRead_pad ws (Fin.snoc v 0)]
    simp [readStep_apply]

theorem climbRead_twist : ∀ (ws : List (L × L)) {m : ℕ}
    (σ : (Fin m → K) ≃ₗ[K] (Fin m → K)) (v : Fin (climbDim m ws) → K),
    climbRead ws (climbTwist ws σ v)
      = (σ (climbRead ws v).1, (climbRead ws v).2)
  | [], _, _, _ => rfl
  | (w, _) :: ws, _, σ, v => by
    show readStep w (climbRead ws (climbTwist ws (padTwist σ) v))
      = (σ (readStep w (climbRead ws v)).1, (readStep w (climbRead ws v)).2)
    rw [climbRead_twist ws (padTwist σ) v]
    simp [readStep_apply, padTwist_apply]

theorem readStep_swap {m : ℕ} (w₁ w₂ : L) (v : Fin (m + 2) → K)
    (s : L → K) :
    readStep w₁ (readStep w₂ (swapLast v, s))
      = readStep w₂ (readStep w₁ (v, s)) := by
  refine Prod.ext ?_ ?_
  · funext j
    show swapLast v (Fin.castSucc (Fin.castSucc j))
      = v (Fin.castSucc (Fin.castSucc j))
    rw [swapLast_apply, Equiv.swap_apply_of_ne_of_ne
      (fun h => (Fin.castSucc_lt_last j).ne (Fin.castSucc_injective _ h))
      (Fin.castSucc_lt_last _).ne]
  · show s + Pi.single w₂ (swapLast v (Fin.last (m + 1)))
        + Pi.single w₁ (swapLast v (Fin.castSucc (Fin.last m)))
      = s + Pi.single w₁ (v (Fin.last (m + 1)))
        + Pi.single w₂ (v (Fin.castSucc (Fin.last m)))
    have h2 : swapLast v (Fin.castSucc (Fin.last m)) = v (Fin.last (m + 1)) := by
      rw [swapLast_apply, Equiv.swap_apply_left]
    rw [swapLast_last, h2]
    exact add_right_comm s _ _

end ReadAlgebra

/-! ## The system stratum: twist rides the climb, legality rides the perm -/

section PermSystems

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]
variable {K : Type*} [DivisionRing K]

omit [BoundedOrder L] [ComplementedLattice L] [IsModularLattice L]
  [IsAtomistic L] in
theorem climbFlat_perm {ws ws' : List (L × L)} (hperm : ws.Perm ws') :
    ∀ x : L, climbFlat x ws = climbFlat x ws' := by
  induction hperm with
  | nil => exact fun _ => rfl
  | cons ww _ ih => exact fun x => ih (x ⊔ ww.1)
  | swap wwA wwB l =>
    intro x
    show climbFlat (x ⊔ wwB.1 ⊔ wwA.1) l = climbFlat (x ⊔ wwA.1 ⊔ wwB.1) l
    rw [sup_right_comm]
  | trans _ _ ih₁ ih₂ => exact fun x => (ih₁ x).trans (ih₂ x)

omit [ComplementedLattice L] [IsAtomistic L] in
theorem ClimbLegal.perm {b₀ : L} {ws ws' : List (L × L)}
    (hperm : ws.Perm ws') :
    ∀ x : L, ClimbLegal b₀ ws x → ClimbLegal b₀ ws' x := by
  induction hperm with
  | nil => exact fun _ h => h
  | cons ww _ ih =>
    rintro x ⟨hw, hwx, hw', hw'le, hw'b, hw'w, htail⟩
    exact ⟨hw, hwx, hw', hw'le, hw'b, hw'w, ih (x ⊔ ww.1) htail⟩
  | swap wwA wwB l =>
    obtain ⟨w₂, w₂'⟩ := wwA
    obtain ⟨w₁, w₁'⟩ := wwB
    rintro x ⟨hw₁, hw₁x, hw₁', hw₁'le, hw₁'b, hw₁'w,
      hw₂, hw₂xw, hw₂', hw₂'le, hw₂'b, hw₂'w, htail⟩
    exact ⟨hw₂, fun h => hw₂xw (h.trans le_sup_left), hw₂', hw₂'le, hw₂'b,
      hw₂'w, hw₁, fun h => hw₂xw (atom_exchange hw₂ h hw₁x), hw₁', hw₁'le,
      hw₁'b, hw₁'w, sup_right_comm x w₁ w₂ ▸ htail⟩
  | trans _ _ ih₁ ih₂ => exact fun x h => ih₂ x (ih₁ x h)

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem Calibrated.twist {x w b₀ w' : L} {n : ℕ} {P : PointSys x n K}
    {Q : PointSys (x ⊔ w) (n + 1) K} (hQ : Calibrated P w b₀ w' Q)
    (σ : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    Calibrated (P.twist σ) w b₀ w' (Q.twist (padTwist σ)) where
  base p hp hpx := by
    have h := pin_map_span_singleton (padTwist σ) _ _ (hQ.base p hp hpx)
    rw [padTwist_snoc] at h
    exact h
  apex := by
    have h := pin_map_span_singleton (padTwist σ) _ _ hQ.apex
    rw [padTwist_snoc, map_zero] at h
    exact h
  unit := by
    have h := pin_map_span_singleton (padTwist σ) _ _ hQ.unit
    rw [padTwist_snoc] at h
    exact h

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem IsClimb.twist {b₀ : L} :
    ∀ (ws : List (L × L)) (x : L) (n : ℕ) (P : PointSys x n K)
      (Q : PointSys (climbFlat x ws) (climbDim n ws) K)
      (σ : (Fin n → K) ≃ₗ[K] (Fin n → K)),
      IsClimb b₀ ws x n P Q →
      IsClimb b₀ ws x n (P.twist σ) (Q.twist (climbTwist ws σ))
  | [], _, _, P, Q, σ, hQ => by
    have h : Q = P := hQ
    subst h
    rfl
  | (w, w') :: ws, x, n, P, Q, σ, hQ => by
    obtain ⟨Q₁, hcal, hpad, hclimb⟩ := hQ
    refine ⟨Q₁.twist (padTwist σ), hcal.twist σ, ?_, ?_⟩
    · intro p hp
      show padTwist σ (Q₁.hv p) = Fin.snoc (σ (P.hv p)) 0
      rw [hpad p hp, padTwist_snoc]
    · exact IsClimb.twist ws (x ⊔ w) (n + 1) Q₁ Q (padTwist σ) hclimb

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem IsClimb.reflat {b₀ : L} {ws : List (L × L)} {x y : L} {n : ℕ}
    {P : PointSys x n K} {Q : PointSys (climbFlat x ws) (climbDim n ws) K}
    (h : x = y) (hf : climbFlat x ws = climbFlat y ws)
    (hQ : IsClimb b₀ ws x n P Q) :
    IsClimb b₀ ws y n (P.reflat h) (Q.reflat hf) := by
  subst h
  exact hQ

variable [DecidableEq L]

omit [ComplementedLattice L] in
theorem isClimb_perm_agree {b₀ : L}
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    {ws ws' : List (L × L)} (hperm : ws.Perm ws') :
    ∀ (x : L) (n : ℕ) (P : PointSys x n K)
      (Q : PointSys (climbFlat x ws) (climbDim n ws) K)
      (Q' : PointSys (climbFlat x ws') (climbDim n ws') K),
      3 ≤ n → IsAtom b₀ → b₀ ≤ x → ClimbLegal b₀ ws x →
      IsClimb b₀ ws x n P Q → IsClimb b₀ ws' x n P Q' →
      ∀ t : L, IsAtom t → t ≤ climbFlat x ws →
        Submodule.span K {climbRead ws (Q.hv t)}
          = Submodule.span K {climbRead ws' (Q'.hv t)} := by
  induction hperm with
  | nil =>
    intro x n P Q Q' _ _ _ _ hQ hQ' t _ _
    have h1 : Q = P := hQ
    have h2 : Q' = P := hQ'
    subst h1
    subst h2
    rfl
  | @cons ww l₁ l₂ hperm ih =>
    intro x n P Q Q' hn hb₀ hb₀x hleg hQ hQ' t ht ht_le
    obtain ⟨w, w'⟩ := ww
    obtain ⟨hw, hwx, hw', hw'le, hw'b, hw'w, htail⟩ := hleg
    obtain ⟨Q₁, hcal, hpad, hclimb⟩ := hQ
    obtain ⟨Q₁', hcal', hpad', hclimb'⟩ := hQ'
    have hleg₂ : ClimbLegal b₀ l₂ (x ⊔ w) := ClimbLegal.perm hperm (x ⊔ w) htail
    obtain ⟨Qaux, hQaux⟩ := isClimb_exists h_irred l₂ (x ⊔ w) (n + 1) Q₁
      (hn.trans (Nat.le_succ n)) hb₀ (hb₀x.trans le_sup_left) hleg₂
    have hIH := ih (x ⊔ w) (n + 1) Q₁ Q Qaux (hn.trans (Nat.le_succ n)) hb₀
      (hb₀x.trans le_sup_left) htail hclimb hQaux t ht ht_le
    have hspan1 : ∀ s : L, IsAtom s → s ≤ x ⊔ w →
        Submodule.span K {Q₁.hv s} = Submodule.span K {Q₁'.hv s} :=
      fun s hs hs_le => calibrated_agree hn h_irred hw hwx hb₀ hb₀x hw'
        hw'le hw'b hw'w hcal hcal' hs hs_le
    have hb1 : Q₁.hv b₀ = Q₁'.hv b₀ := by
      rw [hpad b₀ hb₀x, hpad' b₀ hb₀x]
    have hagree := (isClimb_agree_congr h_irred l₂ (x ⊔ w) (n + 1) Q₁ Q₁'
      Qaux Q' (hn.trans (Nat.le_succ n)) hb₀ (hb₀x.trans le_sup_left) hleg₂
      hspan1 hb1 hQaux hclimb').1 t ht (climbFlat_perm hperm (x ⊔ w) ▸ ht_le)
    have h1 := span_map_of_span_eq (readStep w) hIH
    have h2 := span_map_of_span_eq (readStep w ∘ₗ climbRead l₂) hagree
    exact h1.trans h2
  | @swap wwA wwB l =>
    intro x n P Q Q' hn hb₀ hb₀x hleg hQ hQ' t ht ht_le
    obtain ⟨w₂, w₂'⟩ := wwA
    obtain ⟨w₁, w₁'⟩ := wwB
    obtain ⟨hw₁, hw₁x, hw₁', hw₁'le, hw₁'b, hw₁'w,
      hw₂, hw₂xw, hw₂', hw₂'le, hw₂'b, hw₂'w, htail⟩ := hleg
    obtain ⟨Qa₁, hcalA₁, hpadA₁, hQtailA⟩ := hQ
    obtain ⟨Qa₂, hcalA₂, hpadA₂, hclimbA⟩ := hQtailA
    obtain ⟨Qb₁, hcalB₁, hpadB₁, hQtailB⟩ := hQ'
    obtain ⟨Qb₂, hcalB₂, hpadB₂, hclimbB⟩ := hQtailB
    have hdia : ∀ s : L, IsAtom s → s ≤ x ⊔ w₁ ⊔ w₂ →
        Submodule.span K {Qa₂.hv s}
          = Submodule.span K {swapLast (Qb₂.hv s)} :=
      fun s hs hs_le => calibrated_diamond hn h_irred hw₁ hw₁x hw₂ hw₂xw
        hb₀ hb₀x hw₁' hw₁'le hw₁'b hw₁'w hw₂' hw₂'le hw₂'b hw₂'w
        hcalA₁ hpadA₁ hcalA₂ hcalB₁ hpadB₁ hcalB₂ hpadB₂ hs hs_le
    have hflat : x ⊔ w₂ ⊔ w₁ = x ⊔ w₁ ⊔ w₂ := sup_right_comm x w₂ w₁
    have hfl2 : climbFlat (x ⊔ w₂ ⊔ w₁) l = climbFlat (x ⊔ w₁ ⊔ w₂) l := by
      rw [hflat]
    set R : PointSys (x ⊔ w₁ ⊔ w₂) (n + 2) K :=
      (Qb₂.twist swapLast).reflat hflat with hR
    set Qc : PointSys (climbFlat (x ⊔ w₁ ⊔ w₂) l) (climbDim (n + 2) l) K :=
      (Q'.twist (climbTwist l swapLast)).reflat hfl2 with hQc
    have hRhv : ∀ s : L, R.hv s = swapLast (Qb₂.hv s) := by
      intro s
      rw [hR, PointSys.reflat_hv]
      rfl
    have hQchv : ∀ s : L, Qc.hv s = climbTwist l swapLast (Q'.hv s) := by
      intro s
      rw [hQc, PointSys.reflat_hv]
      rfl
    have hclimbR : IsClimb b₀ l (x ⊔ w₁ ⊔ w₂) (n + 2) R Qc :=
      IsClimb.reflat hflat hfl2
        (IsClimb.twist l (x ⊔ w₂ ⊔ w₁) (n + 2) Qb₂ Q' swapLast hclimbB)
    have hspan : ∀ s : L, IsAtom s → s ≤ x ⊔ w₁ ⊔ w₂ →
        Submodule.span K {Qa₂.hv s} = Submodule.span K {R.hv s} := by
      intro s hs hs_le
      rw [hRhv s]
      exact hdia s hs hs_le
    have hb : Qa₂.hv b₀ = R.hv b₀ := by
      rw [hpadA₂ b₀ (hb₀x.trans le_sup_left), hpadA₁ b₀ hb₀x, hRhv,
        hpadB₂ b₀ (hb₀x.trans le_sup_left), hpadB₁ b₀ hb₀x,
        swapLast_snoc_snoc]
    have hagree := (isClimb_agree_congr h_irred l (x ⊔ w₁ ⊔ w₂) (n + 2)
      Qa₂ R Q Qc ((hn.trans (Nat.le_succ n)).trans (Nat.le_succ (n + 1)))
      hb₀ (hb₀x.trans (le_sup_left.trans le_sup_left)) htail hspan hb
      hclimbA hclimbR).1 t ht ht_le
    have hmap := span_map_of_span_eq
      (readStep w₁ ∘ₗ (readStep w₂ ∘ₗ climbRead l)) hagree
    have hcomp : (readStep w₁ ∘ₗ (readStep w₂ ∘ₗ climbRead l)) (Qc.hv t)
        = climbRead ((w₂, w₂') :: (w₁, w₁') :: l) (Q'.hv t) := by
      show readStep w₁ (readStep w₂ (climbRead l (Qc.hv t)))
        = readStep w₂ (readStep w₁ (climbRead l (Q'.hv t)))
      rw [hQchv t, climbRead_twist l swapLast (Q'.hv t), readStep_swap]
    rw [hcomp] at hmap
    exact hmap
  | @trans l₁ l₂ l₃ hp₁ hp₂ ih₁ ih₂ =>
    intro x n P Q Q' hn hb₀ hb₀x hleg hQ hQ' t ht ht_le
    have hleg₂ : ClimbLegal b₀ l₂ x := ClimbLegal.perm hp₁ x hleg
    obtain ⟨Qmid, hQmid⟩ := isClimb_exists h_irred l₂ x n P hn hb₀ hb₀x hleg₂
    exact (ih₁ x n P Q Qmid hn hb₀ hb₀x hleg hQ hQmid t ht ht_le).trans
      (ih₂ x n P Qmid Q' hn hb₀ hb₀x hleg₂ hQmid hQ' t ht
        (climbFlat_perm hp₁ x ▸ ht_le))

end PermSystems

end Foam.Bridges

/-! ## Axiom audit -/

/-- info: 'Foam.Bridges.span_map_of_span_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.span_map_of_span_eq

/-- info: 'Foam.Bridges.padTwist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.padTwist

/-- info: 'Foam.Bridges.padTwist_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.padTwist_apply

/-- info: 'Foam.Bridges.padTwist_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.padTwist_snoc

/-- info: 'Foam.Bridges.climbTwist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.climbTwist

/-- info: 'Foam.Bridges.readStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.readStep

/-- info: 'Foam.Bridges.readStep_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.readStep_apply

/-- info: 'Foam.Bridges.climbRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.climbRead

/-- info: 'Foam.Bridges.climbRead_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.climbRead_pad

/-- info: 'Foam.Bridges.climbRead_twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.climbRead_twist

/-- info: 'Foam.Bridges.readStep_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.readStep_swap

/-- info: 'Foam.Bridges.climbFlat_perm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.climbFlat_perm

/-- info: 'Foam.Bridges.ClimbLegal.perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.ClimbLegal.perm

/-- info: 'Foam.Bridges.Calibrated.twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.Calibrated.twist

/-- info: 'Foam.Bridges.IsClimb.twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.IsClimb.twist

/-- info: 'Foam.Bridges.IsClimb.reflat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.IsClimb.reflat

/-- info: 'Foam.Bridges.isClimb_perm_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.isClimb_perm_agree

