import Bridges.FTPG.Ground

/-!
# Camp four, second pitch: the calibrated step and its rigidity

`PointSys.step` extends a point system by one atom, but its output is
gauge-dependent: the heights carry a free factor in `K*`.  This pitch pins the
gauge.  A *calibrated* extension fixes, span-level, the coordinates of the
new atom `w` (the last basis vector) and of one calibration atom `w'` — a
third atom on `b₀ ⊔ w` for a fixed base atom `b₀` — at height `1` over `b₀`'s
stored representative.

* `calibrated_agree` — **rigidity**: any two calibrated extensions agree
  span-level on every atom.  Constructive: an affine atom off the calibration
  line is pinned by intersecting two pencil planes (through `w` and through
  `w'` — the `w'`-trace is a shear trace, so the standing shear stratum
  supplies every side condition), and an atom on the calibration line is
  pinned by routing through an auxiliary axis `u₁` off `b₀`'s span.
* `PointSys.calibrated_exists` — existence: the ladder step composed with the
  height rescale `heightEquiv` (right multiplication in the last slot, which
  is left-linear).
* `calibrated_last_zero_iff` — membership in the old flat reads off the last
  slot: the window sees exactly its own coordinates.

Model-verified before carving (`probe_coherence.py`): rigidity, the exact
`K*`-freedom, and the two-step diamond, over `PG(3,q)`/`PG(4,q)`,
`q ∈ {2,3,5}`, twisted base systems throughout.
-/

namespace Foam.Bridges

universe u

/-! ## The coefficient stratum: shapes, the two-plane pin, the height rescale -/

section PinAlgebra

variable {K : Type*} [DivisionRing K] {n : ℕ}

theorem pin_span_pair_congr {m : ℕ} {a a' b b' : Fin m → K}
    (ha : Submodule.span K {a} = Submodule.span K {a'})
    (hb : Submodule.span K {b} = Submodule.span K {b'}) :
    Submodule.span K ({a, b} : Set (Fin m → K)) =
      Submodule.span K ({a', b'} : Set (Fin m → K)) := by
  rw [show ({a, b} : Set (Fin m → K)) = insert a {b} from rfl,
    show ({a', b'} : Set (Fin m → K)) = insert a' {b'} from rfl,
    Submodule.span_insert, Submodule.span_insert, ha, hb]

theorem pin_shape {v : Fin n → K} {z : Fin (n+1) → K}
    (hz : z ∈ Submodule.span K
      ({Fin.snoc v 0, Fin.snoc 0 1} : Set (Fin (n+1) → K))) :
    ∃ ξ η : K, z = Fin.snoc (ξ • v) η := by
  obtain ⟨ξ, η, h⟩ := Submodule.mem_span_pair.mp hz
  refine ⟨ξ, η, ?_⟩
  rw [← h, ladder_snoc_comb, smul_zero, add_zero, mul_zero, zero_add, mul_one]

theorem pin_meet {va vc : Fin n → K} (hva : va ≠ 0)
    (hind : vc ∉ Submodule.span K {va}) {μ ρ σ : K}
    {z : Fin (n+1) → K}
    (h1 : z ∈ Submodule.span K
      ({Fin.snoc va 0, Fin.snoc 0 1} : Set (Fin (n+1) → K)))
    (h2 : z ∈ Submodule.span K
      ({Fin.snoc vc μ, Fin.snoc (ρ • va + σ • vc) 0} : Set (Fin (n+1) → K))) :
    z ∈ Submodule.span K {(Fin.snoc (ρ • va) (-(σ * μ)) : Fin (n+1) → K)} := by
  obtain ⟨α, β, hz1⟩ := Submodule.mem_span_pair.mp h1
  obtain ⟨γ, δ, hz2⟩ := Submodule.mem_span_pair.mp h2
  rw [ladder_snoc_comb, smul_zero, add_zero, mul_zero, zero_add, mul_one] at hz1
  rw [ladder_snoc_comb, mul_zero, add_zero] at hz2
  have heq := hz1.trans hz2.symm
  obtain ⟨hbase, hlast⟩ := ladder_snoc_eq_iff.mp heq
  have hbase' : α • va + (0 : K) • vc
      = (δ * ρ) • va + (γ + δ * σ) • vc := by
    rw [zero_smul, add_zero, hbase, smul_add, smul_smul, smul_smul, add_smul]
    abel
  obtain ⟨hα, hγδ⟩ := ladder_pair_unique hva hind hbase'
  have hγ : γ = -(δ * σ) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hγδ.symm
  refine Submodule.mem_span_singleton.mpr ⟨δ, ?_⟩
  rw [ladder_snoc_smul, smul_smul, ← hz1, hα, hlast, hγ, mul_neg, neg_mul,
    mul_assoc]

theorem pin_eq {m : ℕ} {v z z' : Fin m → K} (hz : z ≠ 0) (hz' : z' ≠ 0)
    (h1 : z ∈ Submodule.span K {v}) (h2 : z' ∈ Submodule.span K {v}) :
    Submodule.span K {z} = Submodule.span K {z'} := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h2
  have ha0 : a ≠ 0 := fun h => hz (by rw [← ha, h, zero_smul])
  have hb0 : b ≠ 0 := fun h => hz' (by rw [← hb, h, zero_smul])
  rw [← ha, ← hb, ladder_span_singleton_smul ha0, ladder_span_singleton_smul hb0]

theorem pin_snoc_zero_span_congr {u v : Fin n → K} (hu : u ≠ 0)
    (h : Submodule.span K {u} = Submodule.span K {v}) :
    Submodule.span K {(Fin.snoc u 0 : Fin (n+1) → K)}
      = Submodule.span K {Fin.snoc v 0} := by
  have hmem : u ∈ Submodule.span K {v} := by
    rw [← h]; exact Submodule.mem_span_singleton_self u
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have ha0 : a ≠ 0 := fun h0 => hu (by rw [← ha, h0, zero_smul])
  rw [← ha, ← ladder_span_singleton_smul (v := Fin.snoc v 0) ha0,
    ladder_snoc_smul, mul_zero]

theorem pin_map_mem_span_singleton {m : ℕ}
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) {u v : Fin m → K}
    (h : e u ∈ Submodule.span K {e v}) : u ∈ Submodule.span K {v} := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  exact Submodule.mem_span_singleton.mpr
    ⟨a, e.injective (by rw [map_smul, ha])⟩

theorem pin_map_span_singleton {m : ℕ}
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) (u v : Fin m → K)
    (h : Submodule.span K {u} = Submodule.span K {v}) :
    Submodule.span K {e u} = Submodule.span K {e v} := by
  have huv : u ∈ Submodule.span K {v} := by
    rw [← h]; exact Submodule.mem_span_singleton_self u
  have hvu : v ∈ Submodule.span K {u} := by
    rw [h]; exact Submodule.mem_span_singleton_self v
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp huv
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hvu
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.mem_span_singleton.mpr ⟨a, by rw [← map_smul, ha]⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.mem_span_singleton.mpr ⟨b, by rw [← map_smul, hb]⟩

theorem pin_map_mem_span_pair_iff {m : ℕ}
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) {u v z : Fin m → K} :
    e z ∈ Submodule.span K ({e u, e v} : Set (Fin m → K)) ↔
      z ∈ Submodule.span K ({u, v} : Set (Fin m → K)) := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h
    exact Submodule.mem_span_pair.mpr
      ⟨a, b, e.injective (by rw [map_add, map_smul, map_smul, hab])⟩
  · intro h
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h
    exact Submodule.mem_span_pair.mpr
      ⟨a, b, by rw [← map_smul, ← map_smul, ← map_add, hab]⟩

noncomputable def heightEquiv (g : K) (hg : g ≠ 0) :
    (Fin (n+1) → K) ≃ₗ[K] (Fin (n+1) → K) where
  toFun v := fun i => if i = Fin.last n then v i * g else v i
  invFun v := fun i => if i = Fin.last n then v i * g⁻¹ else v i
  left_inv v := by
    funext i
    by_cases h : i = Fin.last n <;>
      simp [h, mul_assoc, mul_inv_cancel₀ hg]
  right_inv v := by
    funext i
    by_cases h : i = Fin.last n <;>
      simp [h, mul_assoc, inv_mul_cancel₀ hg]
  map_add' u v := by
    funext i
    by_cases h : i = Fin.last n <;> simp [h, add_mul]
  map_smul' c v := by
    funext i
    by_cases h : i = Fin.last n <;> simp [h, mul_assoc]

theorem heightEquiv_snoc (g : K) (hg : g ≠ 0) (v : Fin n → K) (a : K) :
    heightEquiv g hg (Fin.snoc v a) = Fin.snoc v (a * g) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [heightEquiv]
  · intro j
    simp [heightEquiv, (Fin.castSucc_lt_last j).ne]

end PinAlgebra

/-! ## The system stratum: the twist, the calibration, the rigidity -/

section PinSystems

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]
variable {K : Type*} [DivisionRing K] {n : ℕ} {x w b₀ w' : L}

noncomputable def PointSys.twist {y : L} (P : PointSys y n K)
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) : PointSys y n K where
  hv t := e (P.hv t)
  ne_zero hp hpx h := P.ne_zero hp hpx (e.map_eq_zero_iff.mp h)
  span_inj hp hpx hq hqx hpq h :=
    P.span_inj hp hpx hq hqx hpq (pin_map_mem_span_singleton e h)
  span_surj v hv := by
    have hv' : e.symm v ≠ 0 := fun h => hv (by
      have h1 := congrArg e h
      rwa [e.apply_symm_apply, map_zero] at h1)
    obtain ⟨p, hp, hpx, hspan⟩ := P.span_surj (e.symm v) hv'
    refine ⟨p, hp, hpx, ?_⟩
    have h1 := pin_map_span_singleton e _ _ hspan
    rwa [e.apply_symm_apply] at h1
  collinear_iff hp hpx hq hqx hr hrx hpq := by
    rw [pin_map_mem_span_pair_iff]
    exact P.collinear_iff hp hpx hq hqx hr hrx hpq

structure Calibrated (P : PointSys x n K) (w b₀ w' : L)
    (Q : PointSys (x ⊔ w) (n+1) K) : Prop where
  base : ∀ p, IsAtom p → p ≤ x →
    Submodule.span K {Q.hv p} = Submodule.span K {Fin.snoc (P.hv p) 0}
  apex : Submodule.span K {Q.hv w}
    = Submodule.span K {(Fin.snoc 0 1 : Fin (n+1) → K)}
  unit : Submodule.span K {Q.hv w'}
    = Submodule.span K {Fin.snoc (P.hv b₀) 1}

variable {P : PointSys x n K}

omit [ComplementedLattice L] in
theorem calibrated_agree_main
    (hw : IsAtom w) (hwx : ¬ w ≤ x)
    (hb₀ : IsAtom b₀) (hb₀x : b₀ ≤ x)
    (hw' : IsAtom w') (hw'_le : w' ≤ b₀ ⊔ w) (hw'b : w' ≠ b₀) (hw'w : w' ≠ w)
    {Q Q' : PointSys (x ⊔ w) (n+1) K}
    (hQ : Calibrated P w b₀ w' Q) (hQ' : Calibrated P w b₀ w' Q')
    {t : L} (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) (htx : ¬ t ≤ x)
    (htb : ¬ t ≤ b₀ ⊔ w) :
    Submodule.span K {Q.hv t} = Submodule.span K {Q'.hv t} := by
  obtain ⟨hw'x, hw'_xw, _, _, _⟩ :=
    ladder_center hw hwx hb₀ hb₀x hw' hw'_le hw'b hw'w
  have htw : t ≠ w := fun h => htb (h ▸ le_sup_right)
  have htw' : t ≠ w' := fun h => htb (h ▸ hw'_le)
  have hb_atom : IsAtom (project w t x) :=
    ladder_trace_atom hw hwx hw le_sup_right ht ht_le htx htw
  have hb_x : project w t x ≤ x := inf_le_right
  have ht_bw : t ≤ project w t x ⊔ w :=
    (ladder_regen hw hwx hw le_sup_right hwx ht ht_le htx htw).2
  have hbb₀ : project w t x ≠ b₀ := fun h => htb (h ▸ ht_bw)
  have hh2_atom : IsAtom (project w' t x) :=
    ladder_trace_atom hw hwx hw' hw'_xw ht ht_le htx htw'
  have hh2_x : project w' t x ≤ x := inf_le_right
  have ht_h2 : t ≤ project w' t x ⊔ w' :=
    (ladder_regen hw hwx hw' hw'_xw hw'x ht ht_le htx htw').2
  have hh2_le : project w' t x ≤ project w t x ⊔ b₀ :=
    ladder_shear_le hw hwx hb₀x hw'_le ht ht_le htx htw
  have hmem : P.hv (project w' t x) ∈
      Submodule.span K {P.hv (project w t x), P.hv b₀} :=
    (P.collinear_iff hb_atom hb_x hb₀ hb₀x hh2_atom hh2_x hbb₀).mp hh2_le
  obtain ⟨ρ, σ, hρσ⟩ := Submodule.mem_span_pair.mp hmem
  have hb_ne : P.hv (project w t x) ≠ 0 := P.ne_zero hb_atom hb_x
  have hind : P.hv b₀ ∉ Submodule.span K {P.hv (project w t x)} :=
    P.span_inj hb_atom hb_x hb₀ hb₀x hbb₀
  have hbw : project w t x ≠ w := fun h => hwx (h ▸ hb_x)
  have hw'h2 : w' ≠ project w' t x := fun h => hw'x (h ▸ hh2_x)
  have key : ∀ (R : PointSys (x ⊔ w) (n+1) K), Calibrated P w b₀ w' R →
      R.hv t ∈ Submodule.span K
        {(Fin.snoc (ρ • P.hv (project w t x)) (-(σ * 1)) : Fin (n+1) → K)} := by
    intro R hR
    have m1 : R.hv t ∈ Submodule.span K
        ({Fin.snoc (P.hv (project w t x)) 0, Fin.snoc 0 1} :
          Set (Fin (n+1) → K)) := by
      have h0 : R.hv t ∈
          Submodule.span K {R.hv (project w t x), R.hv w} :=
        (R.collinear_iff hb_atom (hb_x.trans le_sup_left) hw le_sup_right
          ht ht_le hbw).mp ht_bw
      rwa [pin_span_pair_congr (hR.base _ hb_atom hb_x) hR.apex] at h0
    have m2 : R.hv t ∈ Submodule.span K
        ({Fin.snoc (P.hv b₀) 1,
          Fin.snoc (ρ • P.hv (project w t x) + σ • P.hv b₀) 0} :
          Set (Fin (n+1) → K)) := by
      have h0 : R.hv t ∈
          Submodule.span K {R.hv w', R.hv (project w' t x)} :=
        (R.collinear_iff hw' hw'_xw hh2_atom (hh2_x.trans le_sup_left)
          ht ht_le hw'h2).mp (by rwa [sup_comm] at ht_h2)
      rw [pin_span_pair_congr hR.unit (hR.base _ hh2_atom hh2_x)] at h0
      rwa [hρσ]
    exact pin_meet hb_ne hind m1 m2
  exact pin_eq (Q.ne_zero ht ht_le) (Q'.ne_zero ht ht_le) (key Q hQ) (key Q' hQ')

omit [ComplementedLattice L] in
theorem calibrated_agree (hn : 3 ≤ n)
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (hw : IsAtom w) (hwx : ¬ w ≤ x)
    (hb₀ : IsAtom b₀) (hb₀x : b₀ ≤ x)
    (hw' : IsAtom w') (hw'_le : w' ≤ b₀ ⊔ w) (hw'b : w' ≠ b₀) (hw'w : w' ≠ w)
    {Q Q' : PointSys (x ⊔ w) (n+1) K}
    (hQ : Calibrated P w b₀ w' Q) (hQ' : Calibrated P w b₀ w' Q')
    {t : L} (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) :
    Submodule.span K {Q.hv t} = Submodule.span K {Q'.hv t} := by
  by_cases htx : t ≤ x
  · rw [hQ.base t ht htx, hQ'.base t ht htx]
  by_cases htw : t = w
  · rw [htw, hQ.apex, hQ'.apex]
  by_cases htb : t ≤ b₀ ⊔ w
  case neg =>
    exact calibrated_agree_main hw hwx hb₀ hb₀x hw' hw'_le hw'b hw'w
      hQ hQ' ht ht_le htx htb
  by_cases htw' : t = w'
  · rw [htw', hQ.unit, hQ'.unit]
  obtain ⟨hw'x, hw'_xw, _, _, _⟩ :=
    ladder_center hw hwx hb₀ hb₀x hw' hw'_le hw'b hw'w
  have hbase_t : project w t x = b₀ :=
    (ladder_base_iff hw hwx ht ht_le htx htw hb₀ hb₀x).mpr htb
  have hspan_ne : Submodule.span K ({P.hv b₀} : Set (Fin n → K)) ≠ ⊤ := by
    have h := ladder_span_pair_ne_top hn (P.hv b₀) (P.hv b₀)
    rwa [Set.pair_eq_singleton] at h
  obtain ⟨v, -, hv_not⟩ := SetLike.exists_of_lt
    (lt_top_iff_ne_top.mpr hspan_ne)
  have hv0 : v ≠ 0 := fun h => hv_not (h ▸ Submodule.zero_mem _)
  obtain ⟨u₁, hu₁, hu₁x, hu₁span⟩ := P.span_surj v hv0
  have hu₁_ind : P.hv u₁ ∉ Submodule.span K {P.hv b₀} := by
    intro h
    apply hv_not
    have h1 : v ∈ Submodule.span K {P.hv u₁} := by
      rw [hu₁span]; exact Submodule.mem_span_singleton_self v
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
    rw [← ha]
    exact Submodule.smul_mem _ _ h
  have hu₁b₀ : u₁ ≠ b₀ := fun h => hu₁_ind (by
    rw [h]; exact Submodule.mem_span_singleton_self _)
  have hu₁w : u₁ ≠ w := fun h => hwx (h ▸ hu₁x)
  obtain ⟨y, hy, hy_le, hyu₁, hyw⟩ := h_irred u₁ w hu₁ hw hu₁w
  obtain ⟨hyx, hy_xw, -, -, hybase⟩ :=
    ladder_center hw hwx hu₁ hu₁x hy hy_le hyu₁ hyw
  have hy_nb : ¬ y ≤ b₀ ⊔ w := by
    intro h
    have h1 : project w y x = b₀ :=
      (ladder_base_iff hw hwx hy hy_xw hyx hyw hb₀ hb₀x).mpr h
    rw [hybase] at h1
    exact hu₁b₀ h1
  have hty : t ≠ y := fun h => hy_nb (h ▸ htb)
  have hy_agree : Submodule.span K {Q.hv y} = Submodule.span K {Q'.hv y} :=
    calibrated_agree_main hw hwx hb₀ hb₀x hw' hw'_le hw'b hw'w
      hQ hQ' hy hy_xw hyx hy_nb
  have hy_shape : ∃ ξ η : K, ξ ≠ 0 ∧
      Q.hv y = Fin.snoc (ξ • P.hv u₁) η := by
    have hm : Q.hv y ∈ Submodule.span K {Q.hv u₁, Q.hv w} :=
      (Q.collinear_iff hu₁ (hu₁x.trans le_sup_left) hw le_sup_right hy hy_xw
        hu₁w).mp hy_le
    rw [pin_span_pair_congr (hQ.base u₁ hu₁ hu₁x) hQ.apex] at hm
    obtain ⟨ξ, η, hs⟩ := pin_shape hm
    refine ⟨ξ, η, ?_, hs⟩
    intro h0
    apply Q.span_inj hw le_sup_right hy hy_xw (Ne.symm hyw)
    rw [hQ.apex, hs, h0, zero_smul]
    exact Submodule.mem_span_singleton.mpr
      ⟨η, by rw [ladder_snoc_smul, smul_zero, mul_one]⟩
  obtain ⟨ξ, η, hξ, hy_vec⟩ := hy_shape
  have hh3_atom : IsAtom (project y t x) :=
    ladder_trace_atom hw hwx hy hy_xw ht ht_le htx hty
  have hh3_x : project y t x ≤ x := inf_le_right
  have ht_h3 : t ≤ project y t x ⊔ y :=
    (ladder_regen hw hwx hy hy_xw hyx ht ht_le htx hty).2
  have hh3_le : project y t x ≤ b₀ ⊔ u₁ := by
    have h := ladder_shear_le hw hwx hu₁x hy_le ht ht_le htx htw
    rwa [hbase_t] at h
  have hmem3 : P.hv (project y t x) ∈
      Submodule.span K {P.hv u₁, P.hv b₀} :=
    (P.collinear_iff hu₁ hu₁x hb₀ hb₀x hh3_atom hh3_x hu₁b₀).mp
      (by rwa [sup_comm] at hh3_le)
  obtain ⟨ρ', σ', hρσ'⟩ := Submodule.mem_span_pair.mp hmem3
  have hdec : σ' • P.hv b₀ + (ρ' * ξ⁻¹) • (ξ • P.hv u₁)
      = P.hv (project y t x) := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hξ, mul_one, add_comm]
    exact hρσ'
  have hind' : ξ • P.hv u₁ ∉ Submodule.span K {P.hv b₀} := by
    intro h
    apply hu₁_ind
    have h1 := Submodule.smul_mem _ ξ⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hξ, one_smul] at h1
  have hb₀_ne : P.hv b₀ ≠ 0 := P.ne_zero hb₀ hb₀x
  have hb₀w : b₀ ≠ w := fun h => hwx (h ▸ hb₀x)
  have hyh3 : y ≠ project y t x := fun h => hyx (h ▸ hh3_x)
  have key : ∀ (R : PointSys (x ⊔ w) (n+1) K), Calibrated P w b₀ w' R →
      Submodule.span K {R.hv y} = Submodule.span K {Q.hv y} →
      R.hv t ∈ Submodule.span K
        {(Fin.snoc (σ' • P.hv b₀) (-((ρ' * ξ⁻¹) * η)) : Fin (n+1) → K)} := by
    intro R hR hRy
    have m1 : R.hv t ∈ Submodule.span K
        ({Fin.snoc (P.hv b₀) 0, Fin.snoc 0 1} : Set (Fin (n+1) → K)) := by
      have h0 : R.hv t ∈ Submodule.span K {R.hv b₀, R.hv w} :=
        (R.collinear_iff hb₀ (hb₀x.trans le_sup_left) hw le_sup_right
          ht ht_le hb₀w).mp htb
      rwa [pin_span_pair_congr (hR.base b₀ hb₀ hb₀x) hR.apex] at h0
    have m2 : R.hv t ∈ Submodule.span K
        ({Fin.snoc (ξ • P.hv u₁) η,
          Fin.snoc (σ' • P.hv b₀ + (ρ' * ξ⁻¹) • (ξ • P.hv u₁)) 0} :
          Set (Fin (n+1) → K)) := by
      have h0 : R.hv t ∈ Submodule.span K {R.hv y, R.hv (project y t x)} :=
        (R.collinear_iff hy hy_xw hh3_atom (hh3_x.trans le_sup_left)
          ht ht_le hyh3).mp (by rwa [sup_comm] at ht_h3)
      rw [pin_span_pair_congr (hRy.trans (by rw [hy_vec]))
        (hR.base _ hh3_atom hh3_x)] at h0
      rwa [hdec]
    exact pin_meet hb₀_ne hind' m1 m2
  exact pin_eq (Q.ne_zero ht ht_le) (Q'.ne_zero ht ht_le)
    (key Q hQ rfl) (key Q' hQ' hy_agree.symm)

omit [ComplementedLattice L] in
theorem PointSys.calibrated_exists (P : PointSys x n K) (hn : 3 ≤ n)
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (hw : IsAtom w) (hwx : ¬ w ≤ x)
    (hb₀ : IsAtom b₀) (hb₀x : b₀ ≤ x)
    (hw' : IsAtom w') (hw'_le : w' ≤ b₀ ⊔ w) (hw'b : w' ≠ b₀) (hw'w : w' ≠ w) :
    ∃ Q : PointSys (x ⊔ w) (n+1) K,
      Calibrated P w b₀ w' Q ∧
      (∀ p : L, p ≤ x → Q.hv p = Fin.snoc (P.hv p) 0) := by
  obtain ⟨Q₀, hQ₀x, hQ₀w⟩ := P.step hn h_irred hw hwx
  obtain ⟨hw'x, hw'_xw, _, _, _⟩ :=
    ladder_center hw hwx hb₀ hb₀x hw' hw'_le hw'b hw'w
  have hb₀w : b₀ ≠ w := fun h => hwx (h ▸ hb₀x)
  have hm : Q₀.hv w' ∈ Submodule.span K {Q₀.hv b₀, Q₀.hv w} :=
    (Q₀.collinear_iff hb₀ (hb₀x.trans le_sup_left) hw le_sup_right
      hw' hw'_xw hb₀w).mp hw'_le
  rw [hQ₀x b₀ hb₀x, hQ₀w] at hm
  obtain ⟨ζ, η, hshape⟩ := pin_shape hm
  have hζ : ζ ≠ 0 := by
    intro h0
    apply Q₀.span_inj hw le_sup_right hw' hw'_xw (Ne.symm hw'w)
    rw [hQ₀w, hshape, h0, zero_smul]
    exact Submodule.mem_span_singleton.mpr
      ⟨η, by rw [ladder_snoc_smul, smul_zero, mul_one]⟩
  have hη : η ≠ 0 := by
    intro h0
    apply Q₀.span_inj hb₀ (hb₀x.trans le_sup_left) hw' hw'_xw (Ne.symm hw'b)
    rw [hQ₀x b₀ hb₀x, hshape, h0]
    exact Submodule.mem_span_singleton.mpr
      ⟨ζ, by rw [ladder_snoc_smul, mul_zero]⟩
  have hg : η⁻¹ * ζ ≠ 0 := mul_ne_zero (inv_ne_zero hη) hζ
  refine ⟨Q₀.twist (heightEquiv (η⁻¹ * ζ) hg), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp hpx
    show Submodule.span K {heightEquiv (η⁻¹ * ζ) hg (Q₀.hv p)} = _
    rw [hQ₀x p hpx, heightEquiv_snoc, zero_mul]
  · show Submodule.span K {heightEquiv (η⁻¹ * ζ) hg (Q₀.hv w)} = _
    rw [hQ₀w, heightEquiv_snoc, one_mul,
      show (Fin.snoc 0 (η⁻¹ * ζ) : Fin (n+1) → K)
        = (η⁻¹ * ζ) • Fin.snoc 0 1 from by
          rw [ladder_snoc_smul, smul_zero, mul_one],
      ladder_span_singleton_smul hg]
  · show Submodule.span K {heightEquiv (η⁻¹ * ζ) hg (Q₀.hv w')} = _
    rw [hshape, heightEquiv_snoc,
      show η * (η⁻¹ * ζ) = ζ from by
        rw [← mul_assoc, mul_inv_cancel₀ hη, one_mul],
      show (Fin.snoc (ζ • P.hv b₀) ζ : Fin (n+1) → K)
        = ζ • Fin.snoc (P.hv b₀) 1 from by
          rw [ladder_snoc_smul, mul_one],
      ladder_span_singleton_smul hζ]
  · intro p hpx
    show heightEquiv (η⁻¹ * ζ) hg (Q₀.hv p) = _
    rw [hQ₀x p hpx, heightEquiv_snoc, zero_mul]

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem calibrated_last_zero_iff {Q : PointSys (x ⊔ w) (n+1) K}
    (hbase : ∀ p, IsAtom p → p ≤ x →
      Submodule.span K {Q.hv p} = Submodule.span K {Fin.snoc (P.hv p) 0})
    {t : L} (ht : IsAtom t) (ht_le : t ≤ x ⊔ w) :
    t ≤ x ↔ Q.hv t (Fin.last n) = 0 := by
  constructor
  · intro htx
    have hm : Q.hv t ∈ Submodule.span K {(Fin.snoc (P.hv t) 0 : Fin (n+1) → K)} := by
      rw [← hbase t ht htx]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    rw [← ha, ladder_snoc_smul, mul_zero, Fin.snoc_last]
  · intro h
    have hstrip : Q.hv t = Fin.snoc (Q.hv t ∘ Fin.castSucc) 0 := by
      rw [← h]
      exact (ladder_snoc_strip (Q.hv t)).symm
    have hu : Q.hv t ∘ Fin.castSucc ≠ 0 := by
      intro h0
      apply Q.ne_zero ht ht_le
      rw [hstrip, h0, ladder_snoc_zero]
    obtain ⟨p, hp, hpx, hspan⟩ := P.span_surj _ hu
    have h1 : Submodule.span K {Q.hv t} = Submodule.span K {Q.hv p} := by
      rw [hbase p hp hpx, hstrip,
        pin_snoc_zero_span_congr (P.ne_zero hp hpx) hspan]
    by_cases hpt : p = t
    · exact hpt ▸ hpx
    · exfalso
      apply Q.span_inj hp (hpx.trans le_sup_left) ht ht_le hpt
      rw [← h1]
      exact Submodule.mem_span_singleton_self _

end PinSystems

end Foam.Bridges

/-! ## Axiom audit -/

/-- info: 'Foam.Bridges.pin_span_pair_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.pin_span_pair_congr

/-- info: 'Foam.Bridges.pin_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.pin_shape

/-- info: 'Foam.Bridges.pin_meet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.pin_meet

/-- info: 'Foam.Bridges.pin_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.pin_eq

/-- info: 'Foam.Bridges.pin_snoc_zero_span_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.pin_snoc_zero_span_congr

/-- info: 'Foam.Bridges.pin_map_mem_span_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.pin_map_mem_span_singleton

/-- info: 'Foam.Bridges.pin_map_span_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.pin_map_span_singleton

/-- info: 'Foam.Bridges.pin_map_mem_span_pair_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.pin_map_mem_span_pair_iff

/-- info: 'Foam.Bridges.heightEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.heightEquiv

/-- info: 'Foam.Bridges.heightEquiv_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.heightEquiv_snoc

/-- info: 'Foam.Bridges.PointSys.twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.PointSys.twist

/-- info: 'Foam.Bridges.Calibrated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.Calibrated

/-- info: 'Foam.Bridges.calibrated_agree_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.calibrated_agree_main

/-- info: 'Foam.Bridges.calibrated_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.calibrated_agree

/-- info: 'Foam.Bridges.PointSys.calibrated_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.PointSys.calibrated_exists

/-- info: 'Foam.Bridges.calibrated_last_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.calibrated_last_zero_iff
