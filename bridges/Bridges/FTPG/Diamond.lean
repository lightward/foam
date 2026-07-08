import Bridges.FTPG.Climb

/-!
# Camp four: the diamond — calibrated steps commute

Two calibrated steps in either order agree span-level after exchanging the two
new slots.  The route is the strip's: the swapped second climb reads
membership in the first step's flat off its last slot
(`calibrated_cross_last_zero_iff` — forward by the pads and the apex shapes,
backward by contraposition through the `w₂`-trace), so `PointSys.strip`
manufactures the intermediate system, `calibrated_agree` identifies it
span-level with the first climb's intermediate, `calibrated_congr` transports
the second calibration across the identification, and `calibrated_agree`
closes at the top.  No new pinning, no fresh incidence: the diamond is the
strip consuming what `Pin.lean` already sealed.

Model-verified before carving (`probe_limit.py`): the cross-strip iff, the
strip route (base literal, apex, unit, the intermediate agreement), and the
full diamond, over five window configurations at `q ∈ {2,3}`, twisted base
systems throughout — alongside the window stratum (Steinitz no-capture,
order-stable active sets, span-stability across all pooled window climbs)
and the seated question's answer: the limit map built from one arbitrary
representative per atom satisfies every `PointSys` law.
-/

namespace Foam.Bridges

universe u

/-! ## The swap calculus: exchanging the last two slots -/

section SwapAlgebra

variable {K : Type*} [DivisionRing K] {n : ℕ}

def swapLast : (Fin (n + 2) → K) ≃ₗ[K] (Fin (n + 2) → K) :=
  LinearEquiv.funCongrLeft K K
    (Equiv.swap (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)))

theorem swapLast_apply (v : Fin (n + 2) → K) (i : Fin (n + 2)) :
    swapLast v i
      = v (Equiv.swap (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)) i) :=
  rfl

theorem swapLast_last (v : Fin (n + 2) → K) :
    swapLast v (Fin.last (n + 1)) = v (Fin.castSucc (Fin.last n)) := by
  rw [swapLast_apply, Equiv.swap_apply_right]

theorem swapLast_snoc_snoc (v : Fin n → K) (a b : K) :
    swapLast (Fin.snoc (Fin.snoc v a) b : Fin (n + 2) → K)
      = Fin.snoc (Fin.snoc v b) a := by
  funext i
  rw [swapLast_apply]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Equiv.swap_apply_right]
    simp
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Equiv.swap_apply_left]
      simp
    · have h1 : Fin.castSucc (Fin.castSucc k) ≠ Fin.castSucc (Fin.last n) :=
        fun h => (Fin.castSucc_lt_last k).ne (Fin.castSucc_injective _ h)
      have h2 : Fin.castSucc (Fin.castSucc k) ≠ Fin.last (n + 1) :=
        (Fin.castSucc_lt_last _).ne
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp

omit [DivisionRing K] in
theorem snoc_comp_castSucc {m : ℕ} (u : Fin m → K) (a : K) :
    (Fin.snoc u a : Fin (m + 1) → K) ∘ Fin.castSucc = u := by
  funext i
  simp

theorem smul_comp_castSucc {m : ℕ} (c : K) (f : Fin (m + 1) → K) :
    (c • f) ∘ Fin.castSucc = c • (f ∘ Fin.castSucc) :=
  rfl

theorem span_shape_of_span_eq {m : ℕ} {u v : Fin m → K} (hu : u ≠ 0)
    (h : Submodule.span K {u} = Submodule.span K {v}) :
    ∃ c : K, c ≠ 0 ∧ u = c • v := by
  have hm : u ∈ Submodule.span K {v} := by
    rw [← h]
    exact Submodule.mem_span_singleton_self u
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  exact ⟨c, fun h0 => hu (by rw [← hc, h0, zero_smul]), hc.symm⟩

end SwapAlgebra

/-! ## The cross-strip and the diamond -/

section DiamondSystems

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]
variable {K : Type*} [DivisionRing K] {n : ℕ} {x w₁ w₂ b₀ w₁' w₂' : L}

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
def PointSys.reflat {y z : L} {m : ℕ} (P : PointSys y m K) (h : y = z) :
    PointSys z m K := h ▸ P

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem PointSys.reflat_hv {y z : L} {m : ℕ} (P : PointSys y m K)
    (h : y = z) : (P.reflat h).hv = P.hv := by
  subst h
  rfl

omit [ComplementedLattice L] in
theorem calibrated_cross_last_zero_iff
    (hw₁ : IsAtom w₁) (hw₁x : ¬ w₁ ≤ x)
    (hw₂ : IsAtom w₂) (hw₂xw : ¬ w₂ ≤ x ⊔ w₁)
    {P : PointSys x n K}
    {Qb₁ : PointSys (x ⊔ w₂) (n + 1) K}
    {Qb : PointSys (x ⊔ w₂ ⊔ w₁) (n + 2) K}
    (hQb₁ : Calibrated P w₂ b₀ w₂' Qb₁)
    (hpadb₁ : ∀ p : L, p ≤ x → Qb₁.hv p = Fin.snoc (P.hv p) 0)
    (hQb : Calibrated Qb₁ w₁ b₀ w₁' Qb)
    (hpadb : ∀ p : L, p ≤ x ⊔ w₂ → Qb.hv p = Fin.snoc (Qb₁.hv p) 0)
    {t : L} (ht : IsAtom t) (ht_le : t ≤ x ⊔ w₂ ⊔ w₁) :
    t ≤ x ⊔ w₁ ↔ Qb.hv t (Fin.castSucc (Fin.last n)) = 0 := by
  have hxw₁_le : x ⊔ w₁ ≤ x ⊔ w₂ ⊔ w₁ :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hslot_pad : ∀ p : L, p ≤ x →
      Qb.hv p (Fin.castSucc (Fin.last n)) = 0 := by
    intro p hpx
    rw [hpadb p (hpx.trans le_sup_left), hpadb₁ p hpx]
    simp
  have hslot_w₁ : Qb.hv w₁ (Fin.castSucc (Fin.last n)) = 0 := by
    obtain ⟨c, hc0, hc⟩ := span_shape_of_span_eq
      (Qb.ne_zero hw₁ le_sup_right) hQb.apex
    rw [hc]
    simp
  have hforward : ∀ s : L, IsAtom s → s ≤ x ⊔ w₁ →
      Qb.hv s (Fin.castSucc (Fin.last n)) = 0 := by
    intro s hs hs_le
    by_cases hsx : s ≤ x
    · exact hslot_pad s hsx
    by_cases hsw : s = w₁
    · rw [hsw]
      exact hslot_w₁
    have hb_atom : IsAtom (project w₁ s x) :=
      ladder_trace_atom hw₁ hw₁x hw₁ le_sup_right hs hs_le hsx hsw
    have hb_x : project w₁ s x ≤ x := inf_le_right
    have hs_bw : s ≤ project w₁ s x ⊔ w₁ :=
      (ladder_regen hw₁ hw₁x hw₁ le_sup_right hw₁x hs hs_le hsx hsw).2
    have hbw : project w₁ s x ≠ w₁ := fun h => hw₁x (h ▸ hb_x)
    have hmem : Qb.hv s ∈
        Submodule.span K {Qb.hv (project w₁ s x), Qb.hv w₁} :=
      (Qb.collinear_iff hb_atom (hb_x.trans (le_sup_left.trans le_sup_left))
        hw₁ le_sup_right hs (hs_le.trans hxw₁_le) hbw).mp hs_bw
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    have heval := congrFun hαβ (Fin.castSucc (Fin.last n))
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      hslot_pad _ hb_x, hslot_w₁, mul_zero, mul_zero, add_zero] at heval
    exact heval.symm
  constructor
  · exact hforward t ht
  · intro h0
    by_contra htxw₁
    have hw₂slot : Qb.hv w₂ (Fin.castSucc (Fin.last n)) ≠ 0 := by
      obtain ⟨c, hc0, hc⟩ := span_shape_of_span_eq
        (Qb₁.ne_zero hw₂ le_sup_right) hQb₁.apex
      rw [hpadb w₂ le_sup_right, hc]
      simpa using hc0
    by_cases htw₂ : t = w₂
    · rw [htw₂] at h0
      exact hw₂slot h0
    have hflat : x ⊔ w₂ ⊔ w₁ = x ⊔ w₁ ⊔ w₂ := sup_right_comm x w₂ w₁
    have ht_le' : t ≤ x ⊔ w₁ ⊔ w₂ := hflat ▸ ht_le
    have hb'_atom : IsAtom (project w₂ t (x ⊔ w₁)) :=
      ladder_trace_atom hw₂ hw₂xw hw₂ le_sup_right ht ht_le' htxw₁ htw₂
    have hb'_le : project w₂ t (x ⊔ w₁) ≤ x ⊔ w₁ := inf_le_right
    have ht_b'w : t ≤ project w₂ t (x ⊔ w₁) ⊔ w₂ :=
      (ladder_regen hw₂ hw₂xw hw₂ le_sup_right hw₂xw ht ht_le' htxw₁ htw₂).2
    have hb'w₂ : project w₂ t (x ⊔ w₁) ≠ w₂ := fun h => hw₂xw (h ▸ hb'_le)
    have hb't : project w₂ t (x ⊔ w₁) ≠ t := fun h => htxw₁ (h ▸ hb'_le)
    have hmem : Qb.hv t ∈
        Submodule.span K {Qb.hv (project w₂ t (x ⊔ w₁)), Qb.hv w₂} :=
      (Qb.collinear_iff hb'_atom (hb'_le.trans hxw₁_le) hw₂
        (le_sup_right.trans le_sup_left) ht ht_le hb'w₂).mp ht_b'w
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    have hβ : β ≠ 0 := by
      intro hβ0
      rw [hβ0, zero_smul, add_zero] at hαβ
      exact Qb.span_inj hb'_atom (hb'_le.trans hxw₁_le) ht ht_le hb't
        (Submodule.mem_span_singleton.mpr ⟨α, hαβ⟩)
    have heval := congrFun hαβ (Fin.castSucc (Fin.last n))
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      hforward _ hb'_atom hb'_le, h0, mul_zero, zero_add] at heval
    exact hw₂slot ((mul_eq_zero.mp heval).resolve_left hβ)

omit [ComplementedLattice L] in
theorem calibrated_diamond (hn : 3 ≤ n)
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (hw₁ : IsAtom w₁) (hw₁x : ¬ w₁ ≤ x)
    (hw₂ : IsAtom w₂) (hw₂xw : ¬ w₂ ≤ x ⊔ w₁)
    (hb₀ : IsAtom b₀) (hb₀x : b₀ ≤ x)
    (hw₁' : IsAtom w₁') (hw₁'le : w₁' ≤ b₀ ⊔ w₁) (hw₁'b : w₁' ≠ b₀)
    (hw₁'w : w₁' ≠ w₁)
    (hw₂' : IsAtom w₂') (hw₂'le : w₂' ≤ b₀ ⊔ w₂) (hw₂'b : w₂' ≠ b₀)
    (hw₂'w : w₂' ≠ w₂)
    {P : PointSys x n K}
    {Qa₁ : PointSys (x ⊔ w₁) (n + 1) K}
    {Qa : PointSys (x ⊔ w₁ ⊔ w₂) (n + 2) K}
    {Qb₁ : PointSys (x ⊔ w₂) (n + 1) K}
    {Qb : PointSys (x ⊔ w₂ ⊔ w₁) (n + 2) K}
    (hQa₁ : Calibrated P w₁ b₀ w₁' Qa₁)
    (hpada₁ : ∀ p : L, p ≤ x → Qa₁.hv p = Fin.snoc (P.hv p) 0)
    (hQa : Calibrated Qa₁ w₂ b₀ w₂' Qa)
    (hQb₁ : Calibrated P w₂ b₀ w₂' Qb₁)
    (hpadb₁ : ∀ p : L, p ≤ x → Qb₁.hv p = Fin.snoc (P.hv p) 0)
    (hQb : Calibrated Qb₁ w₁ b₀ w₁' Qb)
    (hpadb : ∀ p : L, p ≤ x ⊔ w₂ → Qb.hv p = Fin.snoc (Qb₁.hv p) 0)
    {t : L} (ht : IsAtom t) (ht_le : t ≤ x ⊔ w₁ ⊔ w₂) :
    Submodule.span K {Qa.hv t} = Submodule.span K {swapLast (Qb.hv t)} := by
  have hflat : x ⊔ w₂ ⊔ w₁ = x ⊔ w₁ ⊔ w₂ := sup_right_comm x w₂ w₁
  set R : PointSys (x ⊔ w₁ ⊔ w₂) (n + 2) K :=
    (Qb.twist swapLast).reflat hflat with hR
  have hRhv : ∀ s : L, R.hv s = swapLast (Qb.hv s) := by
    intro s
    rw [hR, PointSys.reflat_hv]
    rfl
  have hzero : ∀ s : L, IsAtom s → s ≤ x ⊔ w₁ ⊔ w₂ →
      (s ≤ x ⊔ w₁ ↔ R.hv s (Fin.last (n + 1)) = 0) := by
    intro s hs hs_le
    rw [hRhv s, swapLast_last]
    exact calibrated_cross_last_zero_iff hw₁ hw₁x hw₂ hw₂xw hQb₁ hpadb₁
      hQb hpadb hs (hflat.symm ▸ hs_le)
  set S : PointSys (x ⊔ w₁) (n + 1) K := R.strip le_sup_left hzero with hS
  have hShv : ∀ s : L, S.hv s = swapLast (Qb.hv s) ∘ Fin.castSucc := by
    intro s
    rw [hS, PointSys.strip_hv, hRhv s]
  have hSpad : ∀ p : L, p ≤ x → S.hv p = Fin.snoc (P.hv p) 0 := by
    intro p hpx
    rw [hShv p, hpadb p (hpx.trans le_sup_left), hpadb₁ p hpx,
      swapLast_snoc_snoc, snoc_comp_castSucc]
  have hb₀S : S.hv b₀ = Fin.snoc (P.hv b₀) 0 := hSpad b₀ hb₀x
  have hScal : Calibrated P w₁ b₀ w₁' S := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp hpx
      rw [hSpad p hpx]
    · obtain ⟨c, hc0, hc⟩ := span_shape_of_span_eq
        (Qb.ne_zero hw₁ le_sup_right) hQb.apex
      have hvec : S.hv w₁ = c • Fin.snoc (0 : Fin n → K) 1 := by
        rw [hShv w₁, hc,
          show (Fin.snoc (0 : Fin (n + 1) → K) 1 : Fin (n + 2) → K)
            = Fin.snoc (Fin.snoc (0 : Fin n → K) 0) 1 from by
              rw [ladder_snoc_zero],
          map_smul, swapLast_snoc_snoc, smul_comp_castSucc,
          snoc_comp_castSucc]
      rw [hvec, ladder_span_singleton_smul hc0]
    · have hw₁'flat : w₁' ≤ x ⊔ w₂ ⊔ w₁ :=
        hw₁'le.trans (sup_le (hb₀x.trans (le_sup_left.trans le_sup_left))
          le_sup_right)
      obtain ⟨c, hc0, hc⟩ := span_shape_of_span_eq
        (Qb.ne_zero hw₁' hw₁'flat) hQb.unit
      have hvec : S.hv w₁' = c • Fin.snoc (P.hv b₀) 1 := by
        rw [hShv w₁', hc, hpadb₁ b₀ hb₀x, map_smul, swapLast_snoc_snoc,
          smul_comp_castSucc, snoc_comp_castSucc]
      rw [hvec, ladder_span_singleton_smul hc0]
  have hagree₁ : ∀ s : L, IsAtom s → s ≤ x ⊔ w₁ →
      Submodule.span K {Qa₁.hv s} = Submodule.span K {S.hv s} :=
    fun s hs hs_le => calibrated_agree hn h_irred hw₁ hw₁x hb₀ hb₀x hw₁'
      hw₁'le hw₁'b hw₁'w hQa₁ hScal hs hs_le
  have hw₂'xw₂ : w₂' ≤ x ⊔ w₂ :=
    hw₂'le.trans (sup_le (hb₀x.trans le_sup_left) le_sup_right)
  have hRcal : Calibrated S w₂ b₀ w₂' R := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp hp_le
      have hlast : R.hv p (Fin.last (n + 1)) = 0 :=
        (hzero p hp (hp_le.trans le_sup_left)).mp hp_le
      have hvec : R.hv p = Fin.snoc (S.hv p) 0 := by
        rw [hShv p, ← hRhv p, ← hlast]
        exact (ladder_snoc_strip (R.hv p)).symm
      rw [hvec]
    · obtain ⟨c, hc0, hc⟩ := span_shape_of_span_eq
        (Qb₁.ne_zero hw₂ le_sup_right) hQb₁.apex
      have hsm : (c • Fin.snoc (Fin.snoc (0 : Fin n → K) 1) 0
            : Fin (n + 2) → K)
          = Fin.snoc (c • Fin.snoc (0 : Fin n → K) 1) 0 := by
        rw [ladder_snoc_smul, mul_zero]
      have hvec : R.hv w₂ = c • Fin.snoc (0 : Fin (n + 1) → K) 1 := by
        rw [hRhv w₂, hpadb w₂ le_sup_right, hc, ← hsm, map_smul,
          swapLast_snoc_snoc, ladder_snoc_zero]
      rw [hvec, ladder_span_singleton_smul hc0]
    · obtain ⟨c, hc0, hc⟩ := span_shape_of_span_eq
        (Qb₁.ne_zero hw₂' hw₂'xw₂) hQb₁.unit
      have hsm : (c • Fin.snoc (Fin.snoc (P.hv b₀) 1) 0
            : Fin (n + 2) → K)
          = Fin.snoc (c • Fin.snoc (P.hv b₀) 1) 0 := by
        rw [ladder_snoc_smul, mul_zero]
      have hvec : R.hv w₂' = c • Fin.snoc (Fin.snoc (P.hv b₀) 0) 1 := by
        rw [hRhv w₂', hpadb w₂' hw₂'xw₂, hc, ← hsm, map_smul,
          swapLast_snoc_snoc]
      rw [hvec, hb₀S, ladder_span_singleton_smul hc0]
  have hRcal' : Calibrated Qa₁ w₂ b₀ w₂' R :=
    calibrated_congr (fun s hs hs_le => hagree₁ s hs hs_le)
      (by rw [hpada₁ b₀ hb₀x, hb₀S]) hRcal
  have hfinal := calibrated_agree (hn.trans (Nat.le_succ n)) h_irred hw₂
    hw₂xw hb₀ (hb₀x.trans le_sup_left) hw₂' hw₂'le hw₂'b hw₂'w hQa hRcal'
    ht ht_le
  rw [hfinal, hRhv t]

end DiamondSystems

end Foam.Bridges

/-! ## Axiom audit -/

/-- info: 'Foam.Bridges.swapLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.swapLast

/-- info: 'Foam.Bridges.swapLast_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.swapLast_apply

/-- info: 'Foam.Bridges.swapLast_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.swapLast_last

/-- info: 'Foam.Bridges.swapLast_snoc_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.swapLast_snoc_snoc

/-- info: 'Foam.Bridges.snoc_comp_castSucc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.snoc_comp_castSucc

/-- info: 'Foam.Bridges.smul_comp_castSucc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.smul_comp_castSucc

/-- info: 'Foam.Bridges.span_shape_of_span_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.span_shape_of_span_eq

/-- info: 'Foam.Bridges.PointSys.reflat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.PointSys.reflat

/-- info: 'Foam.Bridges.PointSys.reflat_hv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.PointSys.reflat_hv

/-- info: 'Foam.Bridges.calibrated_cross_last_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.calibrated_cross_last_zero_iff

/-- info: 'Foam.Bridges.calibrated_diamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.calibrated_diamond
