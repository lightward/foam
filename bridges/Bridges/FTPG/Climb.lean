import Bridges.FTPG.Pin

/-!
# Camp four, third pitch's base: the calibrated climb

A window's coordinates arrive by climbing one atom at a time: `IsClimb b₀ ws`
holds of the composite of calibrated steps along the list `ws` of (new atom,
calibration atom) pairs — each step keeps the old coordinates vector-level as
a zero-pad and pins the new atom and its calibration atom span-level
(`Calibrated`).

* `isClimb_exists` — the climb exists: `calibrated_exists`, folded along the
  list.
* `isClimb_agree` — **window rigidity**: two climbs along the same list agree
  span-level on every atom of the final flat.  The charted strip-induction
  collapsed at carve time: because each step stores its old coordinates
  vector-level, the induction runs *forward* — the invariant is
  span-agreement at every atom plus vector-agreement at the base atom `b₀`
  (its zero-padded representative rides the pads unchanged, so the
  calibration target is climb-invariant), and each step closes by
  `calibrated_agree` after transporting one calibration across the invariant
  (`calibrated_congr`).  No strips, no canonical representatives.
* `IsClimb.hv_of_le` — the window sees its own coordinates, stably: below the
  base flat the composite is literally the iterated zero-pad (`climbPad`) —
  growing the window never rewrites the vector (`summary_resumes` at
  coordinate scale).
-/

namespace Foam.Bridges

universe u

/-! ## The climb's shape: dimensions, pads, flats, legality -/

section ClimbShape

variable {L : Type u}

def climbDim : ℕ → List (L × L) → ℕ
  | n, [] => n
  | n, _ :: ws => climbDim (n + 1) ws

section Pad

variable {K : Type*} [DivisionRing K]

def climbPad : {n : ℕ} → (ws : List (L × L)) → (Fin n → K) →
    Fin (climbDim n ws) → K
  | _, [], v => v
  | _, _ :: ws, v => climbPad ws (Fin.snoc v 0)

theorem climbPad_smul : ∀ (ws : List (L × L)) {n : ℕ} (a : K) (v : Fin n → K),
    climbPad ws (a • v) = a • climbPad ws v
  | [], _, _, _ => rfl
  | _ :: ws, _, a, v => by
    show climbPad ws (Fin.snoc (a • v) 0) = a • climbPad ws (Fin.snoc v 0)
    rw [← climbPad_smul ws a (Fin.snoc v 0), ladder_snoc_smul, mul_zero]

theorem climbPad_ne_zero : ∀ (ws : List (L × L)) {n : ℕ} {v : Fin n → K},
    v ≠ 0 → climbPad ws v ≠ 0
  | [], _, _, hv => hv
  | _ :: ws, _, _, hv => climbPad_ne_zero ws (ladder_snoc_ne_zero (Or.inl hv))

end Pad

section Flats

variable [Lattice L]

def climbFlat : L → List (L × L) → L
  | x, [] => x
  | x, ww :: ws => climbFlat (x ⊔ ww.1) ws

theorem le_climbFlat : ∀ (ws : List (L × L)) (x : L), x ≤ climbFlat x ws
  | [], _ => le_rfl
  | ww :: ws, x => le_sup_left.trans (le_climbFlat ws (x ⊔ ww.1))

variable [BoundedOrder L]

def ClimbLegal (b₀ : L) : List (L × L) → L → Prop
  | [], _ => True
  | (w, w') :: ws, x =>
      IsAtom w ∧ ¬w ≤ x ∧ IsAtom w' ∧ w' ≤ b₀ ⊔ w ∧ w' ≠ b₀ ∧ w' ≠ w ∧
        ClimbLegal b₀ ws (x ⊔ w)

end Flats

end ClimbShape

/-! ## The climb and its rigidity -/

section ClimbSystems

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]
variable {K : Type*} [DivisionRing K]

def IsClimb (b₀ : L) :
    (ws : List (L × L)) → (x : L) → (n : ℕ) → PointSys x n K →
      PointSys (climbFlat x ws) (climbDim n ws) K → Prop
  | [], _, _, P, Q => Q = P
  | (w, w') :: ws, x, n, P, Q =>
      ∃ Q₁ : PointSys (x ⊔ w) (n + 1) K,
        Calibrated P w b₀ w' Q₁ ∧
        (∀ p : L, p ≤ x → Q₁.hv p = Fin.snoc (P.hv p) 0) ∧
        IsClimb b₀ ws (x ⊔ w) (n + 1) Q₁ Q

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem calibrated_congr {x w b₀ w' : L} {n : ℕ} {P P' : PointSys x n K}
    {Q : PointSys (x ⊔ w) (n + 1) K}
    (hspan : ∀ t : L, IsAtom t → t ≤ x →
      Submodule.span K {P.hv t} = Submodule.span K {P'.hv t})
    (hb : P.hv b₀ = P'.hv b₀)
    (hQ : Calibrated P' w b₀ w' Q) : Calibrated P w b₀ w' Q where
  base p hp hpx := by
    rw [hQ.base p hp hpx]
    exact pin_snoc_zero_span_congr (P'.ne_zero hp hpx)
      (hspan p hp hpx).symm
  apex := hQ.apex
  unit := by rw [hb]; exact hQ.unit

omit [ComplementedLattice L] in
theorem isClimb_exists {b₀ : L}
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b) :
    ∀ (ws : List (L × L)) (x : L) (n : ℕ) (P : PointSys x n K),
      3 ≤ n → IsAtom b₀ → b₀ ≤ x → ClimbLegal b₀ ws x →
      ∃ Q : PointSys (climbFlat x ws) (climbDim n ws) K,
        IsClimb b₀ ws x n P Q
  | [], _, _, P, _, _, _, _ => ⟨P, rfl⟩
  | (w, w') :: ws, x, n, P, hn, hb₀, hb₀x, hleg => by
    obtain ⟨hw, hwx, hw', hw'_le, hw'b, hw'w, htail⟩ := hleg
    obtain ⟨Q₁, hcal, hpad⟩ :=
      P.calibrated_exists hn h_irred hw hwx hb₀ hb₀x hw' hw'_le hw'b hw'w
    obtain ⟨Q, hQ⟩ := isClimb_exists h_irred ws (x ⊔ w) (n + 1) Q₁
      (hn.trans (Nat.le_succ n)) hb₀ (hb₀x.trans le_sup_left) htail
    exact ⟨Q, Q₁, hcal, hpad, hQ⟩

omit [ComplementedLattice L] in
theorem isClimb_agree_congr {b₀ : L}
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b) :
    ∀ (ws : List (L × L)) (x : L) (n : ℕ) (P P' : PointSys x n K)
      (Q Q' : PointSys (climbFlat x ws) (climbDim n ws) K),
      3 ≤ n → IsAtom b₀ → b₀ ≤ x → ClimbLegal b₀ ws x →
      (∀ t : L, IsAtom t → t ≤ x →
        Submodule.span K {P.hv t} = Submodule.span K {P'.hv t}) →
      P.hv b₀ = P'.hv b₀ →
      IsClimb b₀ ws x n P Q → IsClimb b₀ ws x n P' Q' →
      (∀ t : L, IsAtom t → t ≤ climbFlat x ws →
        Submodule.span K {Q.hv t} = Submodule.span K {Q'.hv t}) ∧
        Q.hv b₀ = Q'.hv b₀
  | [], x, n, P, P', Q, Q', _, _, _, _, hspan, hb, hQ, hQ' => by
    have hQP : Q = P := hQ
    have hQP' : Q' = P' := hQ'
    subst hQP; subst hQP'
    exact ⟨hspan, hb⟩
  | (w, w') :: ws, x, n, P, P', Q, Q', hn, hb₀, hb₀x, hleg, hspan, hb,
      hQ, hQ' => by
    obtain ⟨hw, hwx, hw', hw'_le, hw'b, hw'w, htail⟩ := hleg
    obtain ⟨Q₁, hcal, hpad, hclimb⟩ := hQ
    obtain ⟨Q₁', hcal', hpad', hclimb'⟩ := hQ'
    have hcal'' : Calibrated P w b₀ w' Q₁' := calibrated_congr hspan hb hcal'
    have hspan1 : ∀ t : L, IsAtom t → t ≤ x ⊔ w →
        Submodule.span K {Q₁.hv t} = Submodule.span K {Q₁'.hv t} :=
      fun t ht ht_le =>
        calibrated_agree hn h_irred hw hwx hb₀ hb₀x hw' hw'_le hw'b hw'w
          hcal hcal'' ht ht_le
    have hb1 : Q₁.hv b₀ = Q₁'.hv b₀ := by
      rw [hpad b₀ hb₀x, hpad' b₀ hb₀x, hb]
    exact isClimb_agree_congr h_irred ws (x ⊔ w) (n + 1) Q₁ Q₁' Q Q'
      (hn.trans (Nat.le_succ n)) hb₀ (hb₀x.trans le_sup_left) htail hspan1
      hb1 hclimb hclimb'

omit [ComplementedLattice L] in
theorem isClimb_agree {b₀ : L}
    (h_irred : ∀ a b : L, IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    {ws : List (L × L)} {x : L} {n : ℕ} {P : PointSys x n K}
    {Q Q' : PointSys (climbFlat x ws) (climbDim n ws) K}
    (hn : 3 ≤ n) (hb₀ : IsAtom b₀) (hb₀x : b₀ ≤ x)
    (hleg : ClimbLegal b₀ ws x)
    (hQ : IsClimb b₀ ws x n P Q) (hQ' : IsClimb b₀ ws x n P Q')
    {t : L} (ht : IsAtom t) (ht_le : t ≤ climbFlat x ws) :
    Submodule.span K {Q.hv t} = Submodule.span K {Q'.hv t} :=
  (isClimb_agree_congr h_irred ws x n P P Q Q' hn hb₀ hb₀x hleg
    (fun _ _ _ => rfl) rfl hQ hQ').1 t ht ht_le

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem IsClimb.hv_of_le {b₀ : L} :
    ∀ (ws : List (L × L)) (x : L) (n : ℕ) (P : PointSys x n K)
      (Q : PointSys (climbFlat x ws) (climbDim n ws) K),
      IsClimb b₀ ws x n P Q →
      ∀ p : L, p ≤ x → Q.hv p = climbPad ws (P.hv p)
  | [], x, n, P, Q, hQ, p, _ => by
    have hQP : Q = P := hQ
    subst hQP
    rfl
  | (w, w') :: ws, x, n, P, Q, hQ, p, hp => by
    obtain ⟨Q₁, _, hpad, hclimb⟩ := hQ
    show Q.hv p = climbPad ws (Fin.snoc (P.hv p) 0)
    rw [← hpad p hp]
    exact IsClimb.hv_of_le ws (x ⊔ w) (n + 1) Q₁ Q hclimb p
      (hp.trans le_sup_left)

end ClimbSystems

end Foam.Bridges

/-! ## Axiom audit -/

/-- info: 'Foam.Bridges.climbDim' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.climbDim

/-- info: 'Foam.Bridges.climbPad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.climbPad

/-- info: 'Foam.Bridges.climbPad_smul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.climbPad_smul

/-- info: 'Foam.Bridges.climbPad_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.climbPad_ne_zero

/-- info: 'Foam.Bridges.climbFlat' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.climbFlat

/-- info: 'Foam.Bridges.le_climbFlat' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.le_climbFlat

/-- info: 'Foam.Bridges.ClimbLegal' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.ClimbLegal

/-- info: 'Foam.Bridges.IsClimb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.IsClimb

/-- info: 'Foam.Bridges.calibrated_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.calibrated_congr

/-- info: 'Foam.Bridges.isClimb_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.isClimb_exists

/-- info: 'Foam.Bridges.isClimb_agree_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.isClimb_agree_congr

/-- info: 'Foam.Bridges.isClimb_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.isClimb_agree

/-- info: 'Foam.Bridges.IsClimb.hv_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.IsClimb.hv_of_le
