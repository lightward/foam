import Bridges.FTPG.Ycoord
import Bridges.FTPG.CoordinateAlgebra

/-!
# The space chart — camp three of the `pointSystem_exists` ascent, third pitch

The first out-of-plane step of the Veblen–Young induction.  A fourth frame
point `R` off the plane `π = O ⊔ U ⊔ V` (the frame already carries one)
spans the 3-space `τ = π ⊔ R`, whose plane at infinity is `σ = m ⊔ R` (the
horizontal directions plus the new vertical) and whose third axis is
`ζ = O ⊔ R`.  A *space-affine* atom — below `τ`, off `σ` — projects twice:

* `baseproj R p = (p ⊔ R) ⊓ π` — the drop through `R` onto the
  coordinatized plane (a plane-affine atom);
* `zproj R p = (p ⊔ m) ⊓ ζ` — the drop along the horizontal directions
  onto the z-axis (an atom of `ζ` other than `R`);
* `spoint R q z = (q ⊔ R) ⊓ (z ⊔ m)` — the chart read backwards.

The recovery is one modular move after the two line identities
(`space_recovers`), each projection inverts the other (`baseproj_spoint`,
`zproj_spoint`), and the affine 3-space splits losslessly:
`spaceChart : SpaceAffine Γ R ≃ Affine Γ × Applicate Γ R`.  The z-axis
then transports onto the coordinate line by ONE standing perspectivity —
center any third atom `c` on `U ⊔ R` (`h_irred` supplies it), the
coplanarity `ζ ⊔ c = l ⊔ c` definitional in the plane `O ⊔ U ⊔ R` —
`applicateTransport : Applicate Γ R ≃ Coordinate Γ`, calibrated at both
ends (`zcoord_O`, `zcoord_R`), so `solidChart`: the affine 3-space is `D³`
at atom level.  No fresh Desargues, no new incidence — one general lemma
(`line_meets_hyperplane`, the height-4 sibling of `project_is_atom`) plus
covBy bookkeeping; the plane points sit at height zero of the new axis
(`zproj_of_affine_π`), so the plane chart embeds without recalibration.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

omit [ComplementedLattice L] in
theorem line_meets_hyperplane {x t p c : L}
    (h_cov : x ⋖ t) (hp : IsAtom p) (hc : IsAtom c) (hpc : p ≠ c)
    (h_le : p ⊔ c ≤ t) (h_not : ¬ p ⊔ c ≤ x) :
    IsAtom ((p ⊔ c) ⊓ x) := by
  have h_lt : x < x ⊔ (p ⊔ c) := lt_of_le_of_ne le_sup_left
    (fun h => h_not (h ▸ le_sup_right))
  have h_join : x ⊔ (p ⊔ c) = t :=
    (h_cov.eq_or_eq h_lt.le (sup_le h_cov.le h_le)).resolve_left (ne_of_gt h_lt)
  have h_cov' : x ⋖ x ⊔ (p ⊔ c) := by rw [h_join]; exact h_cov
  have h_inf_cov : x ⊓ (p ⊔ c) ⋖ p ⊔ c :=
    IsLowerModularLattice.inf_covBy_of_covBy_sup h_cov'
  have h_p_lt : p < p ⊔ c := lt_of_le_of_ne le_sup_left
    (fun h => hpc (IsAtom.eq_of_le hc hp (h ▸ le_sup_right)).symm)
  have h_ne_bot : (p ⊔ c) ⊓ x ≠ ⊥ := by
    intro h
    rw [inf_comm] at h
    rw [h] at h_inf_cov
    exact h_inf_cov.2 hp.bot_lt h_p_lt
  exact line_height_two hp hc hpc (bot_lt_iff_ne_bot.mpr h_ne_bot)
    (lt_of_le_of_ne inf_le_left (fun h => h_not (h ▸ inf_le_right)))

variable {Γ : CoordSystem L} {R : L}

theorem CoordSystem.ne_R_of_le_π (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    {p : L} (hp_π : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) : p ≠ R :=
  fun h => hR_π (h ▸ hp_π)

theorem CoordSystem.hU_ne_R (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) : Γ.U ≠ R :=
  CoordSystem.ne_R_of_le_π hR_π (le_sup_right.trans le_sup_left)

theorem CoordSystem.hR_not_m (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    ¬ R ≤ Γ.U ⊔ Γ.V :=
  fun h => hR_π (h.trans Γ.m_le_π)

theorem CoordSystem.R_inf_π (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    R ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = ⊥ :=
  (hR.le_iff.mp inf_le_left).resolve_right (fun h => hR_π (h ▸ inf_le_right))

theorem CoordSystem.π_covBy_τ (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    Γ.O ⊔ Γ.U ⊔ Γ.V ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R := by
  have h := covBy_sup_of_inf_covBy_left
    (CoordSystem.R_inf_π hR hR_π ▸ hR.bot_covBy)
  rwa [sup_comm R (Γ.O ⊔ Γ.U ⊔ Γ.V)] at h

theorem CoordSystem.σ_inf_π (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.U ⊔ Γ.V ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = Γ.U ⊔ Γ.V := by
  rw [sup_inf_assoc_of_le R Γ.m_le_π, CoordSystem.R_inf_π hR hR_π, sup_bot_eq]

theorem CoordSystem.hO_not_σ (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    ¬ Γ.O ≤ Γ.U ⊔ Γ.V ⊔ R := fun h =>
  Γ.hO_not_m (le_of_le_of_eq (le_inf h (le_sup_left.trans le_sup_left))
    (CoordSystem.σ_inf_π hR hR_π))

theorem CoordSystem.O_inf_σ (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    Γ.O ⊓ (Γ.U ⊔ Γ.V ⊔ R) = ⊥ :=
  (Γ.hO.le_iff.mp inf_le_left).resolve_right
    (fun h => CoordSystem.hO_not_σ hR hR_π (h ▸ inf_le_right))

theorem CoordSystem.σ_covBy_τ (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    Γ.U ⊔ Γ.V ⊔ R ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R := by
  have h := covBy_sup_of_inf_covBy_left
    (CoordSystem.O_inf_σ hR hR_π ▸ Γ.hO.bot_covBy)
  rwa [← sup_assoc, ← sup_assoc] at h

theorem CoordSystem.ζ_inf_π (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.O ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = Γ.O := by
  rw [sup_inf_assoc_of_le R (le_sup_left.trans le_sup_left : Γ.O ≤ _),
    CoordSystem.R_inf_π hR hR_π, sup_bot_eq]

theorem CoordSystem.hU_not_ζ (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    ¬ Γ.U ≤ Γ.O ⊔ R := fun h =>
  Γ.hOU (IsAtom.eq_of_le Γ.hU Γ.hO (le_of_le_of_eq
    (le_inf h (le_sup_right.trans le_sup_left)) (CoordSystem.ζ_inf_π hR hR_π))).symm

theorem CoordSystem.ζ_inf_σ (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.O ⊔ R) ⊓ (Γ.U ⊔ Γ.V ⊔ R) = R := by
  rw [sup_comm Γ.O R, sup_inf_assoc_of_le Γ.O (le_sup_right : R ≤ Γ.U ⊔ Γ.V ⊔ R),
    CoordSystem.O_inf_σ hR hR_π, sup_bot_eq]

/-! ## The two projections and the recovery -/

def CoordSystem.baseproj (Γ : CoordSystem L) (R p : L) : L :=
  (p ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V)

def CoordSystem.zproj (Γ : CoordSystem L) (R p : L) : L :=
  (p ⊔ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ R)

def CoordSystem.spoint (Γ : CoordSystem L) (R q z : L) : L :=
  (q ⊔ R) ⊓ (z ⊔ (Γ.U ⊔ Γ.V))

theorem CoordSystem.ne_R_of_off_σ {p : L} (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    p ≠ R :=
  fun h => hp_σ (h.le.trans le_sup_right)

theorem CoordSystem.not_m_of_off_σ {p : L} (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    ¬ p ≤ Γ.U ⊔ Γ.V :=
  fun h => hp_σ (h.trans le_sup_left)

theorem CoordSystem.m_covBy_sup {x : L} (hx : IsAtom x)
    (hx_m : ¬ x ≤ Γ.U ⊔ Γ.V) :
    Γ.U ⊔ Γ.V ⋖ x ⊔ (Γ.U ⊔ Γ.V) := by
  have h_meet : x ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
    (hx.le_iff.mp inf_le_left).resolve_right (fun h => hx_m (h ▸ inf_le_right))
  exact covBy_sup_of_inf_covBy_left (h_meet ▸ hx.bot_covBy)

theorem CoordSystem.hR_not_sup_m
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p : L}
    (hp : IsAtom p) (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    ¬ R ≤ p ⊔ (Γ.U ⊔ Γ.V) := by
  intro h
  have h_cov := CoordSystem.m_covBy_sup hp (CoordSystem.not_m_of_off_σ hp_σ)
  have hσ_le : Γ.U ⊔ Γ.V ⊔ R ≤ p ⊔ (Γ.U ⊔ Γ.V) := sup_le le_sup_right h
  rcases h_cov.eq_or_eq le_sup_left hσ_le with h' | h'
  · exact CoordSystem.hR_not_m hR_π (h' ▸ (le_sup_right : R ≤ Γ.U ⊔ Γ.V ⊔ R))
  · exact hp_σ (h'.symm ▸ (le_sup_left : p ≤ p ⊔ (Γ.U ⊔ Γ.V)))

theorem CoordSystem.sup_m_covBy_τ (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p : L} (hp : IsAtom p)
    (hp_τ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    p ⊔ (Γ.U ⊔ Γ.V) ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R := by
  have hRnot := CoordSystem.hR_not_sup_m hR_π hp hp_σ
  have h_meet : R ⊓ (p ⊔ (Γ.U ⊔ Γ.V)) = ⊥ :=
    (hR.le_iff.mp inf_le_left).resolve_right (fun h => hRnot (h ▸ inf_le_right))
  have h_cov := covBy_sup_of_inf_covBy_left (h_meet ▸ hR.bot_covBy)
  have h_eq : R ⊔ (p ⊔ (Γ.U ⊔ Γ.V)) = Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R := by
    apply le_antisymm
    · exact sup_le le_sup_right (sup_le hp_τ (Γ.m_le_π.trans le_sup_left))
    · have h_lt : Γ.U ⊔ Γ.V ⊔ R < (Γ.U ⊔ Γ.V ⊔ R) ⊔ p := lt_of_le_of_ne
        le_sup_left (fun h => hp_σ (h.symm ▸ (le_sup_right : p ≤ _)))
      have h_top : (Γ.U ⊔ Γ.V ⊔ R) ⊔ p = Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
        ((CoordSystem.σ_covBy_τ hR hR_π).eq_or_eq h_lt.le
          (sup_le (CoordSystem.σ_covBy_τ hR hR_π).le hp_τ)).resolve_left
          (ne_of_gt h_lt)
      rw [← h_top]
      exact sup_le (sup_le (le_sup_right.trans le_sup_right) le_sup_left)
        (le_sup_left.trans le_sup_right)
  rwa [h_eq] at h_cov

theorem CoordSystem.baseproj_is_atom (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p : L} (hp : IsAtom p)
    (hp_τ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    IsAtom (Γ.baseproj R p) :=
  line_meets_hyperplane (CoordSystem.π_covBy_τ hR hR_π) hp hR
    (CoordSystem.ne_R_of_off_σ hp_σ) (sup_le hp_τ le_sup_right)
    (fun h => hR_π (le_sup_right.trans h))

theorem CoordSystem.baseproj_le_π (Γ : CoordSystem L) (R p : L) :
    Γ.baseproj R p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
  inf_le_right

theorem CoordSystem.baseproj_of_le_π (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {q : L} (hq_π : q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    Γ.baseproj R q = q := by
  show (q ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = q
  rw [sup_inf_assoc_of_le R hq_π, CoordSystem.R_inf_π hR hR_π, sup_bot_eq]

theorem CoordSystem.sup_R_baseproj (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p : L} (hp : IsAtom p)
    (hp_τ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    p ⊔ R = Γ.baseproj R p ⊔ R := by
  have hb_atom := CoordSystem.baseproj_is_atom hR hR_π hp hp_τ hp_σ
  have h := line_eq_of_atom_le' hR hp hb_atom
    (CoordSystem.ne_R_of_off_σ hp_σ).symm
    (fun h' => hR_π (h'.trans_le (Γ.baseproj_le_π R p)))
    (le_of_le_of_eq (inf_le_left : Γ.baseproj R p ≤ p ⊔ R) (sup_comm p R))
  rw [sup_comm p R, sup_comm (Γ.baseproj R p) R]
  exact h

theorem CoordSystem.baseproj_affine (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p : L} (hp : IsAtom p)
    (hp_τ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    ¬ Γ.baseproj R p ≤ Γ.U ⊔ Γ.V := by
  intro h
  apply hp_σ
  calc p ≤ p ⊔ R := le_sup_left
    _ = Γ.baseproj R p ⊔ R := CoordSystem.sup_R_baseproj hR hR_π hp hp_τ hp_σ
    _ ≤ Γ.U ⊔ Γ.V ⊔ R := sup_le (h.trans le_sup_left) le_sup_right

theorem CoordSystem.zproj_le_ζ (Γ : CoordSystem L) (R p : L) :
    Γ.zproj R p ≤ Γ.O ⊔ R :=
  inf_le_right

theorem CoordSystem.zproj_is_atom (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p : L} (hp : IsAtom p)
    (hp_τ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    IsAtom (Γ.zproj R p) := by
  have h := line_meets_hyperplane
    (CoordSystem.sup_m_covBy_τ hR hR_π hp hp_τ hp_σ) Γ.hO hR
    (CoordSystem.ne_R_of_le_π hR_π (le_sup_left.trans le_sup_left))
    (sup_le ((le_sup_left.trans le_sup_left).trans le_sup_left) le_sup_right)
    (fun h' => CoordSystem.hR_not_sup_m hR_π hp hp_σ (le_sup_right.trans h'))
  show IsAtom ((p ⊔ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ R))
  rwa [inf_comm]

theorem CoordSystem.zproj_ne_R
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p : L} (hp : IsAtom p)
    (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    Γ.zproj R p ≠ R :=
  fun h => CoordSystem.hR_not_sup_m hR_π hp hp_σ
    (h ▸ (inf_le_left : Γ.zproj R p ≤ p ⊔ (Γ.U ⊔ Γ.V)))

theorem CoordSystem.zproj_not_m (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p : L} (hp : IsAtom p)
    (hp_τ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    ¬ Γ.zproj R p ≤ Γ.U ⊔ Γ.V := by
  intro h
  have h1 : Γ.zproj R p ≤ (Γ.O ⊔ R) ⊓ (Γ.U ⊔ Γ.V ⊔ R) :=
    le_inf (Γ.zproj_le_ζ R p) (h.trans le_sup_left)
  rw [CoordSystem.ζ_inf_σ hR hR_π] at h1
  exact CoordSystem.zproj_ne_R hR_π hp hp_σ
    (IsAtom.eq_of_le (CoordSystem.zproj_is_atom hR hR_π hp hp_τ hp_σ) hR h1)

theorem CoordSystem.sup_m_zproj (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p : L} (hp : IsAtom p)
    (hp_τ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    p ⊔ (Γ.U ⊔ Γ.V) = Γ.zproj R p ⊔ (Γ.U ⊔ Γ.V) := by
  have hz_not_m := CoordSystem.zproj_not_m hR hR_π hp hp_τ hp_σ
  have h1 : Γ.zproj R p ⊔ (Γ.U ⊔ Γ.V) ≤ p ⊔ (Γ.U ⊔ Γ.V) :=
    sup_le (inf_le_left : Γ.zproj R p ≤ p ⊔ (Γ.U ⊔ Γ.V)) le_sup_right
  rcases (CoordSystem.m_covBy_sup hp (CoordSystem.not_m_of_off_σ hp_σ)).eq_or_eq
    le_sup_right h1 with h | h
  · exact absurd
      (h ▸ (le_sup_left : Γ.zproj R p ≤ Γ.zproj R p ⊔ (Γ.U ⊔ Γ.V))) hz_not_m
  · exact h.symm

theorem CoordSystem.space_recovers (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {p : L} (hp : IsAtom p)
    (hp_τ : p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R) (hp_σ : ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R) :
    Γ.spoint R (Γ.baseproj R p) (Γ.zproj R p) = p := by
  show (Γ.baseproj R p ⊔ R) ⊓ (Γ.zproj R p ⊔ (Γ.U ⊔ Γ.V)) = p
  rw [← CoordSystem.sup_R_baseproj hR hR_π hp hp_τ hp_σ,
    ← CoordSystem.sup_m_zproj hR hR_π hp hp_τ hp_σ,
    sup_inf_assoc_of_le R (le_sup_left : p ≤ p ⊔ (Γ.U ⊔ Γ.V))]
  have h_meet : R ⊓ (p ⊔ (Γ.U ⊔ Γ.V)) = ⊥ :=
    (hR.le_iff.mp inf_le_left).resolve_right
      (fun h => CoordSystem.hR_not_sup_m hR_π hp hp_σ (h ▸ inf_le_right))
  rw [h_meet, sup_bot_eq]

/-! ## The chart read backwards -/

theorem CoordSystem.ζ_affine_off_σ (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {z : L} (hz : IsAtom z)
    (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    ¬ z ≤ Γ.U ⊔ Γ.V ⊔ R := fun h =>
  hz_R (IsAtom.eq_of_le hz hR
    (le_of_le_of_eq (le_inf hz_ζ h) (CoordSystem.ζ_inf_σ hR hR_π)))

theorem CoordSystem.ζ_le_τ (Γ : CoordSystem L) (R : L) :
    Γ.O ⊔ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
  sup_le ((le_sup_left.trans le_sup_left).trans le_sup_left) le_sup_right

theorem CoordSystem.plane_affine_off_σ (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {x : L}
    (hx_π : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hx_m : ¬ x ≤ Γ.U ⊔ Γ.V) :
    ¬ x ≤ Γ.U ⊔ Γ.V ⊔ R := fun h =>
  hx_m (le_of_le_of_eq (le_inf h hx_π) (CoordSystem.σ_inf_π hR hR_π))

theorem CoordSystem.spoint_is_atom (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {x : L} (hx : IsAtom x)
    (hx_π : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {z : L} (hz : IsAtom z)
    (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    IsAtom (Γ.spoint R x z) := by
  have hz_σ := CoordSystem.ζ_affine_off_σ hR hR_π hz hz_ζ hz_R
  exact line_meets_hyperplane
    (CoordSystem.sup_m_covBy_τ hR hR_π hz (hz_ζ.trans (Γ.ζ_le_τ R)) hz_σ)
    hx hR (CoordSystem.ne_R_of_le_π hR_π hx_π)
    (sup_le (hx_π.trans le_sup_left) le_sup_right)
    (fun h => CoordSystem.hR_not_sup_m hR_π hz hz_σ (le_sup_right.trans h))

theorem CoordSystem.spoint_le_τ {x z : L} (hx_π : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    Γ.spoint R x z ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R :=
  (inf_le_left : Γ.spoint R x z ≤ x ⊔ R).trans
    (sup_le (hx_π.trans le_sup_left) le_sup_right)

theorem CoordSystem.spoint_ne_R (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {x z : L} (hz : IsAtom z)
    (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    Γ.spoint R x z ≠ R := by
  intro h
  have hz_σ := CoordSystem.ζ_affine_off_σ hR hR_π hz hz_ζ hz_R
  exact CoordSystem.hR_not_sup_m hR_π hz hz_σ
    (h ▸ (inf_le_right : Γ.spoint R x z ≤ z ⊔ (Γ.U ⊔ Γ.V)))

theorem CoordSystem.sup_R_spoint (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {x : L} (hx : IsAtom x)
    (hx_π : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {z : L} (hz : IsAtom z)
    (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    Γ.spoint R x z ⊔ R = x ⊔ R := by
  have hs_atom := CoordSystem.spoint_is_atom hR hR_π hx hx_π hz hz_ζ hz_R
  have h := line_eq_of_atom_le' hR hx hs_atom
    (CoordSystem.ne_R_of_le_π hR_π hx_π).symm
    (Ne.symm (CoordSystem.spoint_ne_R hR hR_π hz hz_ζ hz_R))
    (le_of_le_of_eq (inf_le_left : Γ.spoint R x z ≤ x ⊔ R) (sup_comm x R))
  rw [sup_comm (Γ.spoint R x z) R, sup_comm x R]
  exact h.symm

theorem CoordSystem.spoint_off_σ (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {x : L} (hx : IsAtom x)
    (hx_π : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hx_m : ¬ x ≤ Γ.U ⊔ Γ.V) {z : L}
    (hz : IsAtom z) (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    ¬ Γ.spoint R x z ≤ Γ.U ⊔ Γ.V ⊔ R := by
  intro h
  apply CoordSystem.plane_affine_off_σ hR hR_π hx_π hx_m
  have hx_le : x ≤ Γ.spoint R x z ⊔ R := by
    rw [CoordSystem.sup_R_spoint hR hR_π hx hx_π hz hz_ζ hz_R]
    exact le_sup_left
  exact hx_le.trans (sup_le h le_sup_right)

theorem CoordSystem.baseproj_spoint (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {x : L} (hx : IsAtom x)
    (hx_π : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {z : L} (hz : IsAtom z)
    (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    Γ.baseproj R (Γ.spoint R x z) = x := by
  show (Γ.spoint R x z ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = x
  rw [CoordSystem.sup_R_spoint hR hR_π hx hx_π hz hz_ζ hz_R]
  exact CoordSystem.baseproj_of_le_π hR hR_π hx_π

theorem CoordSystem.zproj_of_on_ζ (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {z : L} (hz : IsAtom z)
    (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    Γ.zproj R z = z := by
  have hz_σ := CoordSystem.ζ_affine_off_σ hR hR_π hz hz_ζ hz_R
  exact (IsAtom.eq_of_le hz
    (CoordSystem.zproj_is_atom hR hR_π hz (hz_ζ.trans (Γ.ζ_le_τ R)) hz_σ)
    (le_inf le_sup_left hz_ζ)).symm

theorem CoordSystem.sup_m_spoint (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {x : L} (hx : IsAtom x)
    (hx_π : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hx_m : ¬ x ≤ Γ.U ⊔ Γ.V) {z : L}
    (hz : IsAtom z) (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    Γ.spoint R x z ⊔ (Γ.U ⊔ Γ.V) = z ⊔ (Γ.U ⊔ Γ.V) := by
  have hz_σ := CoordSystem.ζ_affine_off_σ hR hR_π hz hz_ζ hz_R
  have hs_σ := CoordSystem.spoint_off_σ hR hR_π hx hx_π hx_m hz hz_ζ hz_R
  have h1 : Γ.spoint R x z ⊔ (Γ.U ⊔ Γ.V) ≤ z ⊔ (Γ.U ⊔ Γ.V) :=
    sup_le (inf_le_right : Γ.spoint R x z ≤ z ⊔ (Γ.U ⊔ Γ.V)) le_sup_right
  rcases (CoordSystem.m_covBy_sup hz (CoordSystem.not_m_of_off_σ hz_σ)).eq_or_eq
    le_sup_right h1 with h | h
  · exact absurd
      (h ▸ (le_sup_left : Γ.spoint R x z ≤ Γ.spoint R x z ⊔ (Γ.U ⊔ Γ.V)))
      (CoordSystem.not_m_of_off_σ hs_σ)
  · exact h

theorem CoordSystem.zproj_spoint (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {x : L} (hx : IsAtom x)
    (hx_π : x ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hx_m : ¬ x ≤ Γ.U ⊔ Γ.V) {z : L}
    (hz : IsAtom z) (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    Γ.zproj R (Γ.spoint R x z) = z := by
  show (Γ.spoint R x z ⊔ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ R) = z
  rw [CoordSystem.sup_m_spoint hR hR_π hx hx_π hx_m hz hz_ζ hz_R]
  exact CoordSystem.zproj_of_on_ζ hR hR_π hz hz_ζ hz_R

theorem CoordSystem.zproj_of_affine_π (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {q : L}
    (hq_π : q ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) (hq_m : ¬ q ≤ Γ.U ⊔ Γ.V) :
    Γ.zproj R q = Γ.O := by
  have h_sup : q ⊔ (Γ.U ⊔ Γ.V) = Γ.O ⊔ Γ.U ⊔ Γ.V := by
    rcases Γ.m_covBy_π.eq_or_eq
      (le_sup_right : Γ.U ⊔ Γ.V ≤ q ⊔ (Γ.U ⊔ Γ.V))
      (sup_le hq_π Γ.m_le_π) with h | h
    · exact absurd (h ▸ (le_sup_left : q ≤ q ⊔ (Γ.U ⊔ Γ.V))) hq_m
    · exact h
  show (q ⊔ (Γ.U ⊔ Γ.V)) ⊓ (Γ.O ⊔ R) = Γ.O
  rw [h_sup, inf_comm]
  exact CoordSystem.ζ_inf_π hR hR_π

/-! ## The space chart: the affine 3-space splits losslessly -/

def SpaceAffine (Γ : CoordSystem L) (R : L) : Type u :=
  {p : L // IsAtom p ∧ p ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ⊔ R ∧ ¬ p ≤ Γ.U ⊔ Γ.V ⊔ R}

def Applicate (Γ : CoordSystem L) (R : L) : Type u :=
  {z : L // IsAtom z ∧ z ≤ Γ.O ⊔ R ∧ z ≠ R}

noncomputable def spaceChart (Γ : CoordSystem L) {R : L} (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    SpaceAffine Γ R ≃ Affine Γ × Applicate Γ R where
  toFun p :=
    (⟨Γ.baseproj R p.1,
        CoordSystem.baseproj_is_atom hR hR_π p.2.1 p.2.2.1 p.2.2.2,
        Γ.baseproj_le_π R p.1,
        CoordSystem.baseproj_affine hR hR_π p.2.1 p.2.2.1 p.2.2.2⟩,
     ⟨Γ.zproj R p.1,
        CoordSystem.zproj_is_atom hR hR_π p.2.1 p.2.2.1 p.2.2.2,
        Γ.zproj_le_ζ R p.1,
        CoordSystem.zproj_ne_R hR_π p.2.1 p.2.2.2⟩)
  invFun xz :=
    ⟨Γ.spoint R xz.1.1 xz.2.1,
      CoordSystem.spoint_is_atom hR hR_π xz.1.2.1 xz.1.2.2.1
        xz.2.2.1 xz.2.2.2.1 xz.2.2.2.2,
      CoordSystem.spoint_le_τ xz.1.2.2.1,
      CoordSystem.spoint_off_σ hR hR_π xz.1.2.1 xz.1.2.2.1 xz.1.2.2.2
        xz.2.2.1 xz.2.2.2.1 xz.2.2.2.2⟩
  left_inv p := Subtype.ext
    (CoordSystem.space_recovers hR hR_π p.2.1 p.2.2.1 p.2.2.2)
  right_inv xz := Prod.ext
    (Subtype.ext (CoordSystem.baseproj_spoint hR hR_π xz.1.2.1 xz.1.2.2.1
      xz.2.2.1 xz.2.2.2.1 xz.2.2.2.2))
    (Subtype.ext (CoordSystem.zproj_spoint hR hR_π xz.1.2.1 xz.1.2.2.1
      xz.1.2.2.2 xz.2.2.1 xz.2.2.2.1 xz.2.2.2.2))

/-! ## The z-transport: the applicate axis reads in `Coordinate Γ` -/

def CoordSystem.zcoord (Γ : CoordSystem L) (c z : L) : L :=
  (z ⊔ c) ⊓ (Γ.O ⊔ Γ.U)

def CoordSystem.zseat (Γ : CoordSystem L) (R c x : L) : L :=
  (x ⊔ c) ⊓ (Γ.O ⊔ R)

theorem CoordSystem.l_inf_UR (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ R) = Γ.U := by
  rw [sup_comm Γ.O Γ.U]
  exact modular_intersection Γ.hU Γ.hO hR Γ.hOU.symm
    (CoordSystem.hU_ne_R hR_π)
    (CoordSystem.ne_R_of_le_π hR_π (le_sup_left.trans le_sup_left))
    (fun h => hR_π (h.trans (sup_le (le_sup_right.trans le_sup_left)
      (le_sup_left.trans le_sup_left))))

theorem CoordSystem.ζ_inf_UR (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    (Γ.O ⊔ R) ⊓ (Γ.U ⊔ R) = R := by
  rw [sup_comm Γ.O R, sup_comm Γ.U R]
  exact modular_intersection hR Γ.hO Γ.hU
    (CoordSystem.ne_R_of_le_π hR_π (le_sup_left.trans le_sup_left)).symm
    (CoordSystem.hU_ne_R hR_π).symm Γ.hOU
    (fun h => CoordSystem.hU_not_ζ hR hR_π (h.trans (sup_comm R Γ.O).le))

theorem CoordSystem.center_not_l (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) :
    ¬ c ≤ Γ.O ⊔ Γ.U := fun h =>
  hc_U (IsAtom.eq_of_le hc Γ.hU
    (le_of_le_of_eq (le_inf h hc_UR) (CoordSystem.l_inf_UR hR hR_π)))

theorem CoordSystem.center_not_ζ (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_R : c ≠ R) :
    ¬ c ≤ Γ.O ⊔ R := fun h =>
  hc_R (IsAtom.eq_of_le hc hR
    (le_of_le_of_eq (le_inf h hc_UR) (CoordSystem.ζ_inf_UR hR hR_π)))

theorem CoordSystem.UR_eq_Uc (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R) :
    Γ.U ⊔ R = Γ.U ⊔ c :=
  line_eq_of_atom_le Γ.hU hR hc (CoordSystem.hU_ne_R hR_π)
    (Ne.symm hc_U) (Ne.symm hc_R) hc_UR

theorem CoordSystem.RU_eq_Rc (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R) :
    R ⊔ Γ.U = R ⊔ c :=
  line_eq_of_atom_le hR Γ.hU hc (CoordSystem.hU_ne_R hR_π).symm
    (Ne.symm hc_R) (Ne.symm hc_U) (hc_UR.trans (sup_comm Γ.U R).le)

theorem CoordSystem.ζ_sup_center (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R) :
    Γ.O ⊔ R ⊔ c = Γ.O ⊔ Γ.U ⊔ c := by
  rw [sup_assoc, sup_assoc, ← CoordSystem.RU_eq_Rc hR hR_π hc hc_UR hc_U hc_R,
    ← CoordSystem.UR_eq_Uc hR hR_π hc hc_UR hc_U hc_R, sup_comm R Γ.U]

theorem CoordSystem.ne_center_of_on_ζ (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_R : c ≠ R) {z : L} (hz_ζ : z ≤ Γ.O ⊔ R) :
    z ≠ c :=
  fun h => CoordSystem.center_not_ζ hR hR_π hc hc_UR hc_R (h ▸ hz_ζ)

theorem CoordSystem.ne_center_of_on_l (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) {x : L} (hx_l : x ≤ Γ.O ⊔ Γ.U) :
    x ≠ c :=
  fun h => CoordSystem.center_not_l hR hR_π hc hc_UR hc_U (h ▸ hx_l)

theorem CoordSystem.zcoord_is_atom (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R)
    {z : L} (hz : IsAtom z) (hz_ζ : z ≤ Γ.O ⊔ R) :
    IsAtom (Γ.zcoord c z) :=
  perspect_atom hc hz
    (CoordSystem.ne_center_of_on_ζ hR hR_π hc hc_UR hc_R hz_ζ)
    Γ.hO Γ.hU Γ.hOU (CoordSystem.center_not_l hR hR_π hc hc_UR hc_U)
    (CoordSystem.ζ_sup_center hR hR_π hc hc_UR hc_U hc_R ▸
      (sup_le (hz_ζ.trans le_sup_left) le_sup_right))

theorem CoordSystem.zcoord_le_l (Γ : CoordSystem L) (c z : L) :
    Γ.zcoord c z ≤ Γ.O ⊔ Γ.U :=
  inf_le_right

theorem CoordSystem.zcoord_ne_U (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R)
    {z : L} (hz : IsAtom z) (hz_ζ : z ≤ Γ.O ⊔ R) (hz_R : z ≠ R) :
    Γ.zcoord c z ≠ Γ.U := by
  intro h
  have hU_le : Γ.U ≤ z ⊔ c := h ▸ (inf_le_left : Γ.zcoord c z ≤ z ⊔ c)
  have h_line : c ⊔ z = c ⊔ Γ.U :=
    line_eq_of_atom_le' hc hz Γ.hU
      (Ne.symm (CoordSystem.ne_center_of_on_ζ hR hR_π hc hc_UR hc_R hz_ζ))
      hc_U (hU_le.trans (sup_comm z c).le)
  have hz_le : z ≤ Γ.U ⊔ R := by
    calc z ≤ c ⊔ z := le_sup_right
      _ = c ⊔ Γ.U := h_line
      _ = Γ.U ⊔ c := sup_comm _ _
      _ = Γ.U ⊔ R := (CoordSystem.UR_eq_Uc hR hR_π hc hc_UR hc_U hc_R).symm
  exact hz_R (IsAtom.eq_of_le hz hR
    (le_of_le_of_eq (le_inf hz_ζ hz_le) (CoordSystem.ζ_inf_UR hR hR_π)))

theorem CoordSystem.zseat_is_atom (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R)
    {x : L} (hx : IsAtom x) (hx_l : x ≤ Γ.O ⊔ Γ.U) :
    IsAtom (Γ.zseat R c x) :=
  perspect_atom hc hx
    (CoordSystem.ne_center_of_on_l hR hR_π hc hc_UR hc_U hx_l)
    Γ.hO hR (CoordSystem.ne_R_of_le_π hR_π (le_sup_left.trans le_sup_left))
    (CoordSystem.center_not_ζ hR hR_π hc hc_UR hc_R)
    ((CoordSystem.ζ_sup_center hR hR_π hc hc_UR hc_U hc_R).symm ▸
      (sup_le (hx_l.trans le_sup_left) le_sup_right))

theorem CoordSystem.zseat_le_ζ (Γ : CoordSystem L) (R c x : L) :
    Γ.zseat R c x ≤ Γ.O ⊔ R :=
  inf_le_right

theorem CoordSystem.zseat_ne_R (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R)
    {x : L} (hx : IsAtom x) (hx_l : x ≤ Γ.O ⊔ Γ.U) (hx_U : x ≠ Γ.U) :
    Γ.zseat R c x ≠ R := by
  intro h
  have hR_le : R ≤ x ⊔ c := h ▸ (inf_le_left : Γ.zseat R c x ≤ x ⊔ c)
  have h_line : c ⊔ x = c ⊔ R :=
    line_eq_of_atom_le' hc hx hR
      (Ne.symm (CoordSystem.ne_center_of_on_l hR hR_π hc hc_UR hc_U hx_l))
      hc_R (hR_le.trans (sup_comm x c).le)
  have hx_le : x ≤ Γ.U ⊔ R := by
    calc x ≤ c ⊔ x := le_sup_right
      _ = c ⊔ R := h_line
      _ = R ⊔ c := sup_comm _ _
      _ = R ⊔ Γ.U := (CoordSystem.RU_eq_Rc hR hR_π hc hc_UR hc_U hc_R).symm
      _ = Γ.U ⊔ R := sup_comm _ _
  exact hx_U (IsAtom.eq_of_le hx Γ.hU
    (le_of_le_of_eq (le_inf hx_l hx_le) (CoordSystem.l_inf_UR hR hR_π)))

theorem CoordSystem.zseat_zcoord (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R)
    {z : L} (hz : IsAtom z) (hz_ζ : z ≤ Γ.O ⊔ R) :
    Γ.zseat R c (Γ.zcoord c z) = z :=
  perspect_roundtrip hc hz
    (CoordSystem.ne_center_of_on_ζ hR hR_π hc hc_UR hc_R hz_ζ)
    Γ.hO hR (CoordSystem.ne_R_of_le_π hR_π (le_sup_left.trans le_sup_left))
    Γ.hO Γ.hU Γ.hOU
    (CoordSystem.center_not_ζ hR hR_π hc hc_UR hc_R)
    (CoordSystem.center_not_l hR hR_π hc hc_UR hc_U)
    (CoordSystem.ζ_sup_center hR hR_π hc hc_UR hc_U hc_R) hz_ζ

theorem CoordSystem.zcoord_zseat (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R)
    {x : L} (hx : IsAtom x) (hx_l : x ≤ Γ.O ⊔ Γ.U) :
    Γ.zcoord c (Γ.zseat R c x) = x :=
  perspect_roundtrip hc hx
    (CoordSystem.ne_center_of_on_l hR hR_π hc hc_UR hc_U hx_l)
    Γ.hO Γ.hU Γ.hOU
    Γ.hO hR (CoordSystem.ne_R_of_le_π hR_π (le_sup_left.trans le_sup_left))
    (CoordSystem.center_not_l hR hR_π hc hc_UR hc_U)
    (CoordSystem.center_not_ζ hR hR_π hc hc_UR hc_R)
    (CoordSystem.ζ_sup_center hR hR_π hc hc_UR hc_U hc_R).symm hx_l

theorem CoordSystem.zcoord_O (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) :
    Γ.zcoord c Γ.O = Γ.O :=
  perspect_fixes_intersection hc Γ.hO
    (CoordSystem.ne_center_of_on_l hR hR_π hc hc_UR hc_U le_sup_left)
    Γ.hO Γ.hU Γ.hOU (CoordSystem.center_not_l hR hR_π hc hc_UR hc_U)
    (le_sup_left : Γ.O ≤ Γ.O ⊔ R) le_sup_left
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right)

theorem CoordSystem.zcoord_R (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R) :
    Γ.zcoord c R = Γ.U := by
  show (R ⊔ c) ⊓ (Γ.O ⊔ Γ.U) = Γ.U
  rw [← CoordSystem.RU_eq_Rc hR hR_π hc hc_UR hc_U hc_R, sup_comm R Γ.U,
    inf_comm]
  exact CoordSystem.l_inf_UR hR hR_π

noncomputable def applicateTransport (Γ : CoordSystem L) {R : L}
    (hR : IsAtom R) (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R) :
    Applicate Γ R ≃ Coordinate Γ where
  toFun z :=
    ⟨Γ.zcoord c z.1,
      CoordSystem.zcoord_is_atom hR hR_π hc hc_UR hc_U hc_R z.2.1 z.2.2.1,
      Γ.zcoord_le_l c z.1,
      CoordSystem.zcoord_ne_U hR hR_π hc hc_UR hc_U hc_R z.2.1 z.2.2.1 z.2.2.2⟩
  invFun x :=
    ⟨Γ.zseat R c x.1,
      CoordSystem.zseat_is_atom hR hR_π hc hc_UR hc_U hc_R x.2.1 x.2.2.1,
      Γ.zseat_le_ζ R c x.1,
      CoordSystem.zseat_ne_R hR hR_π hc hc_UR hc_U hc_R x.2.1 x.2.2.1 x.2.2.2⟩
  left_inv z := Subtype.ext
    (CoordSystem.zseat_zcoord hR hR_π hc hc_UR hc_U hc_R z.2.1 z.2.2.1)
  right_inv x := Subtype.ext
    (CoordSystem.zcoord_zseat hR hR_π hc hc_UR hc_U hc_R x.2.1 x.2.2.1)

/-! ## The assembly: the affine 3-space is `D³` at atom level -/

noncomputable def solidChart (Γ : CoordSystem L) {R : L} (hR : IsAtom R)
    (hR_π : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) {c : L} (hc : IsAtom c)
    (hc_UR : c ≤ Γ.U ⊔ R) (hc_U : c ≠ Γ.U) (hc_R : c ≠ R) :
    SpaceAffine Γ R ≃ (Coordinate Γ × Coordinate Γ) × Coordinate Γ :=
  (spaceChart Γ hR hR_π).trans
    ((planeChart Γ).prodCongr (applicateTransport Γ hR hR_π hc hc_UR hc_U hc_R))

theorem CoordFrame.solidChart_exists (Φ : CoordFrame L) :
    Nonempty (SpaceAffine Φ.Γ Φ.R ≃
      (Coordinate Φ.Γ × Coordinate Φ.Γ) × Coordinate Φ.Γ) := by
  obtain ⟨c, hc, hc_UR, hc_U, hc_R⟩ :=
    Φ.h_irred Φ.Γ.U Φ.R Φ.Γ.hU Φ.hR_atom (CoordSystem.hU_ne_R Φ.hR_not)
  exact ⟨solidChart Φ.Γ Φ.hR_atom Φ.hR_not hc hc_UR hc_U hc_R⟩

end Foam.Bridges

/-- info: 'Foam.Bridges.line_meets_hyperplane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.line_meets_hyperplane

/-- info: 'Foam.Bridges.CoordSystem.π_covBy_τ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.π_covBy_τ

/-- info: 'Foam.Bridges.CoordSystem.σ_covBy_τ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.σ_covBy_τ

/-- info: 'Foam.Bridges.CoordSystem.σ_inf_π' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.σ_inf_π

/-- info: 'Foam.Bridges.CoordSystem.ζ_inf_π' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ζ_inf_π

/-- info: 'Foam.Bridges.CoordSystem.ζ_inf_σ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ζ_inf_σ

/-- info: 'Foam.Bridges.CoordSystem.sup_m_covBy_τ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.sup_m_covBy_τ

/-- info: 'Foam.Bridges.CoordSystem.baseproj_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.baseproj_is_atom

/-- info: 'Foam.Bridges.CoordSystem.baseproj_of_le_π' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.baseproj_of_le_π

/-- info: 'Foam.Bridges.CoordSystem.zproj_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.zproj_is_atom

/-- info: 'Foam.Bridges.CoordSystem.zproj_of_affine_π' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.zproj_of_affine_π

/-- info: 'Foam.Bridges.CoordSystem.space_recovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.space_recovers

/-- info: 'Foam.Bridges.CoordSystem.spoint_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.spoint_is_atom

/-- info: 'Foam.Bridges.CoordSystem.baseproj_spoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.baseproj_spoint

/-- info: 'Foam.Bridges.CoordSystem.zproj_spoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.zproj_spoint

/-- info: 'Foam.Bridges.spaceChart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.spaceChart

/-- info: 'Foam.Bridges.CoordSystem.ζ_sup_center' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.ζ_sup_center

/-- info: 'Foam.Bridges.CoordSystem.zcoord_is_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.zcoord_is_atom

/-- info: 'Foam.Bridges.CoordSystem.zseat_zcoord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.zseat_zcoord

/-- info: 'Foam.Bridges.CoordSystem.zcoord_zseat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.zcoord_zseat

/-- info: 'Foam.Bridges.CoordSystem.zcoord_O' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.zcoord_O

/-- info: 'Foam.Bridges.CoordSystem.zcoord_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordSystem.zcoord_R

/-- info: 'Foam.Bridges.applicateTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.applicateTransport

/-- info: 'Foam.Bridges.solidChart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.solidChart

/-- info: 'Foam.Bridges.CoordFrame.solidChart_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.solidChart_exists
