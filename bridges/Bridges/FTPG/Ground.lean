import Bridges.FTPG.Ladder

/-!
# Camp four, second pitch's base: the ladder grounded at τ

Camp three's exports are literally the ladder's induction datum at `n = 4`:
the space's homogeneous coordinates `hvec4` with their four laws
(`hvec4_ne_zero`, `hvec4_span_inj`, `hvec4_span_surj`, `space_collinear_iff`)
instantiate `PointSys` at the frame 3-space `τ = O ⊔ U ⊔ V ⊔ R`, over the
opposite of the coordinate division ring.  The gauge center `c` is supplied
by `h_irred`, exactly as in the space pitches; `PointSys.step` can now climb
from here.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

noncomputable def CoordFrame.pointSysTau (Φ : CoordFrame L) {c : L}
    (hc : IsAtom c) (hc_UR : c ≤ Φ.Γ.U ⊔ Φ.R) (hc_U : c ≠ Φ.Γ.U)
    (hc_R : c ≠ Φ.R) :
    PointSys (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R) 4 (Coordinate Φ.Γ)ᵐᵒᵖ where
  hv := Φ.Γ.hvec4 Φ.R c
  ne_zero := fun _ _ => Φ.Γ.hvec4_ne_zero Φ.R c _
  span_inj := fun hp hp_τ hq hq_τ hpq =>
    Φ.hvec4_span_inj hc hc_UR hc_U hc_R hp hp_τ hq hq_τ hpq
  span_surj := Φ.hvec4_span_surj hc hc_UR hc_U hc_R
  collinear_iff := fun hp hp_τ hq hq_τ hr hr_τ hpq =>
    Φ.space_collinear_iff hc hc_UR hc_U hc_R hp hp_τ hq hq_τ hr hr_τ hpq

theorem CoordFrame.pointSysTau_exists (Φ : CoordFrame L) :
    Nonempty (PointSys (Φ.Γ.O ⊔ Φ.Γ.U ⊔ Φ.Γ.V ⊔ Φ.R) 4
      (Coordinate Φ.Γ)ᵐᵒᵖ) := by
  obtain ⟨c, hc, hc_UR, hc_U, hc_R⟩ :=
    Φ.h_irred Φ.Γ.U Φ.R Φ.Γ.hU Φ.hR_atom (CoordSystem.hU_ne_R Φ.hR_not)
  exact ⟨Φ.pointSysTau hc hc_UR hc_U hc_R⟩

end Foam.Bridges

/-! ## Axiom audit -/

/-- info: 'Foam.Bridges.CoordFrame.pointSysTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.pointSysTau

/-- info: 'Foam.Bridges.CoordFrame.pointSysTau_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.CoordFrame.pointSysTau_exists
