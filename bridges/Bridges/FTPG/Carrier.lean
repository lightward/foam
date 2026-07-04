import Bridges.FTPG.Projective
import Bridges.FTPG.Coord
import Bridges.FTPG.Mul
import Bridges.FTPG.Neg
import Bridges.FTPG.Inverse
import Bridges.FTPG.Parallelogram

/-!
# The coordinate carrier

`Coordinate Γ` — the affine points of the coordinate line `l = O ⊔ U` (the
atoms on `l` other than `U`) — together with its `Zero`/`One` and the
existence of a coordinate system from the irreducibility and height
hypotheses.  This file sits *upstream* of the algebra
(`CoordinateAlgebra`, `Additive`, `Ring`): the totalized operations and
their laws are proven there over this carrier, and the `DivisionRing`
assembly (`Instance.lean`) consumes both.
-/

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

def Coordinate (Γ : CoordSystem L) : Type u :=
  {a : L // IsAtom a ∧ a ≤ Γ.O ⊔ Γ.U ∧ a ≠ Γ.U}

namespace Coordinate

variable {Γ : CoordSystem L}

@[ext] theorem ext {a b : Coordinate Γ} (h : a.1 = b.1) : a = b := Subtype.ext h

theorem isAtom (a : Coordinate Γ) : IsAtom a.1 := a.2.1
theorem on_l   (a : Coordinate Γ) : a.1 ≤ Γ.O ⊔ Γ.U := a.2.2.1
theorem ne_U   (a : Coordinate Γ) : a.1 ≠ Γ.U := a.2.2.2

instance : Zero (Coordinate Γ) := ⟨⟨Γ.O, Γ.hO, le_sup_left, Γ.hOU⟩⟩
instance : One  (Coordinate Γ) := ⟨⟨Γ.I, Γ.hI, Γ.hI_on, Γ.hUI.symm⟩⟩

theorem zero_val : (0 : Coordinate Γ).1 = Γ.O := rfl
theorem one_val  : (1 : Coordinate Γ).1 = Γ.I := rfl

end Coordinate

omit [ComplementedLattice L] [IsModularLattice L] in
/-- In an atomistic lattice, if `x < y` there is an atom `≤ y` that is `≰ x`. -/
theorem exists_atom_le_not_le {x y : L} (hxy : x < y) :
    ∃ p : L, IsAtom p ∧ p ≤ y ∧ ¬ p ≤ x := by
  by_contra h
  push_neg at h
  obtain ⟨s, hs_lub, hs_atoms⟩ := IsAtomistic.isLUB_atoms y
  have hy_le_x : y ≤ x :=
    hs_lub.2 (fun p hp => h p (hs_atoms p hp) (hs_lub.1 hp))
  exact lt_irrefl _ (lt_of_le_of_lt hy_le_x hxy)

theorem coordSystem_exists
    (h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (h_height : ∃ (a b c d : L), ⊥ < a ∧ a < b ∧ b < c ∧ c < d) :
    Nonempty (CoordSystem L) := by
  obtain ⟨a, b, c, _d, ha_pos, hab, hbc, _hcd⟩ := h_height
  -- O : an atom below a
  obtain ⟨O, hO, hO_le_a, _⟩ := exists_atom_le_not_le ha_pos
  have hO_le_b : O ≤ b := hO_le_a.trans hab.le
  -- U : an atom below b not below a, hence O ≠ U
  obtain ⟨U, hU, hU_le_b, hU_not_a⟩ := exists_atom_le_not_le hab
  have hOU : O ≠ U := fun h => hU_not_a (h ▸ hO_le_a)
  -- V : an atom below c off the line l = O ⊔ U
  have hOU_lt_c : O ⊔ U < c := lt_of_le_of_lt (sup_le hO_le_b hU_le_b) hbc
  obtain ⟨V, hV, _hV_le_c, hV_off⟩ := exists_atom_le_not_le hOU_lt_c
  -- l = O ⊔ U incidences
  have hO_le_l : O ≤ O ⊔ U := le_sup_left
  have hU_le_l : U ≤ O ⊔ U := le_sup_right
  -- I : third atom on the line l
  obtain ⟨I, hI, hI_on, hI_ne_O, hI_ne_U⟩ := h_irred O U hO hU hOU
  have hOI : O ≠ I := fun h => hI_ne_O h.symm
  have hUI : U ≠ I := fun h => hI_ne_U h.symm
  -- distinctness with V (V is off l, the others lie on l)
  have hI_ne_V : I ≠ V := fun h => hV_off (h ▸ hI_on)
  have hV_ne_I : V ≠ I := fun h => hI_ne_V h.symm
  -- C : third atom on the line I ⊔ V
  obtain ⟨C, hC, hC_on_IV, hC_ne_I, hC_ne_V⟩ := h_irred I V hI hV hI_ne_V
  -- plane membership
  have hC_plane : C ≤ O ⊔ U ⊔ V :=
    hC_on_IV.trans (sup_le (hI_on.trans le_sup_left) le_sup_right)
  -- C not on l
  have hC_not_l : ¬ C ≤ O ⊔ U := by
    intro hC_l
    have h_IV_eq : I ⊔ V = I ⊔ C :=
      line_eq_of_atom_le hI hV hC hI_ne_V (fun h => hC_ne_I h.symm) hC_ne_V.symm hC_on_IV
    have hV_le_l : V ≤ O ⊔ U := by
      calc V ≤ I ⊔ V := le_sup_right
        _ = I ⊔ C := h_IV_eq
        _ ≤ O ⊔ U := sup_le hI_on hC_l
    exact hV_off hV_le_l
  -- C not on m = U ⊔ V
  have hC_not_m : ¬ C ≤ U ⊔ V := by
    intro hC_m
    have h_VI_eq : V ⊔ I = V ⊔ C :=
      line_eq_of_atom_le hV hI hC hV_ne_I (fun h => hC_ne_V h.symm) hC_ne_I.symm
        (by rw [sup_comm]; exact hC_on_IV)
    have hI_le_m : I ≤ U ⊔ V := by
      calc I ≤ V ⊔ I := le_sup_right
        _ = V ⊔ C := h_VI_eq
        _ ≤ U ⊔ V := sup_le le_sup_right hC_m
    -- I lies on both l and m, so I = U, contradiction
    have hVU : V ≠ U := fun h => hV_off (h ▸ hU_le_l)
    have hVO : V ≠ O := fun h => hV_off (h ▸ hO_le_l)
    have hV_not_UO : ¬ V ≤ U ⊔ O := fun h => hV_off (by rwa [sup_comm] at h)
    have h_meet : (U ⊔ O) ⊓ (U ⊔ V) = U :=
      modular_intersection hU hO hV hOU.symm hVU.symm hVO.symm hV_not_UO
    have hI_le_UO : I ≤ U ⊔ O := by rw [sup_comm]; exact hI_on
    have hI_le_U : I ≤ U := h_meet ▸ le_inf hI_le_UO hI_le_m
    exact hUI ((hU.le_iff.mp hI_le_U).resolve_left hI.1).symm
  exact ⟨{
    O := O, U := U, I := I, V := V, C := C
    hO := hO, hU := hU, hI := hI, hV := hV, hC := hC
    hOU := hOU, hOI := hOI, hUI := hUI
    hI_on := hI_on
    hV_off := hV_off
    hC_not_l := hC_not_l
    hC_not_m := hC_not_m
    hC_plane := hC_plane }⟩

end Foam.Bridges

#print axioms Foam.Bridges.exists_atom_le_not_le
#print axioms Foam.Bridges.coordSystem_exists
