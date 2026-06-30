import Bridges.Dilation
import Bridges.Inverse

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

structure Dilation (Γ : CoordSystem L) where

  toOrderIso : L ≃o L

  fixes_O : toOrderIso Γ.O = Γ.O

  preserves_l : toOrderIso (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U

  fixes_m : ∀ P : L, IsAtom P → P ≤ Γ.U ⊔ Γ.V → toOrderIso P = P

namespace Dilation

variable {Γ : CoordSystem L}

@[ext]
theorem ext {f g : Dilation Γ} (h : f.toOrderIso = g.toOrderIso) : f = g := by
  cases f
  cases g
  congr

def id (Γ : CoordSystem L) : Dilation Γ where
  toOrderIso := OrderIso.refl L
  fixes_O := rfl
  preserves_l := rfl
  fixes_m := fun _ _ _ => rfl

def comp (f g : Dilation Γ) : Dilation Γ where
  toOrderIso := f.toOrderIso.trans g.toOrderIso
  fixes_O := by

    simp [OrderIso.trans_apply, f.fixes_O, g.fixes_O]
  preserves_l := by

    rw [OrderIso.trans_apply, f.preserves_l, g.preserves_l]
  fixes_m := by
    intro P hP_atom hP_le

    simp [OrderIso.trans_apply, f.fixes_m P hP_atom hP_le,
          g.fixes_m P hP_atom hP_le]

instance : Mul (Dilation Γ) := ⟨comp⟩

instance : One (Dilation Γ) := ⟨id Γ⟩

instance : Monoid (Dilation Γ) where
  mul := comp
  one := id Γ
  mul_assoc f g h := by
    ext
    rfl
  one_mul f := by
    ext
    rfl
  mul_one f := by
    ext
    rfl

end Dilation

noncomputable def σ_toFun (Γ : CoordSystem L) (c : L) (P : L) : L := by
  classical
  exact
    if P ≤ Γ.O ⊔ Γ.U then coord_mul Γ P c
    else if P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V then dilation_ext Γ c P
    else P

noncomputable def σ_invFun (Γ : CoordSystem L) (c : L) (P : L) : L := by
  classical
  exact
    if P ≤ Γ.O ⊔ Γ.U then coord_mul Γ P (coord_inv Γ c)
    else if P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V then dilation_ext Γ (coord_inv Γ c) P
    else P

noncomputable def σ (Γ : CoordSystem L) (c : L)
    (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U) :
    Dilation Γ where
  toOrderIso :=
    { toFun := σ_toFun Γ c
      invFun := σ_invFun Γ c
      left_inv := by

        sorry
      right_inv := by

        sorry
      map_rel_iff' := by

        sorry }
  fixes_O := by

    show σ_toFun Γ c Γ.O = Γ.O
    unfold σ_toFun
    classical
    simp only [le_sup_left, if_true]
    exact coord_mul_left_zero Γ c hc hc_on hc_ne_U
  preserves_l := by

    sorry
  fixes_m := by
    intro P hP hP_on_m

    show σ_toFun Γ c P = P
    unfold σ_toFun
    classical
    by_cases hP_on_l : P ≤ Γ.O ⊔ Γ.U
    · simp only [hP_on_l, if_true]

      have hP_eq_U : P = Γ.U := Γ.atom_on_both_eq_U hP hP_on_l hP_on_m
      subst hP_eq_U

      sorry
    · simp only [hP_on_l, if_false]
      have hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
        hP_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
      simp only [hP_plane, if_true]
      exact dilation_ext_fixes_m Γ hc hP hc_on hP_on_m hc_ne_O hP_on_l

theorem σ_mul (Γ : CoordSystem L) (a b : L)
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : IsAtom (coord_mul Γ a b))
    (hab_on : coord_mul Γ a b ≤ Γ.O ⊔ Γ.U)
    (hab_ne_O : coord_mul Γ a b ≠ Γ.O)
    (hab_ne_U : coord_mul Γ a b ≠ Γ.U) :
    σ Γ (coord_mul Γ a b) hab hab_on hab_ne_O hab_ne_U =
      σ Γ a ha ha_on ha_ne_O ha_ne_U * σ Γ b hb hb_on hb_ne_O hb_ne_U :=
  sorry

theorem σ_add_pointwise (Γ : CoordSystem L) (a b : L)
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : IsAtom (coord_add Γ a b))
    (hab_on : coord_add Γ a b ≤ Γ.O ⊔ Γ.U)
    (hab_ne_O : coord_add Γ a b ≠ Γ.O)
    (hab_ne_U : coord_add Γ a b ≠ Γ.U)
    (P : L) :
    (σ Γ (coord_add Γ a b) hab hab_on hab_ne_O hab_ne_U).toOrderIso P =
      coord_add Γ
        ((σ Γ a ha ha_on ha_ne_O ha_ne_U).toOrderIso P)
        ((σ Γ b hb hb_on hb_ne_O hb_ne_U).toOrderIso P) :=
  sorry

end Foam.Bridges
