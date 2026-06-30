import Bridges.Projective
import Bridges.Coord
import Bridges.Mul
import Bridges.Neg
import Bridges.Inverse
import Bridges.Parallelogram

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

theorem coord_add_ne_U (a b : Coordinate Γ) : coord_add Γ a.1 b.1 ≠ Γ.U := by
  sorry

theorem coord_mul_ne_U (a b : Coordinate Γ) : coord_mul Γ a.1 b.1 ≠ Γ.U := by
  sorry

theorem coord_mul_ne_O (a b : Coordinate Γ)
    (ha : a.1 ≠ Γ.O) (hb : b.1 ≠ Γ.O) : coord_mul Γ a.1 b.1 ≠ Γ.O := by
  sorry

instance : Zero (Coordinate Γ) := ⟨⟨Γ.O, Γ.hO, le_sup_left, Γ.hOU⟩⟩
instance : One  (Coordinate Γ) := ⟨⟨Γ.I, Γ.hI, Γ.hI_on, Γ.hUI.symm⟩⟩

theorem zero_val : (0 : Coordinate Γ).1 = Γ.O := rfl
theorem one_val  : (1 : Coordinate Γ).1 = Γ.I := rfl

noncomputable instance : Add (Coordinate Γ) :=
  ⟨fun a b => ⟨coord_add Γ a.1 b.1,
    coord_add_atom Γ a.1 b.1 a.isAtom b.isAtom a.on_l b.on_l
      (by sorry) (by sorry) a.ne_U b.ne_U,
    inf_le_right,
    coord_add_ne_U a b⟩⟩

noncomputable instance : Mul (Coordinate Γ) :=
  ⟨fun a b => ⟨coord_mul Γ a.1 b.1,
    coord_mul_atom Γ a.1 b.1 a.isAtom b.isAtom a.on_l b.on_l
      (by sorry) (by sorry) a.ne_U b.ne_U,
    inf_le_right,
    coord_mul_ne_U a b⟩⟩

noncomputable instance : Neg (Coordinate Γ) :=
  ⟨fun a => ⟨coord_neg Γ a.1,
    by sorry,
    coord_neg_on_l Γ a.1,
    by sorry⟩⟩

open Classical in
noncomputable instance : Inv (Coordinate Γ) :=
  ⟨fun a => if h : a.1 = Γ.O then a else ⟨coord_inv Γ a.1,
    coord_inv_atom Γ a.isAtom a.on_l a.ne_U,
    coord_inv_on_l Γ a.1,
    coord_inv_ne_U Γ a.isAtom a.on_l h⟩⟩

noncomputable instance : DivisionRing (Coordinate Γ) where
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  zero := 0
  one := 1
  nsmul := nsmulRec
  zsmul := zsmulRec

  add_assoc      := by intro a b c; ext; sorry
  zero_add       := by intro a;     ext; exact coord_add_left_zero Γ a.1 a.isAtom a.on_l a.ne_U
  add_zero       := by intro a;     ext; exact coord_add_right_zero Γ a.1 a.isAtom a.on_l
  add_comm       := by intro a b;   ext; sorry
  neg_add_cancel := by intro a;     ext; sorry

  mul_assoc      := by intro a b c; ext; sorry
  one_mul        := by intro a;     ext; sorry
  mul_one        := by intro a;     ext; sorry

  left_distrib   := by intro a b c; ext; sorry
  right_distrib  := by intro a b c; ext; sorry

  zero_mul       := by intro a;     ext; exact coord_mul_left_zero Γ a.1 a.isAtom a.on_l a.ne_U
  mul_zero       := by intro a;     ext; exact coord_mul_right_zero Γ a.1 a.isAtom a.on_l a.ne_U

  mul_inv_cancel := by intro a ha;  ext; sorry
  inv_zero       := dif_pos rfl
  exists_pair_ne := ⟨0, 1, by
    intro h; exact Γ.hOI (congrArg Subtype.val h)⟩
  nnqsmul := _
  qsmul := _

end Coordinate

def CoordVec (Γ : CoordSystem L) : Type u := ℕ → Coordinate Γ

noncomputable instance (Γ : CoordSystem L) : AddCommGroup (CoordVec Γ) :=
  inferInstanceAs (AddCommGroup (ℕ → Coordinate Γ))

noncomputable instance (Γ : CoordSystem L) : Module (Coordinate Γ) (CoordVec Γ) :=
  inferInstanceAs (Module (Coordinate Γ) (ℕ → Coordinate Γ))

noncomputable def coordIso (Γ : CoordSystem L) :
    L ≃o Submodule (Coordinate Γ) (CoordVec Γ) where
  toFun     := fun _ => sorry
  invFun    := fun _ => sorry
  left_inv  := fun _ => sorry
  right_inv := fun _ => sorry
  map_rel_iff' := by intro a b; sorry

theorem coordSystem_exists
    (h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (h_height : ∃ (a b c d : L), ⊥ < a ∧ a < b ∧ b < c ∧ c < d) :
    Nonempty (CoordSystem L) := by
  sorry

theorem ftpg_proof : ftpg_statement.{u} := by
  intro L _ _ _ _ _ h_irred h_height
  obtain ⟨Γ⟩ := coordSystem_exists h_irred h_height
  exact ⟨Coordinate Γ, inferInstance,
         CoordVec Γ, inferInstance, inferInstance,
         ⟨coordIso Γ⟩⟩

end Foam.Bridges
