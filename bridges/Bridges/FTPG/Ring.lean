import Bridges.FTPG.Additive

namespace Foam.Bridges

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

namespace Coordinate

variable {Φ : CoordFrame L}

theorem fmul_val_ne_O_of_ne_zero {a b : Coordinate Φ.Γ}
    (ha : a ≠ 0) (hb : b ≠ 0) : (fmul a b).1 ≠ Φ.Γ.O :=
  mul_ne_O a b (val_ne_O_of_ne_zero ha) (val_ne_O_of_ne_zero hb)

theorem fmul_ne_zero {a b : Coordinate Φ.Γ} (ha : a ≠ 0) (hb : b ≠ 0) :
    fmul a b ≠ 0 :=
  ne_zero_of_val_ne_O (fmul_val_ne_O_of_ne_zero ha hb)

theorem fright_distrib_generic (a b c : Coordinate Φ.Γ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hs : fadd a b ≠ 0)
    (hsum : fadd (fmul a c) (fmul b c) ≠ 0) :
    fmul (fadd a b) c = fadd (fmul a c) (fmul b c) := by
  apply Coordinate.ext
  show coord_mul Φ.Γ (coord_add Φ.Γ a.1 b.1) c.1
     = coord_add Φ.Γ (coord_mul Φ.Γ a.1 c.1) (coord_mul Φ.Γ b.1 c.1)
  exact coord_mul_right_distrib Φ.Γ a.1 b.1 c.1 a.isAtom b.isAtom c.isAtom
    a.on_l b.on_l c.on_l
    (val_ne_O_of_ne_zero ha) (val_ne_O_of_ne_zero hb) (val_ne_O_of_ne_zero hc)
    a.ne_U b.ne_U c.ne_U
    (fun h => hab (Coordinate.ext h))
    (fadd_val_ne_O_of_ne_zero hs) (add_ne_U a b)
    (fmul_val_ne_O_of_ne_zero ha hc) (mul_ne_U a c)
    (fmul_val_ne_O_of_ne_zero hb hc) (mul_ne_U b c)
    (fun h => hab (fmul_right_cancel a b c (val_ne_O_of_ne_zero hc)
      (Coordinate.ext h)))
    (fmul_val_ne_O_of_ne_zero hs hc)
    (mul_ne_U (fadd a b) c)
    (fadd_val_ne_O_of_ne_zero hsum)
    (add_ne_U (fmul a c) (fmul b c))
    Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred

theorem fleft_distrib_generic (a b c : Coordinate Φ.Γ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hb1 : b ≠ 1) (hs : fadd b c ≠ 0)
    (hsum : fadd (fmul a b) (fmul a c) ≠ 0) :
    fmul a (fadd b c) = fadd (fmul a b) (fmul a c) := by
  apply Coordinate.ext
  show coord_mul Φ.Γ a.1 (coord_add Φ.Γ b.1 c.1)
     = coord_add Φ.Γ (coord_mul Φ.Γ a.1 b.1) (coord_mul Φ.Γ a.1 c.1)
  exact coord_mul_left_distrib Φ.Γ a.1 b.1 c.1 a.isAtom b.isAtom c.isAtom
    a.on_l b.on_l c.on_l
    (val_ne_O_of_ne_zero ha) (val_ne_O_of_ne_zero hb) (val_ne_O_of_ne_zero hc)
    a.ne_U b.ne_U c.ne_U
    (fun h => hbc (Coordinate.ext h))
    (fadd_val_ne_O_of_ne_zero hs) (add_ne_U b c)
    (fmul_val_ne_O_of_ne_zero ha hb) (mul_ne_U a b)
    (fmul_val_ne_O_of_ne_zero ha hc) (mul_ne_U a c)
    (fun h => hbc (fmul_left_cancel a b c (val_ne_O_of_ne_zero ha)
      (Coordinate.ext h)))
    (fmul_val_ne_O_of_ne_zero ha hs)
    (mul_ne_U a (fadd b c))
    (fadd_val_ne_O_of_ne_zero hsum)
    (add_ne_U (fmul a b) (fmul a c))
    (fun h => hb1 (Coordinate.ext h))
    Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred

end Coordinate

end Foam.Bridges

#print axioms Foam.Bridges.Coordinate.fright_distrib_generic
#print axioms Foam.Bridges.Coordinate.fleft_distrib_generic
