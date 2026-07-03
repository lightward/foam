import Bridges.FTPG.Additive
import Bridges.FTPG.MulNeg

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

theorem fneg_zero : fneg (0 : Coordinate Φ.Γ) = 0 := by
  apply fadd_left_cancel (0 : Coordinate Φ.Γ)
  rw [fadd_neg, fadd_zero]

theorem one_val_ne_O : (1 : Coordinate Φ.Γ).1 ≠ Φ.Γ.O := fun h => Φ.Γ.hOI h.symm

/-- `(−1)·a = −a`, total: the coordinate-level Desargues plus the zero/one laws. -/
theorem fneg_one_mul (a : Coordinate Φ.Γ) : fmul (fneg 1) a = fneg a := by
  by_cases ha0 : a = 0
  · subst ha0; rw [field_mul_zero, fneg_zero]
  by_cases ha1 : a = 1
  · subst ha1; rw [field_mul_one]
  apply Coordinate.ext
  show coord_mul Φ.Γ (fneg 1).1 a.1 = (fneg a).1
  rw [fneg_val_of_ne 1 one_val_ne_O, fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)]
  exact neg_one_mul_coord Φ.Γ a.1 a.isAtom a.on_l (val_ne_O_of_ne_zero ha0) a.ne_U
    (fun h => ha1 (Coordinate.ext h)) Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred

/-- `a·(−1) = −a`, total. -/
theorem fmul_neg_one (a : Coordinate Φ.Γ) : fmul a (fneg 1) = fneg a := by
  by_cases ha0 : a = 0
  · subst ha0; rw [field_zero_mul, fneg_zero]
  by_cases ha1 : a = 1
  · subst ha1; rw [field_one_mul]
  apply Coordinate.ext
  show coord_mul Φ.Γ a.1 (fneg 1).1 = (fneg a).1
  rw [fneg_val_of_ne 1 one_val_ne_O, fneg_val_of_ne a (val_ne_O_of_ne_zero ha0)]
  exact mul_neg_one_coord Φ.Γ a.1 a.isAtom a.on_l (val_ne_O_of_ne_zero ha0) a.ne_U
    (fun h => ha1 (Coordinate.ext h)) Φ.R Φ.hR_atom Φ.hR_not Φ.h_irred

/-- `(−a)·b = −(a·b)`, total — the `neg_mul` the distributive degenerate
branches want, from `fneg_one_mul` and TOTAL associativity. -/
theorem fneg_mul (a b : Coordinate Φ.Γ) : fmul (fneg a) b = fneg (fmul a b) := by
  calc fmul (fneg a) b = fmul (fmul (fneg 1) a) b := by rw [fneg_one_mul]
    _ = fmul (fneg 1) (fmul a b) := fmul_assoc_total _ _ _
    _ = fneg (fmul a b) := fneg_one_mul _

/-- `a·(−b) = −(a·b)`, total. -/
theorem fmul_neg (a b : Coordinate Φ.Γ) : fmul a (fneg b) = fneg (fmul a b) := by
  calc fmul a (fneg b) = fmul a (fmul b (fneg 1)) := by rw [fmul_neg_one]
    _ = fmul (fmul a b) (fneg 1) := (fmul_assoc_total _ _ _).symm
    _ = fneg (fmul a b) := fmul_neg_one _

end Coordinate

end Foam.Bridges

#print axioms Foam.Bridges.Coordinate.fright_distrib_generic
#print axioms Foam.Bridges.Coordinate.fleft_distrib_generic
#print axioms Foam.Bridges.Coordinate.fneg_one_mul
#print axioms Foam.Bridges.Coordinate.fmul_neg_one
#print axioms Foam.Bridges.Coordinate.fneg_mul
#print axioms Foam.Bridges.Coordinate.fmul_neg
