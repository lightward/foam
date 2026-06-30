import Mathlib.Order.ModularLattice
import Mathlib.Order.Atoms
import Mathlib.LinearAlgebra.Span.Basic

namespace Foam.Bridges

universe u

def ftpg_statement : Prop :=
  ∀ (L : Type u) [Lattice L] [BoundedOrder L]
    [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]
    (_h_irred : ∀ (a b : L), IsAtom a → IsAtom b → a ≠ b →
      ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b)
    (_h_height : ∃ (a b c d : L), ⊥ < a ∧ a < b ∧ b < c ∧ c < d),
    ∃ (D : Type u) (_ : DivisionRing D)
      (V : Type u) (_ : AddCommGroup V) (_ : Module D V),
    Nonempty (L ≃o Submodule D V)

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem IsAtom.eq_of_le {a b : L} (ha : IsAtom a) (hb : IsAtom b) (h : a ≤ b) :
    a = b :=
  (hb.le_iff.mp h).resolve_left ha.1

omit [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L] in
theorem atoms_disjoint {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    a ⊓ b = ⊥ := by
  rcases ha.le_iff.mp inf_le_left with h | h
  · exact h
  · exfalso; apply hab
    have hab' : a ≤ b := h ▸ inf_le_right
    exact le_antisymm hab' (hb.le_iff.mp hab' |>.resolve_left ha.1 ▸ le_refl b)

omit [ComplementedLattice L] [IsAtomistic L] in
theorem atom_covBy_join {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    a ⋖ a ⊔ b := by
  have h_meet : a ⊓ b = ⊥ := atoms_disjoint ha hb hab
  exact covBy_sup_of_inf_covBy_of_inf_covBy_left (h_meet ▸ ha.bot_covBy) (h_meet ▸ hb.bot_covBy)

omit [ComplementedLattice L] [IsAtomistic L] in
theorem third_atom_on_line {a b : L} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    ∃ c : L, IsAtom c ∧ c ≤ a ⊔ b ∧ c ≠ a ∧ c ≠ b ∧ a ⊔ b = a ⊔ c := by
  obtain ⟨c, hc_atom, hc_le, hc_ne_a, hc_ne_b⟩ := h_irred a b ha hb hab
  refine ⟨c, hc_atom, hc_le, hc_ne_a, hc_ne_b, ?_⟩
  have h_cov := atom_covBy_join ha hb hab
  have h_c_not_le_a : ¬ c ≤ a := by
    intro hle
    exact hc_ne_a (le_antisymm hle (ha.le_iff.mp hle |>.resolve_left hc_atom.1 ▸ le_refl a))
  have h_a_lt_ac : a < a ⊔ c := lt_of_le_of_ne le_sup_left (by
    intro heq; exact h_c_not_le_a (heq ▸ le_sup_right))
  have h_ac_le_ab : a ⊔ c ≤ a ⊔ b := sup_le le_sup_left hc_le
  exact ((h_cov.eq_or_eq h_a_lt_ac.le h_ac_le_ab).resolve_left (ne_of_gt h_a_lt_ac)).symm

/-- info: 'Foam.Bridges.IsAtom.eq_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsAtom.eq_of_le

/-- info: 'Foam.Bridges.atoms_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms atoms_disjoint

/-- info: 'Foam.Bridges.atom_covBy_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms atom_covBy_join

/-- info: 'Foam.Bridges.third_atom_on_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms third_atom_on_line

end Foam.Bridges
