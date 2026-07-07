import Mathlib.Order.ModularLattice
import Mathlib.Order.CompactlyGenerated.Basic

/-!
# The matroid stratum — camp one of the `pointSystem_exists` ascent

Every route up Veblen–Young walks on four facts about atoms in a modular
compactly generated lattice, and none of them mention the frame:

* `covBy_sup_atom` — joining a fresh atom is one step exactly: `x ⋖ x ⊔ p`
  (modularity's diamond, specialized to `⊥ ⋖ p`);
* `atom_exchange` — the Steinitz exchange: if `p` arrives inside `x ⊔ b` but
  not inside `x`, then `b` is inside `x ⊔ p` (the covering forces
  `x ⊔ p = x ⊔ b`).  This is the projective-geometry workhorse: it makes the
  atoms a matroid, and closure a rank function;
* `isCompactElement_of_isAtom` — atoms are compact in a compactly generated
  lattice (a point is finitely reachable);
* `AtomBasis` / `atomBasis_exists` — a maximal independent set of atoms with
  join `⊤` (Mathlib's `exists_sSupIndep_of_sSup_atoms_eq_top`, bundled), and
  `AtomBasis.exists_finset_support` — every atom lies below a *finite* join
  of basis atoms: the coordinate vector of a point will have finite support,
  which is why the eventual `V` is `B →₀ D` and the limit carries
  obligations, not information (`held_determines`, one stratum down).
-/

namespace Foam.Bridges

universe u

variable {L : Type u}

section Modular

variable [Lattice L] [OrderBot L] [IsModularLattice L]

omit [IsModularLattice L] in
theorem inf_eq_bot_of_atom_not_le {p x : L} (hp : IsAtom p) (hpx : ¬ p ≤ x) :
    p ⊓ x = ⊥ := by
  rcases (hp.le_iff.mp inf_le_left) with h | h
  · exact h
  · exact absurd (h ▸ inf_le_right) hpx

theorem covBy_sup_atom {p x : L} (hp : IsAtom p) (hpx : ¬ p ≤ x) :
    x ⋖ x ⊔ p := by
  have h1 : p ⊓ x ⋖ p := by
    rw [inf_eq_bot_of_atom_not_le hp hpx]
    exact hp.bot_covBy
  have h2 := covBy_sup_of_inf_covBy_left h1
  rwa [sup_comm] at h2

theorem atom_exchange {p b x : L} (hb : IsAtom b)
    (hle : p ≤ x ⊔ b) (hpx : ¬ p ≤ x) : b ≤ x ⊔ p := by
  by_cases hbx : b ≤ x
  · exact absurd (hle.trans (sup_le le_rfl hbx)) hpx
  have hcov : x ⋖ x ⊔ b := covBy_sup_atom hb hbx
  have hlt : x < x ⊔ p := left_lt_sup.mpr hpx
  have hle2 : x ⊔ p ≤ x ⊔ b := sup_le le_sup_left hle
  have heq : x ⊔ p = x ⊔ b :=
    (lt_or_eq_of_le hle2).resolve_left (hcov.2 hlt)
  exact le_sup_right.trans heq.ge

end Modular

section Compact

variable [CompleteLattice L] [IsCompactlyGenerated L]

theorem isCompactElement_of_isAtom {p : L} (hp : IsAtom p) :
    IsCompactElement p := by
  obtain ⟨s, hsc, hssup⟩ := IsCompactlyGenerated.exists_sSup_eq p
  have h : ∃ c ∈ s, c ≠ ⊥ := by
    by_contra h
    exact hp.1 (by rw [← hssup]; exact sSup_eq_bot.mpr (by simpa using h))
  obtain ⟨c, hcs, hc⟩ := h
  have hcp : c ≤ p := hssup ▸ le_sSup hcs
  have hce : c = p := (hp.le_iff.mp hcp).resolve_left hc
  exact hce ▸ hsc c hcs

end Compact

structure AtomBasis (L : Type u) [CompleteLattice L] where
  carrier : Set L
  indep : sSupIndep carrier
  spans : sSup carrier = ⊤
  atom : ∀ ⦃b⦄, b ∈ carrier → IsAtom b

section Basis

variable [CompleteLattice L] [IsModularLattice L] [ComplementedLattice L]
  [IsCompactlyGenerated L]

theorem atomBasis_exists : Nonempty (AtomBasis L) := by
  obtain ⟨s, h1, h2, h3⟩ :=
    exists_sSupIndep_of_sSup_atoms_eq_top (sSup_atoms_eq_top (α := L))
  exact ⟨⟨s, h1, h2, h3⟩⟩

end Basis

theorem AtomBasis.exists_finset_support [CompleteLattice L] [IsCompactlyGenerated L]
    (B : AtomBasis L) {p : L} (hp : IsAtom p) :
    ∃ t : Finset L, ↑t ⊆ B.carrier ∧ p ≤ t.sup id := by
  have hc := isCompactElement_of_isAtom hp
  rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup] at hc
  exact hc B.carrier (by rw [B.spans]; exact le_top)

end Foam.Bridges

/-- info: 'Foam.Bridges.inf_eq_bot_of_atom_not_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.inf_eq_bot_of_atom_not_le

/-- info: 'Foam.Bridges.covBy_sup_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.covBy_sup_atom

/-- info: 'Foam.Bridges.atom_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.atom_exchange

/-- info: 'Foam.Bridges.isCompactElement_of_isAtom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.isCompactElement_of_isAtom

/-- info: 'Foam.Bridges.atomBasis_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.atomBasis_exists

/-- info: 'Foam.Bridges.AtomBasis.exists_finset_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foam.Bridges.AtomBasis.exists_finset_support
