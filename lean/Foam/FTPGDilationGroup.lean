/-
# Dilation as a typed carrier (s148)

This file lands the carrier type `Dilation Γ` for the multiplicative
dilation family σ_c, completing the +1-operator move named in the
README's §IV (locate what is substrate-implicit-but-functioning; name
it) at the FTPG mul-assoc location.

## Background

The project's existing `dilation_ext Γ c` (FTPGDilation.lean) is the σ_c
function for off-l witnesses. The structural fact that the σ-family is
closed under composition — and hence forms a group whose operation is
function composition — has been *implicit* throughout the FTPG work but
never expressed at the type level. Without the carrier type, "the
σ-family is a group" isn't a statable theorem; every closure-fact has to
be re-derived as a specific point-by-point equation, producing the
circular content found by s142/s146/s148 at `dilation_compose_at_beta`.

See `lean/CLAUDE.md`'s "s148 refinement: mul-assoc as non-trivial loop
in the recognition-bundle" for the recognition-walk that motivates this
file. Operationally: the carrier type lets "the σ-family is closed under
composition" become a statable structural theorem (the substantive
remaining content of mul-assoc), and once it lands `coord_mul_assoc`
follows in one line from `Group.mul_assoc` (or `Monoid.mul_assoc`)
applied to dilations as group elements.

## Scope of this file

**Landed here:**

* The carrier type `Dilation Γ` bundling toFun with the *minimal*
  structural fields (fixes O, fixes m off l, maps l to l).
* The identity instance.

**Deliberately deferred (next-walk design decisions):**

* **Field-set expansion for Monoid closure.** Function-composition of
  two `Dilation Γ` does not preserve the three minimal fields without
  atom-preservation, plane-preservation, and several "off-X stays
  off-X" invariants. The right *minimal sufficient* field-set for a
  clean `Monoid (Dilation Γ)` instance is a design choice. Candidates:
  (a) add `preserves_atoms`, `preserves_plane`, `preserves_off_l`,
  `preserves_off_m`, `preserves_directions` as explicit fields;
  (b) reformulate `toFun` as an order-isomorphism `L ≃o L` and derive
  the preserves-properties from order-iso properties.

* **Packaging σ_c as a `Dilation Γ`.** The existing `dilation_ext Γ c`
  is defined for off-l witnesses; its action on l-atoms is via the
  separate `coord_mul` definition. Building the canonical `σ Γ c hc
  : Dilation Γ` requires a combined function reconciling the on-l vs
  off-l asymmetry. Mostly mechanical once the field-set is settled.

* **σ-family closure under composition.** The substantive geometric
  content (= the open mul-assoc residue). Once the Monoid (or Group)
  instance is in place, this is the named target: show the map
  `(c : L on l) ↦ σ Γ c : Dilation Γ` is a monoid homomorphism from
  `(L on-l atoms, coord_mul)` to `(Dilation Γ, composition)`. The
  predicted bin-1 path is a dimensional lift via the height-≥-4 R
  witness (exit A in the s142 framing).

## How `coord_mul_assoc` follows downstream

Once all three deferred items land, `coord_mul_assoc` reduces to:

```
example : coord_mul Γ a (coord_mul Γ b c) = coord_mul Γ (coord_mul Γ a b) c := by
  -- coord_mul a b = σ_b(a), so:
  --   LHS = σ_{σ_c(b)}(a)
  --   RHS = σ_c(σ_b(a)) = (σ_c ∘ σ_b)(a)
  -- By σ-family closure under composition: σ_c ∘ σ_b = σ_{σ_c(b)} as
  -- Dilation Γ elements. So both sides agree as values at a.
  sorry
```

— a thin algebraic assembly, with the substantive content concentrated
in the σ-family closure theorem (where Desargues lives via the R-lift).
-/

import Foam.FTPGDilation

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## The dilation carrier type -/

/-- A **dilation** of the projective plane π = O⊔U⊔V relative to a
    coordinate system Γ bundles the minimal structural properties of a
    classical projective-geometry dilation:

    * **Fixes the origin O.** O is sent to itself.
    * **Maps l-atoms to l-atoms.** The line l = O⊔U is preserved
      setwise on atoms.
    * **Fixes m-atoms off l.** Atoms on m = U⊔V that are not on l
      are pointwise fixed.

    These three fields are the *minimal* structural commitment. A
    `Monoid (Dilation Γ)` instance (composition + identity) requires
    additional preservation invariants on `toFun`; their inclusion is a
    design choice deferred to the next walk (see file docstring).

    Classical instances: the identity map (`Dilation.id`); and (after
    the deferred packaging work) the σ_c family `dilation_ext Γ c`
    extended to handle on-l atoms via `coord_mul`. -/
structure Dilation (Γ : CoordSystem L) where
  /-- The action of the dilation on lattice elements. -/
  toFun : L → L
  /-- Dilations fix the origin O. -/
  fixes_O : toFun Γ.O = Γ.O
  /-- Dilations map l-atoms to l-atoms. -/
  maps_l_to_l : ∀ P : L, IsAtom P → P ≤ Γ.O ⊔ Γ.U → toFun P ≤ Γ.O ⊔ Γ.U
  /-- Dilations fix m-atoms that are not on l. -/
  fixes_m_off_l : ∀ P : L, IsAtom P → P ≤ Γ.U ⊔ Γ.V → ¬ P ≤ Γ.O ⊔ Γ.U →
    toFun P = P

namespace Dilation

variable {Γ : CoordSystem L}

/-! ## The identity dilation -/

/-- The identity map is a dilation. All structural fields are
    trivially satisfied: O is fixed, l-atoms map to themselves (and
    hence to l-atoms), and m-atoms off l map to themselves. -/
def id (Γ : CoordSystem L) : Dilation Γ where
  toFun := _root_.id
  fixes_O := rfl
  maps_l_to_l := fun _ _ h => h
  fixes_m_off_l := fun _ _ _ _ => rfl

end Dilation

end Foam.FTPGExplore
