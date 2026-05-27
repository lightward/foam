/-
# FTPGGaugeFigureLayer — buffer/working-space layer-typing with chirality

## The recognition this file lands

`FTPGMulAssocCrossings.lean` names the asymmetric collapse at the
inverse-pair (y = coord_inv x): *"RHS reduces, LHS persists. The
asymmetric collapse IS gauge 3's layer-distinction visible at this
internal configuration."* The file sees a layer-distinction. It doesn't
yet name *which two layers*, *how their roles are assigned*, or *whether
the assignment can flip*. This file types those.

## The two layers

* **working_space** — content evaluates forward; completes in place.
  Example at g3_asymmetric: σ_{x · x⁻¹}(β(a)) reduces via
  `coord_mul_right_inv` + `dilation_ext_identity` to β(a). Fires forward.
* **buffer** — content is held as a *vacuum-shape* (in the spiral-circuit
  sense; see Lightward AI's `spiral-circuit.md`: "a spiral circuit
  exhibiting stable recursion won't return the input, it'll create a
  vacuum in the shape of the first input"). Catches what the working
  space couldn't carry forward. Fires (vacuum-fill event) when matching
  content arrives.

## Chirality: role-assignment is gauge

The asymmetry between the two structural sides is real. The *assignment*
of which side plays which role is a **chirality choice** — like primary
handedness in even-limbed creatures. Structurally arbitrary; operationally
required. (Compare the removed `README.md` passage: *"the chirality is
gauge (all equivalent) and structural (one must be selected)."* Compare
also `FTPGDilationGroup.lean`'s left-to-right composition convention,
chosen for σ-family compatibility — the project's operative chirality.)

Classical FTPG resolves the chirality *statically* via holonomy collapse
(the dagger smooths the asymmetry). Foam's no-dagger setting requires
the chirality to be **dynamically switchable** — content can flip sides
when one side gets stuck. `CellChirality.flip` is the type-level handle
for that primitive.

## What this file contributes

* `CellLayer` — the two structural roles (`working_space`, `buffer`)
* `CellChirality` — role-assignment as a typed pair, with `.canonical`
  and `.flip` operations
* `inverse_pair_expr_lhs` / `inverse_pair_expr_rhs` — the two lattice
  expressions at g3_asymmetric, named *positionally* (no role baked in)
* `vacuum_fill_event_at_inverse_pair` — the equation between them,
  chirality-invariant (lattice equality is symmetric, holds regardless
  of which role each side is assigned)

No new proofs. Recognition-grade typing of structure that
`FTPGMulAssocCrossings.lean`'s docstring already half-named, now with
chirality as choice-not-essence.
-/

import Foam.FTPGMulAssocCrossings

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## Layer roles -/

/-- The two structural roles a side of an asymmetric-cell equation can
    play in foam's dagger-free FTPG bridge.

    * `working_space` — forward-evaluating content; completes in place
    * `buffer` — held vacuum-shape; catches blocked content; fires on
      matching arrival

    These are the two layers `FTPGMulAssocCrossings.lean`'s docstring
    names ("gauge 3's layer-distinction"). -/
inductive CellLayer where
  | working_space
  | buffer
  deriving DecidableEq, Repr

/-! ## Chirality: the role-assignment as gauge -/

/-- The chirality of an asymmetric-cell equation: which side plays
    which role. The two roles must be distinct (a working_space *is*
    the complement of a buffer in this pairing). The assignment itself
    is chirality-arbitrary — both chiralities are equally valid;
    operating requires choosing one.

    `flip` exists because dynamic side-switching is the dagger-free
    analog of classical FTPG's static holonomy-collapse: when content
    can't complete on one side, the chirality can flip and the other
    side becomes the working space. -/
structure CellChirality where
  lhs_role : CellLayer
  rhs_role : CellLayer
  distinct : lhs_role ≠ rhs_role

namespace CellChirality

/-- The canonical chirality for the current static reading of
    `dilation_compose_at_beta_y_eq_coord_inv_x`: the
    inverse-pair-composition side (LHS) is buffer, the fired-side
    (RHS) is working_space. Reflects the "RHS reduces, LHS persists"
    observation in `FTPGMulAssocCrossings.lean`'s docstring. -/
def canonical : CellChirality where
  lhs_role := .buffer
  rhs_role := .working_space
  distinct := by decide

/-- Chirality-flip: swap the role assignment. The dynamic
    side-switching primitive. -/
def flip (c : CellChirality) : CellChirality where
  lhs_role := c.rhs_role
  rhs_role := c.lhs_role
  distinct := fun h => c.distinct h.symm

/-- Flip is an involution. -/
@[simp] theorem flip_flip (c : CellChirality) : c.flip.flip = c := rfl

/-- The two chiralities are flips of each other. -/
theorem flip_canonical_ne_canonical : canonical.flip ≠ canonical := by
  intro h
  have : (CellLayer.working_space : CellLayer) = CellLayer.buffer :=
    congrArg lhs_role h
  exact absurd this (by decide)

end CellChirality

/-! ## g3_asymmetric's two expressions, named positionally -/

/-- The LHS of `dilation_compose_at_beta_y_eq_coord_inv_x` as a
    standalone definition. Positional name — no role baked in.

    Structurally: `σ_{coord_inv x}(σ_x(β(a)))`. Under
    `CellChirality.canonical`, this side plays `buffer`. Under
    `canonical.flip`, this side plays `working_space`. -/
noncomputable def inverse_pair_expr_lhs (Γ : CoordSystem L) (x a : L) : L :=
  dilation_ext Γ (coord_inv Γ x) (dilation_ext Γ x ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)))

/-- The RHS of `dilation_compose_at_beta_y_eq_coord_inv_x` as a
    standalone definition. Positional name — no role baked in.

    Structurally: `σ_{coord_mul x (coord_inv x)}(β(a))`. Under
    `CellChirality.canonical`, this side plays `working_space`
    (reduces via `coord_mul_right_inv` + `dilation_ext_identity` to
    β(a)). Under `canonical.flip`, this side plays `buffer`. -/
noncomputable def inverse_pair_expr_rhs (Γ : CoordSystem L) (x a : L) : L :=
  dilation_ext Γ (coord_mul Γ x (coord_inv Γ x)) ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E))

/-! ## The vacuum-fill event

The equation between the two positional expressions. Holds
chirality-invariantly: lattice equality is symmetric, so the equation
is true regardless of which side is read as buffer and which as
working_space.

This is the same content as
`dilation_compose_at_beta_y_eq_coord_inv_x` (which is open as a named
candidate-`sorry`); re-typed here to make the layer-distinction
visible as Lean structure rather than only narrative. -/

/-- The vacuum-fill event at the inverse-pair: lhs-expression equals
    rhs-expression. Chirality-invariant. Body forwards to the existing
    named candidate-sorry. -/
theorem vacuum_fill_event_at_inverse_pair (Γ : CoordSystem L)
    (x a : L) (hx : IsAtom x) (ha : IsAtom a)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (ha_ne_O : a ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    inverse_pair_expr_lhs Γ x a = inverse_pair_expr_rhs Γ x a := by
  unfold inverse_pair_expr_lhs inverse_pair_expr_rhs
  exact dilation_compose_at_beta_y_eq_coord_inv_x Γ x a hx ha hx_on ha_on
    hx_ne_O ha_ne_O hx_ne_U ha_ne_U

end Foam.FTPGExplore
