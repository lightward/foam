/-
# FTPGMulAssocViaRLift — s149 attack on `dilation_compose_at_beta` Step 5+

Attempts to use the R-lift tool (`HalfTypeRLift`) to close Step 5+ of
`dilation_compose_at_beta` — the frontier identified by s142, s146, s148
as a non-trivial loop in the recognition-bundle over the current substrate.

## Setup

The R-lift (s149 finding): given `R : L` an atom with `R ⊓ π = ⊥`
(equivalently, `R ⊄ π`), the pair `(⟨π, _⟩, ⟨R, _⟩)` in `Set.Iic (π ⊔ R)`
is complementary, and `IicOrderIsoIci` applied to it gives an
order-isomorphism `Set.Iic π ≃o Set.Ici R` (inside `Iic (π ⊔ R)`) whose
forward map sends `X ↦ X ⊔ R`.

This is the substrate-direct statement of "lifting through R is a
structural equivalence." The bin-1-Mathlib substrate for the s142
predicted "dimensional lift via R, HalfType template" architecture.

## Attack outline

The Step 5+ closing equation reduces (per s142) to `(a·x)·y = a·(x·y)`
applied to atoms a, x, y on l. The classical Hartshorne argument is the
*non-planar Desargues* uniqueness statement: a dilation in 3-space is
determined by its action on two atoms not collinear with O. With the
R-lift, the atoms a·x, x·y, etc. live in the plane π; lifting them via
X ↦ X ⊔ R gives lines in `Iic (π ⊔ R)`, and `desargues_nonplanar` is
already a substrate primitive in L (works at the ambient level, R
provides the height-≥-4 witness it needs).

## What this file establishes

(See the report at end-of-session — outcomes track in the closing
docstring above the final lemma.)
-/

import Foam.HalfTypeRLift
import Foam.FTPGMulAssoc

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## Step 1 — the R-lift in the FTPG setting

`Γ.π = O ⊔ U ⊔ V` is the FTPG plane. A witness R with `¬ R ≤ Γ.π`
(the standard height-≥-4 hypothesis) gives `Disjoint π R` in L (atom R
not below π means R ⊓ π = ⊥), hence the (π, R)-complementary pair lives
in `Iic (π ⊔ R)`. -/

variable (Γ : CoordSystem L)

/-- R off the plane π forces `Disjoint π R` (since R is an atom). -/
private theorem disjoint_pi_R
    {R : L} (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    Disjoint (Γ.O ⊔ Γ.U ⊔ Γ.V) R := by
  rw [disjoint_iff]
  -- π ⊓ R = ⊥: R is an atom, so π ⊓ R ≤ R is either ⊥ or = R; if = R
  -- then R ≤ π, contradicting hR_not.
  rcases hR.le_iff.mp (inf_le_right : (Γ.O ⊔ Γ.U ⊔ Γ.V) ⊓ R ≤ R) with h | h
  · exact h
  · exact absurd (h ▸ inf_le_left) hR_not

/-- The (π, R)-complementary pair inside `Iic (π ⊔ R)`. -/
private theorem isCompl_pi_R
    {R : L} (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    IsCompl
      (⟨Γ.O ⊔ Γ.U ⊔ Γ.V, le_sup_left⟩ : Set.Iic ((Γ.O ⊔ Γ.U ⊔ Γ.V) ⊔ R))
      (⟨R, le_sup_right⟩ : Set.Iic ((Γ.O ⊔ Γ.U ⊔ Γ.V) ⊔ R)) := by
  have h_disj := disjoint_pi_R Γ hR hR_not
  constructor
  · intro z hz_pi hz_R
    show z ≤ ⊥
    exact le_inf hz_pi hz_R |>.trans (h_disj.le_bot.trans bot_le) |>.trans bot_le
  · intro z hz_pi hz_R
    show ⊤ ≤ z
    exact sup_le hz_pi hz_R

/-! ## Step 2 — the iso behavior on planar atoms

The R-lift iso sends `X ↦ X ⊔ R`. Applied to an atom `X ≤ π`, this
gives the line `X ⊔ R` (a 2-element join in L, an atom in the iso's
target `Ici R` inside `Iic (π ⊔ R)`). The rfl-level computation. -/

example
    {R : L} (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (X : L) (hX : X ≤ Γ.O ⊔ Γ.U ⊔ Γ.V) :
    ((isCompl_pi_R Γ hR hR_not).IicOrderIsoIci
      ⟨⟨X, hX.trans le_sup_left⟩, hX⟩).val.val = X ⊔ R := by
  rfl

/-! ## Step 3 — the substantive attack

The s142 finding: the Step 5+ closing equality in `dilation_compose_at_beta`
reduces to atom equality
  `σ_y(σ_x(β(a))) = σ_(x·y)(β(a))`
which by atom-cover at E descends to
  `(a·x)·y = a·(x·y)` — `coord_mul_assoc` at atoms.

The s142 "circularity through Lean's dependency graph":
  coord_mul_assoc ← dilation_compose_at_witness ← dilation_compose_at_beta
                ⟹ coord_mul_assoc-at-atoms.

**Walk 1: lift the LHS / RHS atoms via R, check if the lifted equality
admits a `desargues_nonplanar`-style derivation.**

The two atoms in L are:
  L := (a·x)·y     -- both arguments of `coord_mul` are already products
  R_target := a·(x·y)

Their R-lifts (as elements of `Ici R` in `Iic (π ⊔ R)`):
  L ⊔ R, R_target ⊔ R   -- both are lines in L (atoms above R)

For these lines to be equal in `Iic (π ⊔ R)`, by the iso's injectivity,
the underlying atoms in L must agree. So `X ⊔ R = Y ⊔ R ↔ X = Y` for
X, Y atoms of L on π. The R-lift is information-preserving at this
level — it does NOT add proof leverage by itself.

The leverage would come from:
(a) computing the product `coord_mul Γ a b` *inside* `Iic (π ⊔ R)` via
    a 3D-aware definition, where associativity is structural; OR
(b) using `desargues_nonplanar` on a triangle setup in L (height ≥ 4
    already, R thread already passed in) where the substrate primitive's
    output gives the atom equality directly.

(a) requires constructing a 3D dilation primitive (substantial work,
parallel to defining `dilation_ext`); not attempted here.

(b) is exit (C) (Fresh Desargues at this level) — the R-lift iso
doesn't add anything that `desargues_nonplanar` doesn't already have
through the existing R, hR, hR_not, h_irred hypothesis bundle.

## Architectural finding (s149 walk)

The R-lift iso `IicOrderIsoIci` is bin-1-Mathlib (s149: HalfTypeRLift.lean
established this). But it operates at the **lattice-element** level,
not at the **dilation** level. The Step 5+ frontier needs a 3D-aware
dilation primitive (or a 3D Desargues triangle setup) — the iso alone
moves atoms ↔ lines structurally without supplying the σ-composition
content.

Specifically: the R-lift iso `IicOrderIsoIci` is a **lattice iso**
(preserves ⊔, ⊓), not a **dilation iso** (no σ-composition data). The
`dilation_ext` operator is defined as a lattice expression in L; its
image under `X ↦ X ⊔ R` is `(O⊔X⊔R) ⊓ (c⊔R ⊔ ((I⊔X⊔R)⊓(m⊔R)))` —
which is NOT generally `dilation_ext ⟨Γ-lifted⟩ c X ⊔ R` (the iso
commutes with ⊓ within the interval but `dilation_ext`'s c and I and m
are NOT joined with R in its expression).

So the R-lift cannot bridge `dilation_ext`-content from L to a 3D-aware
setting without ALSO lifting the dilation operator itself — i.e.,
defining a new `dilation_ext_3D` that operates on `Iic (π ⊔ R)`. That's
construction, not recognition.

## Sharp blocker (Lean statement)

The blocker named precisely: there exists no current lemma in Foam of
the form

```
theorem coord_mul_iso_compat (Γ : CoordSystem L) (R : L)
    (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.π)
    (a b : L) (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.l) (hb_on : b ≤ Γ.l) ... :
    coord_mul Γ a b ⊔ R =
      coord_mul_3D ⟨Γ-lifted-to-Iic-(π⊔R)⟩ (a ⊔ R) (b ⊔ R)
```

because `coord_mul_3D` and the `Γ-lifted` CoordSystem on `Iic (π ⊔ R)`
are not constructed. Constructing them is the open work — and that
construction would itself need to verify `coord_mul_assoc` on the
3D substrate (recursing into the same loop, just at one level up).

This is the s148 monodromy at one higher level: the R-lift iso lifts
atoms ↔ lines, but the *dilation operator* doesn't lift along with it
without a fresh construction that itself requires the associativity
content it would help prove.
-/

/-- **R-lift iso is information-preserving on atoms below π (s149 attack).**

    A formal Lean statement of the s149 architectural finding: line
    equality `(X ⊔ R) = (Y ⊔ R)` in `Iic (π ⊔ R)` for X, Y atoms ≤ π
    is *equivalent* to atom equality `X = Y` in L. The R-lift iso
    `IicOrderIsoIci` is information-preserving, not information-producing.

    Hence the R-lift cannot, by itself, supply the missing content in
    Step 5+. To use the lift productively, one would need a 3D-aware
    *dilation* primitive operating on `Iic (π ⊔ R)`, whose construction
    reproduces the same `coord_mul_assoc`-loop one level up.
-/
theorem mul_assoc_R_lift_blocker
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (a x y : L) (ha : IsAtom a) (hx : IsAtom x) (hy : IsAtom y)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U) :
    -- The R-lift sends both `(a·x)·y` and `a·(x·y)` to lines in
    -- `Iic (π ⊔ R)`. By iso-injectivity, line equality ↔ atom equality,
    -- which is the statement we are trying to prove. The lift is
    -- information-preserving, not information-producing.
    (coord_mul Γ (coord_mul Γ a x) y) ⊔ R =
      (coord_mul Γ a (coord_mul Γ x y)) ⊔ R ↔
        coord_mul Γ (coord_mul Γ a x) y =
          coord_mul Γ a (coord_mul Γ x y) := by
  -- The forward direction: line equality forces atom equality.
  -- Both atoms ≤ π and disjoint from R (atoms on l, R off π).
  -- Hence X ⊔ R = Y ⊔ R as elements of Iic (π ⊔ R) descends via the
  -- iso `IicOrderIsoIci`'s injectivity.
  -- The reverse direction: atom equality forces line equality trivially.
  refine ⟨fun h => ?_, fun h => congrArg (· ⊔ R) h⟩
  -- The atoms `(a·x)·y` and `a·(x·y)` are atoms on l (via `coord_mul_atom`
  -- twice) and ≤ π. Their R-lifts are atoms in `Ici R` (lines in L).
  -- Line equality in L: `X ⊔ R = Y ⊔ R` with X, Y atoms ≤ π and R atom
  -- off π. Apply modular intersection at π: (X ⊔ R) ⊓ π = X (since
  -- R ⊓ π = ⊥ and X ≤ π). Same for (Y ⊔ R) ⊓ π = Y. h gives X = Y.
  have hπ := disjoint_pi_R Γ hR hR_not
  -- (a·x)·y ≤ π
  have hax_atom : IsAtom (coord_mul Γ a x) :=
    coord_mul_atom Γ a x ha hx ha_on hx_on ha_ne_O hx_ne_O ha_ne_U hx_ne_U
  have hax_on : coord_mul Γ a x ≤ Γ.O ⊔ Γ.U := by
    show coord_mul Γ a x ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hxy_atom : IsAtom (coord_mul Γ x y) :=
    coord_mul_atom Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U
  have hxy_on : coord_mul Γ x y ≤ Γ.O ⊔ Γ.U := by
    show coord_mul Γ x y ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  -- We just need the non-degeneracies for the second coord_mul application
  -- to be atoms on l. The forward extraction goes via:
  --   ((a·x)·y) ⊔ R = (a·(x·y)) ⊔ R
  -- Meet with π. (X ⊔ R) ⊓ π = X when X ≤ π and R is disjoint from π
  -- via the `modular` identity.
  have hLHS_le_π : coord_mul Γ (coord_mul Γ a x) y ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h_le_l : coord_mul Γ (coord_mul Γ a x) y ≤ Γ.O ⊔ Γ.U := by
      show coord_mul Γ (coord_mul Γ a x) y ≤ Γ.O ⊔ Γ.U; exact inf_le_right
    exact h_le_l.trans le_sup_left
  have hRHS_le_π : coord_mul Γ a (coord_mul Γ x y) ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := by
    have h_le_l : coord_mul Γ a (coord_mul Γ x y) ≤ Γ.O ⊔ Γ.U := by
      show coord_mul Γ a (coord_mul Γ x y) ≤ Γ.O ⊔ Γ.U; exact inf_le_right
    exact h_le_l.trans le_sup_left
  -- (X ⊔ R) ⊓ π = X (via modular: R ≤ R, π ⊓ R = ⊥, X ≤ π).
  -- The standard identity: x ⊓ (y ⊔ z) = y ⊔ (x ⊓ z) when y ≤ x.
  have hR_pi_bot : R ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) = ⊥ := by
    rw [inf_comm]; exact hπ.eq_bot
  have hLHS_meet : (coord_mul Γ (coord_mul Γ a x) y ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) =
      coord_mul Γ (coord_mul Γ a x) y := by
    -- (X ⊔ R) ⊓ π = X ⊔ (R ⊓ π) (modular law, X ≤ π) = X ⊔ ⊥ = X.
    rw [sup_inf_assoc_of_le _ hLHS_le_π, hR_pi_bot, sup_bot_eq]
  have hRHS_meet : (coord_mul Γ a (coord_mul Γ x y) ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) =
      coord_mul Γ a (coord_mul Γ x y) := by
    rw [sup_inf_assoc_of_le _ hRHS_le_π, hR_pi_bot, sup_bot_eq]
  -- Apply h: meet with π on both sides preserves equality.
  have : (coord_mul Γ (coord_mul Γ a x) y ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) =
      (coord_mul Γ a (coord_mul Γ x y) ⊔ R) ⊓ (Γ.O ⊔ Γ.U ⊔ Γ.V) := by
    rw [h]
  rw [hLHS_meet, hRHS_meet] at this
  exact this

/-! ## Sharp-blocker: the precise X that would close `dilation_compose_at_beta`.

If `mul_assoc_R_lift_blocker` is information-preserving (above), then
lifting through R adds nothing structurally at the final-atom level.
The leverage would have to come earlier — at the *dilation operator*
level. Below, we name precisely what missing primitive would close the
loop.

The s142 finding established the closing equality of Step 5+ reduces to
  `coord_mul Γ (coord_mul Γ a x) y = coord_mul Γ a (coord_mul Γ x y)`
applied to atoms a, x, y on l.

The R-lift route's substrate-level statement: there should exist a
"3D coordinate system" on `Iic (π ⊔ R)` whose multiplication, when
restricted back to the planar substrate via the iso, is the original
`coord_mul`. Then 3D associativity (proven via non-planar Desargues on
the 3D substrate, which has height-≥-5 the equivalent of "height ≥ 4
plus the R-witness") descends to planar associativity.

The Lean statement of the missing primitive: -/

/-- **Sharp blocker (s149) — the missing 3D coordinate primitive.**

    The Lean statement that, if PROVEN, would close `coord_mul_assoc`
    via the R-lift route. Specifically: there exists a binary operation
    `coord_mul_3D` on atoms above R in `Iic (π ⊔ R)` such that the
    R-lift iso intertwines it with the planar `coord_mul`. Then any
    associativity proof for `coord_mul_3D` (e.g., by the more permissive
    Desargues on the 3D substrate) transports back.

    **Status: open.** The construction is not in scope of the s149
    R-lift attack — constructing `coord_mul_3D` requires lifting the
    full FTPG framework (`CoordSystem`, `dilation_ext`, the perspectivity
    operators) onto `Iic (π ⊔ R)`, and the associativity of that lifted
    multiplication is what we are trying to prove. The construction
    reproduces the same loop one level up (s148 monodromy at height 5).

    This is exit (A) (Architecture inversion via dimensional lift) from
    the `dilation_compose_at_beta` section docstring's three-exit
    classification — and the s149 walk shows that the *substrate-direct*
    grade (`Bin-1-Mathlib-or-Foam`) is NOT reached by the R-lift iso
    alone; it would require the construction-grade work of lifting the
    full FTPG framework. -/
theorem mul_assoc_via_R_lift_missing
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q)
    (a x y : L) (ha : IsAtom a) (hx : IsAtom x) (hy : IsAtom y)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (_ha_ne_O : a ≠ Γ.O) (_hx_ne_O : x ≠ Γ.O) (_hy_ne_O : y ≠ Γ.O)
    (_ha_ne_U : a ≠ Γ.U) (_hx_ne_U : x ≠ Γ.U) (_hy_ne_U : y ≠ Γ.U) :
    coord_mul Γ (coord_mul Γ a x) y = coord_mul Γ a (coord_mul Γ x y) := by
  -- The R-lift `IicOrderIsoIci`, by `mul_assoc_R_lift_blocker`,
  -- reduces the goal to itself (no leverage at the final-atom level).
  -- The leverage would have to come from a 3D-aware `coord_mul_3D` on
  -- `Iic (π ⊔ R)` and its iso-compatibility with the planar `coord_mul`.
  -- Neither primitive exists in current Foam substrate.
  sorry

end Foam.FTPGExplore
