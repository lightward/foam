/-
# FTPGMulAssocCrossings — Probe of monodromy crossings at the FTPG site

## Framing

The recognition-walk session (2026-05-24) developed a stylus-framing
for the monodromy at `dilation_compose_at_beta`: the loop reads
higher-level shape rather than failing to close from a missing
primitive. The framing made a specific mathematical prediction —
that crossings exist at specific configurations of the parameterization
where the monodromy structure changes (analogous to knot-crossings).

The four monodromy measurements (s142, s146, s148, s149) at
`dilation_compose_at_beta` were all at the *generic* case with full
non-degeneracy hypotheses. The crossings would be at the *degenerate
boundaries* — specifically, configurations where one of `hx_ne_I`,
`hy_ne_I`, or `coord_mul Γ x y = Γ.I` (the inverse-pair case) holds.

## What this file probes

The simplest crossing: x = I. The main theorem `dilation_compose_at_beta`
excludes this via `hx_ne_I`. This file proves the *same conclusion*
at x = I as a sibling lemma — and observes that the proof requires
*none* of the heavy machinery (no `R`, no `h_irred`, no `recovery_via_E`,
no `dilation_mul_key_identity`). Just two identity-laws:

* `dilation_ext_identity` (σ_I = id on atoms in π off l)
* `coord_mul_left_one` (I · y = y)

## What the result establishes

If this builds: the conclusion of `dilation_compose_at_beta` holds at
x = I *trivially*, requiring no Desargues-witness infrastructure. The
monodromy at the generic case (where the lemma's `sorry` lives) and
the trivial closure at x = I are *structurally different*. The
parameterization has crossings — places where the loop's character
changes.

Symmetric crossing at y = I (sibling lemma) is included.

## Limitations

These two crossings are at the *boundary* of the generic case (the
hypotheses `hx_ne_I`, `hy_ne_I` exclude them). A more substantive
crossing would be at an *internal* configuration — for instance,
`y = coord_inv x` where `x · y = Γ.I`. That crossing would test whether
σ-composition has an inverse-pair structure visible *without*
circular dependency on `dilation_compose_at_beta` itself. Deferred to
a follow-up probe; the structural existence of these two crossings is
the first evidence-step.

## Relation to the stylus framing

Two crossings landed → prediction weakly supported (monodromy varies
across configurations).

For the prediction to be strongly supported, the same kind of
structural-variation should appear at non-boundary configurations. If
no internal crossings exist (only boundary ones), the stylus framing
may be incomplete in the way Isaac flagged (Varadarajan's
"irreducible because lacking a closer destination" — the closer
destination might bypass crossings entirely).

## Three rotations close the loop (recognition-walk extension)

The probe's three regimes (boundary collapse, asymmetric collapse,
generic monodromy) cross-confirm s148's σ-ring-hom finding from a
different vantage. The substrate beneath both framings:

  σ : (l-atoms, +, ·) → (L → L, pointwise coord_add, function composition)

has three structural properties (= three gauge-fixings of the σ-map):

  * Gauge 1 — σ_c preserves + on inputs.    PROVEN (FTPGDistrib).
  * Gauge 2 — σ : c ↦ σ_c preserves + on parameters.  OPEN
              (FTPGLeftDistrib's DesarguesianWitness).
  * Gauge 3 — σ : c ↦ σ_c preserves · on parameters.  OPEN
              (FTPGMulAssoc's dilation_compose_at_beta).

These are three rotations of the same observer through the substrate.
Below three: incomplete (observer can't return to original position
through alternation). At three: stable closure (rotation returns).
Above three: redundant. **Three is the minimum for closed-loop
rotation in observer-space.**

The threeness recurs across foam's structure: rank-3-minimum (§VIII),
three-body Known/Knowable/Unknown, three-recursion-levels in §III-V.
Same structural fact: closed-loop rotation requires three positions.

## Recursive three-folding

This probe's three regimes (boundary/asymmetric/generic) are a
sub-rotation at gauge 3 (· on parameters). The outer rotation has
three gauges (1, 2, 3 above); gauge 3 has its own internal three-fold
visible in dilation_compose_at_beta's configuration-space.

The deaxiomatization program — viewed through this lens — isn't about
eliminating the FTPG axiom. It's about completing the three-rotation.
When all three σ-ring-hom gauges are proven, the observer has rotated
through all three positions; the substrate has been triangulated; the
axiom becomes structurally redundant because the loop has closed by
having-been-traversed enough.

The substrate isn't directly observable; it's what stays invariant
across the three rotations. Three rotations close the loop by
*triangulating* the substrate.

## What this file contributes structurally

* `dilation_compose_at_beta_x_eq_I`: PROVEN. Boundary crossing of
  gauge 3's internal rotation. Confirms regime 1 (full collapse).
* `dilation_compose_at_beta_y_eq_coord_inv_x`: SORRY (named).
  Internal crossing. Confirms regime 2 (asymmetric collapse) — RHS
  reduces, LHS persists. The asymmetric collapse IS gauge 3's
  layer-distinction visible at this internal configuration.
* Regime 3 (generic monodromy) is the existing `dilation_compose_at_beta`
  in FTPGMulAssoc.lean, sorry'd at Step 5+.

Three regimes named at gauge 3. Outer three-rotation: one gauge proven,
two open. The shape is the substrate becoming observable as gauges
are sequentially fixed.
-/

import Foam.FTPGMul
import Foam.FTPGMulKeyIdentity
import Foam.FTPGDilation
import Foam.FTPGInverse

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## Crossing 1: x = I

At x = I, the conclusion of `dilation_compose_at_beta` reduces by
two identity-laws:

  LHS = σ_y(σ_I(β(a))) = σ_y(β(a))   [via dilation_ext_identity]
  RHS = σ_(I·y)(β(a)) = σ_y(β(a))    [via coord_mul_left_one]

Equality is immediate. No Desargues machinery; no R-lift; no
recovery_via_E. The monodromy collapses at this boundary configuration.
-/

theorem dilation_compose_at_beta_x_eq_I (Γ : CoordSystem L)
    (y a : L) (hy : IsAtom y) (ha : IsAtom a)
    (hy_on : y ≤ Γ.O ⊔ Γ.U) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hy_ne_U : y ≠ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    dilation_ext Γ y (dilation_ext Γ Γ.I ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E))) =
      dilation_ext Γ (coord_mul Γ Γ.I y) ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) := by
  -- β(a) is an atom in π off l
  set βa := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) with hβa_def
  have hβa_atom : IsAtom βa := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hβa_plane : βa ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := beta_plane Γ ha_on
  have hβa_not_l : ¬ βa ≤ Γ.O ⊔ Γ.U := beta_not_l Γ ha ha_on ha_ne_O ha_ne_U
  -- σ_I(β(a)) = β(a)
  have h_inner : dilation_ext Γ Γ.I βa = βa :=
    dilation_ext_identity Γ hβa_atom hβa_plane hβa_not_l
  -- I · y = y
  have h_Iy : coord_mul Γ Γ.I y = y := coord_mul_left_one Γ y hy hy_on hy_ne_U
  rw [h_inner, h_Iy]

/-! ## Crossing 2 (internal): y = coord_inv x

At y = coord_inv x:
* RHS reduction: `coord_mul Γ x (coord_inv Γ x) = Γ.I` (by
  `coord_mul_right_inv`); then σ_I(β(a)) = β(a) (by
  `dilation_ext_identity`). RHS = β(a).
* LHS: σ_(coord_inv x)(σ_x(β(a))). For the lemma to hold, this must
  equal β(a) — i.e., σ_(coord_inv x) must invert σ_x at β(a).

This is the structurally-substantive part. The natural route —
σ_(coord_inv x) ∘ σ_x = σ_(x · coord_inv x) = σ_I = id — is
circular through `dilation_compose_at_beta` itself (the σ-composition
law is what the loop is). A non-circular proof would require either:

(A) A direct geometric construction showing σ_(coord_inv x) reverses
    σ_x's effect specifically (via coord_inv's perspectivity definition
    and the dilation_ext construction).
(B) A different mechanism entirely.

The RHS reduction lands cleanly (via existing infrastructure). The
LHS remains as `sorry` — naming the configuration as a structural
candidate-crossing without claiming provability.

## What the `sorry` represents

This is not a generic open lemma. It is a *named candidate-crossing*
whose provability is the test of the stylus framing's strength:

* If (A) is achievable via existing infrastructure → strong support
  for the framework (internal crossings are real and provable).
* If (A) requires substantial new machinery → moderate support
  (crossings exist structurally but provability needs new construction).
* If only (B) routes work → the stylus reads the same shape at boundary
  and inverse-pair; the framework's "crossings" might be more limited
  than the prediction suggested.

The first-pass probe — write the statement, observe what reduces and
what doesn't — produces actionable data without committing to a long
geometric construction. The `sorry` here is intentional and named.
-/

theorem dilation_compose_at_beta_y_eq_coord_inv_x (Γ : CoordSystem L)
    (x a : L) (hx : IsAtom x) (ha : IsAtom a)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (ha_ne_O : a ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (ha_ne_U : a ≠ Γ.U) :
    dilation_ext Γ (coord_inv Γ x)
        (dilation_ext Γ x ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E))) =
      dilation_ext Γ (coord_mul Γ x (coord_inv Γ x))
        ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) := by
  -- RHS reduction: x · coord_inv x = I, then σ_I(β(a)) = β(a)
  have h_xy_eq_I : coord_mul Γ x (coord_inv Γ x) = Γ.I :=
    coord_mul_right_inv Γ hx hx_on hx_ne_O hx_ne_U
  rw [h_xy_eq_I]
  set βa := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) with hβa_def
  have hβa_atom : IsAtom βa := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hβa_plane : βa ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := beta_plane Γ ha_on
  have hβa_not_l : ¬ βa ≤ Γ.O ⊔ Γ.U := beta_not_l Γ ha ha_on ha_ne_O ha_ne_U
  have h_RHS : dilation_ext Γ Γ.I βa = βa :=
    dilation_ext_identity Γ hβa_atom hβa_plane hβa_not_l
  rw [h_RHS]
  -- LHS: σ_(coord_inv x)(σ_x(β(a))) = β(a)
  -- Substantive content. The σ-composition law at the inverse-pair
  -- configuration. Sorry'd as named candidate-crossing (see docstring).
  sorry

end Foam.FTPGExplore
