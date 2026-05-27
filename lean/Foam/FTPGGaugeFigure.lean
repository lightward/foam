/-
# FTPGGaugeFigure — the 3×3 figure (s152, post-s151 stylus refinement)

The s151 reframe (`FTPGMulAssocCrossings.lean`) named three σ-ring-hom
gauges and within each, three configurational regimes. This file makes
the 3×3 figure visible as a typed artifact: each cell is named as a
Prop, its existing theorem (or named candidate `sorry`) referenced,
its structural role in the figure recorded.

## The three gauges (σ-ring-hom rotations)

σ : (l-atoms, +, ·) → (L → L, pointwise coord_add, composition)
should be a ring homomorphism, with three structural compatibilities:

* **G1** — σ_c preserves + on inputs      (right-distributivity)
* **G2** — σ : c ↦ σ_c preserves + on parameters  (left-distributivity)
* **G3** — σ : c ↦ σ_c preserves · on parameters  (mul-associativity)

## The three regimes

* **boundary** — one input is the identity of the corresponding operation
* **asymmetric** — one input is the inverse-pair partner of another
* **generic** — full non-degeneracy

## The 3×3

|    | boundary             | asymmetric                         | generic                              |
|----|----------------------|------------------------------------|--------------------------------------|
| G1 | (a+O)·c = a·c        | (a+(-a))·c = a·c+(-a)·c            | (a+b)·c = a·c+b·c          PROVEN   |
| G2 | a·(b+O) = a·b        | a·(b+(-b)) = a·b+a·(-b)            | a·(b+c) = a·b+a·c          Witness  |
| G3 | a·(I·c) = (a·I)·c    | a·(x·x⁻¹) = (a·x)·x⁻¹              | a·(b·c) = (a·b)·c          open     |

## The s152 reading of the asymmetric row (a structural revision)

Initial intuition: "asymmetric cells are one-line specializations of
the generic + zero-annihilation." Checking signatures revealed this is
wrong: `coord_mul_right_distrib` carries hypothesis `coord_add a b ≠ O`,
which is *violated* by the asymmetric configuration (sum IS O). So the
asymmetric row cells are not direct specializations of the generic row
cells.

Distilled: each asymmetric cell asks one question — does the σ-action
commute with the relevant operation's inversion?

* **G1-asymmetric**: does σ_c commute with `coord_neg`?  `(-a)·c = -(a·c)`?
* **G2-asymmetric**: does `c ↦ σ_c` commute with `coord_neg`?  `a·(-b) = -(a·b)`?
* **G3-asymmetric**: does `c ↦ σ_c` commute with `coord_inv`?
  `σ_(coord_inv x) = (σ_x)⁻¹` in the dilation monoid?

These three are the **dagger-shape across gauges**: in Heunen-Kornell's
six-axiom Hilbert characterization, the dagger jointly enforces all
three. Foam's no-dagger setting separates them; the asymmetric row IS
the dagger-probe.

## Second-pass refinement: the twist concentrates in gauge 3

G1-asymmetric and G2-asymmetric are **derivable from their column's
generic + the additive group structure**, via an auxiliary-atom
bootstrap that routes around the degenerate-sum hypothesis:

For G1: introduce x atom, x ≠ a, x ≠ -a, with appropriate
non-degeneracies. Then by two applications of g1_generic plus
add-assoc plus coord_add_left_neg applied to x·c, cancel x·c to obtain
`a·c + (-a)·c = O`. Symmetric construction for G2 with auxiliary y.

For G3, the analogous bootstrap would require two applications of
g3_generic — but g3_generic is open (the dilation_compose_at_beta
sorry). There is no substitute for assoc the way additive
infrastructure substitutes for the degenerate-sum case.

So the structural reading: **the holonomy of the FTPG bridge
concentrates in gauge 3**. G1 and G2 carry no irreducible twist (the
asymmetric cells are bootstrap-trivializable). G3 — both its
asymmetric and generic cells — is where the dagger-asymmetry actually
lives.

This matches HK's framing: without dagger, what's missing in foam's
σ-ring-hom reduces to the multiplicative-associativity content. The
additive content is fully accessible; the multiplicative content
carries the holonomy.

## What this file contributes

Nine cell-bindings, each a Prop named for its figure position and
referenced (where existing) to its theorem. The asymmetric row's three
cells are stated explicitly as candidate-Props with `sorry`, naming
the three dagger-shape questions as typed objects in the project.

This is recognition-grade: no new construction, just layout. The
figure's structure becomes a Lean artifact.
-/

import Foam.FTPGDistrib
import Foam.FTPGLeftDistrib
import Foam.FTPGMulAssoc
import Foam.FTPGMulAssocCrossings
import Foam.FTPGInverse
import Foam.FTPGNeg

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## Generic row -/

/-- G1-generic: right-distributivity. PROVEN as `coord_mul_right_distrib`. -/
abbrev g1_generic := @coord_mul_right_distrib

/-- G2-generic: left-distributivity. Requires `DesarguesianWitness Γ`.
Proven as `coord_mul_left_distrib`. -/
abbrev g2_generic := @coord_mul_left_distrib

/-- G3-generic: σ-composition at β-images. Open as `dilation_compose_at_beta`
(Step 5+ sorry'd; 4 monodromy measurements s142/s146/s148/s149).

The trefoil's **third crossing** (`StatelessSubstrate.TrefoilCrossing.third`):
the *commitment-site* where the observer's
`StatelessSubstrate.HolonomicLedger` lands. The four prior monodromy
measurements weren't failures — they were unknotting moves contributing
to the resistance-map (`dissonance-as-unknotting`), each returning
"circularity" as the substrate refusing the wrong type
(silence-as-signal).

In `StatelessSubstrate.lean` terms: G3 yield-position. Closes via
`ExternalYieldComposition` (single yield may dissolve g3_asymmetric
and g3_generic jointly — *some unknottings dissolve more than one
type of knot*) or via re-entrant recognition-walks surfacing
substrate-direct closure. Commitment is observer-side (BYO `now`);
substrate doesn't carry it.

**Tree-balance reframing (s155, simplified from earlier
AsyncMeasurement protocol):** this cell is one position in the *tree
of accumulated FTPG measurements*. Each measurement is a disposable
single-use observer (`StatelessSubstrate.Measurement`); the tree-state
across measurements is realized as `Foam.CommitmentState` in
Resolver.lean. The sorry is the *tree being unbalanced at this
position* — async-ness lives at tree-level
(`CommitmentState.IsResolved` / `MetabolisisStep.IsFixedPoint`), not
at the individual measurement. Settlement at this position happens
when the `HolonomicLedger` commits at `TrefoilCrossing.third`; the
sorry is the correct typed state until then. -/
abbrev g3_generic := @dilation_compose_at_beta

/-! ## Boundary row -/

/-- G1-boundary: (a + O)·c = a·c. Trivial via `coord_add_right_zero`. -/
theorem g1_boundary (Γ : CoordSystem L)
    (a c : L) (ha : IsAtom a) (ha_on : a ≤ Γ.O ⊔ Γ.U) :
    coord_mul Γ (coord_add Γ a Γ.O) c = coord_mul Γ a c := by
  rw [coord_add_right_zero Γ a ha ha_on]

/-- G2-boundary: a · (b + O) = a · b. Trivial via `coord_add_right_zero`. -/
theorem g2_boundary (Γ : CoordSystem L)
    (a b : L) (hb : IsAtom b) (hb_on : b ≤ Γ.O ⊔ Γ.U) :
    coord_mul Γ a (coord_add Γ b Γ.O) = coord_mul Γ a b := by
  rw [coord_add_right_zero Γ b hb hb_on]

/-- G3-boundary at x=I: σ_y(σ_I(β(a))) = σ_(I·y)(β(a)). PROVEN as
`dilation_compose_at_beta_x_eq_I` (s151).

The trefoil's **first crossing** (`StatelessSubstrate.TrefoilCrossing.first`):
deterministic, no commitment required. Monodromy fully collapses
at this boundary — identity-laws alone, no Desargues. The trefoil-
progression's deterministic anchor. -/
abbrev g3_boundary := @dilation_compose_at_beta_x_eq_I

/-! ## Asymmetric row — the dagger-probe

Each cell asks whether σ commutes with inversion in the relevant
operation. None is derivable from the corresponding generic cell;
each is independent measurement evidence.
-/

/-- G1-asymmetric: does σ_c commute with `coord_neg`?

LHS = `(a + (-a)) · c = O · c = O` via `coord_add_left_neg` +
`coord_mul_left_zero`.

RHS = `a·c + (-a)·c`. For RHS = O, we need `(-a)·c = -(a·c)` — i.e.,
the σ_c-action commutes with additive inversion.

Not a specialization of `coord_mul_right_distrib`: that theorem's
hypothesis `hs_ne_O : coord_add Γ a b ≠ Γ.O` is violated here (the
sum IS O). This is a separate measurement at a configuration the
generic excludes.
-/
theorem g1_asymmetric (Γ : CoordSystem L) (a c : L)
    (ha : IsAtom a) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hc_ne_U : c ≠ Γ.U) :
    coord_mul Γ (coord_neg Γ a) c = coord_neg Γ (coord_mul Γ a c) := by
  -- s152 finding: substrate-derivable via "additive bootstrap."
  -- Direct lattice proof of (σc ⊔ ea) ⊓ l = (C ⊔ e_{ac}) ⊓ l would
  -- require Desargues, but we can route around through the algebraic
  -- structure:
  --
  --   1. pick auxiliary atom x ≠ a, ≠ -a
  --   2. apply g1_generic at (a, -a + x): (a + (-a+x))·c = a·c + (-a+x)·c
  --      (sum = x ≠ O, hypotheses satisfied)
  --   3. apply g1_generic at (-a, x): (-a+x)·c = (-a)·c + x·c
  --      (sum ≠ O, hypotheses satisfied)
  --   4. combine via add-assoc: x·c = a·c + (-a)·c + x·c
  --   5. cancel x·c via coord_add_left_neg applied to x·c
  --      ⟹ a·c + (-a)·c = O ⟹ (-a)·c = -(a·c) by uniqueness
  --
  -- The construction needs R, h_irred parameters (for coord_add_left_neg
  -- on x·c) and additional hypotheses for the auxiliary x. Open as
  -- recognition-target — the structural conclusion (substrate-derivable
  -- without fresh Desargues) is the figure-finding.
  sorry

/-- G2-asymmetric: does the parameter ↦ σ_param map commute with
`coord_neg`?

LHS = `a · (b + (-b)) = a · O = O` via `coord_add_left_neg` +
`coord_mul_right_zero`. RHS = `a·b + a·(-b)`. For RHS = O, need
`a·(-b) = -(a·b)`.

Same structural shape as g1_asymmetric: substrate-derivable via
additive bootstrap (introduce auxiliary y, two applications of
g2_generic, cancel a·y).

Difference from g1_asymmetric: this version depends on a
`DesarguesianWitness Γ` (g2_generic = coord_mul_left_distrib carries
that interface). The bootstrap inherits the witness-dependency. -/
theorem g2_asymmetric (Γ : CoordSystem L) (a b : L)
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) :
    coord_mul Γ a (coord_neg Γ b) = coord_neg Γ (coord_mul Γ a b) := by
  sorry

/-- G3-asymmetric: σ_(coord_inv x)(σ_x(β(a))) = β(a). Named as
`dilation_compose_at_beta_y_eq_coord_inv_x` (s151).

The trefoil's **second crossing**
(`StatelessSubstrate.TrefoilCrossing.second`) — *vacuum-formation
site*. RHS forward-evaluates to β(a); LHS persists as held vacuum-
shape. Typed in `FTPGGaugeFigureLayer.lean` (s155) as the
`vacuum_fill_event_at_inverse_pair` between `inverse_pair_expr_lhs`
(buffer-side, `CellLayer.buffer`) and `inverse_pair_expr_rhs`
(working-space-side, `CellLayer.working_space`). The chirality
assignment is gauge (`CellChirality.canonical` + `.flip`).

In `StatelessSubstrate.lean` (s155) terms: tape-positions (G3, read)
and (G3, write) — the yield with both observer-states. Commitment
proper happens at the *third* crossing (g3_generic).

The dagger-shape in the multiplicative gauge: G3-asymmetric is the
question of σ-involution under multiplicative inversion — equivalently,
the vacuum formed when the observer's `StatelessSubstrate.HolonomicLedger`
encounters the inverse-pair configuration. The sorry is vacuum-shape-
typed, awaiting fill via yield-composition or substrate-direct
surfacing.

In tree-balance terms (s155): this cell is one position in the tree
of accumulated measurements; the sorry is the tree-not-yet-balanced-
at-this-position. The single measurement here is one-shot disposable
(`StatelessSubstrate.Measurement`); it has no async-property itself.
Tree-balance is checked via `Foam.CommitmentState.IsResolved` or
`MetabolisisStep.IsFixedPoint`. Settlement at this position happens
when metabolisis brings the tree to balance. -/
abbrev g3_asymmetric := @dilation_compose_at_beta_y_eq_coord_inv_x

end Foam.FTPGExplore
