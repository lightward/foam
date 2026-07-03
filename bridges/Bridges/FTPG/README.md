# FTPG — the fundamental theorem of projective geometry, deaxiomatized

`../FTPG.lean` states classical FTPG as an axiom (`ftpg`): every complemented
modular bounded lattice is order-isomorphic to the subspace lattice of a vector
space over a division ring. It is the one imported posit of the classical bridge.

This directory is the effort to **discharge** it — construct the division ring
and the lattice iso from the lattice itself, deleting the axiom. It lifts the
von Staudt / von Neumann coordinatization (the prior era's, tag `the-between`),
now with the two hard walls proven.

## State

All three hard walls are proven, axiom-free-modulo-classical
(`[propext, Classical.choice, Quot.sound]`):

- **multiplicative associativity** — `MulAssoc.lean` (`coord_mul_assoc`)
- **distributivity** — `LeftDistrib.lean` / `Distrib.lean`
- **the additive group** — `Additive.lean` (`fadd_assoc_total`), CLOSED.
  The summit lemma is **`tau_inv_tower`**: τ_x ∘ τ_{−x} = id on the auxiliary
  line q — the one translation-composition law `beta_step_core` cannot state
  (composite parameter O).  It subsumes what the prior era isolated as the
  base-change involution, its 17 witness-incidence leaves, and the
  characteristic-2 knot (`char2_absorb` is just the master lemma with −a
  rewritten to a).  Camps: `neg_tower_reverse` (the reverse translation is the
  negative's tower, from `coord_add_left_neg`), `inv_aux_point` (the
  general-position point `z = (x ⊔ E) ⊓ (w' ⊔ X)` — model-verified over
  `PG(2,q)`, `q = 3,5,7,11,13`, before carving), `span_plane`, `q_covBy_π`,
  `tower_meets_E_line`, `tower_inj`; doubling satellites `z3_knot` (the ℤ/3
  sub-line closes — `dbl_beta_generic` in four moves), `dbl_plus_neg`,
  `dbl_assoc_sq`.

Open frontier:

- the **`DivisionRing` totalization** — of the six side-conditioned fields,
  four are now total: `fadd_assoc_total`, `fadd_comm`, `fneg_add`
  (`Additive.lean`) and `fmul_assoc_total` (`CoordinateAlgebra.lean` —
  multiplication's wall never needed distinct operands, so its totalization is
  pure case analysis).  The genuine residual is the two **distributive laws**.
  Their degenerate branches wanted `mul_neg` (`a·(−b) = −(a·b)`) and
  multiplicative cancellation; cancellation is now **free**
  (`CoordinateAlgebra.lean`: total associativity turns the right-inverse law
  into the left — `field_inv_mul_cancel` — and `fmul_left_cancel` /
  `fmul_right_cancel` follow by algebra alone, no geometry).  What remains is
  `mul_neg`, which total associativity reduces to the one-parameter laws
  `x·(−1) = −x` and `(−1)·x = −x` — *the −1-dilation is the negation
  involution* — the next descent.
- the **coordinate map / lattice iso** — `Iso.lean`, `Deaxiomatize.lean`,
  reduced to a single `PointSystem` residual (the *second* FTPG). Mathlib's
  `Projectivization.Subspace.submodule` supplies the last step for free.
  (`Deaxiomatize.lean`'s premature instances also await the import-order
  reconciliation: the assembly belongs downstream of the proven laws.)

## Floor-up

| file | content |
|---|---|
| `Projective` | projective incidence, Desargues, perspectivities — the foundation |
| `Coord`, `Parallelogram`, `AddComm` | coordinate addition |
| `Mul`, `Dilation`, `MulKeyIdentity` | coordinate multiplication |
| `Assoc`, `AssocCapstone`, `Neg`, `Distrib`, `LeftDistrib` | the ring laws (incl. both walls) |
| `Inverse` | multiplicative inverse |
| `AddCancel`, `Additive` | the additive group, closed (cancellation, τ-inverse master lemma, total associativity) |
| `CoordinateAlgebra`, `Iso`, `Deaxiomatize` | the endgame — the `DivisionRing` instance, the lattice iso, and `ftpg_proof` |

## Notes

- `ftpg_proof : ftpg_statement` (in `Deaxiomatize`) type-checks end to end — it
  reduces to the labeled endgame gaps, not to the axiom.
- The closure lemmas (`coord_add_ne_U`, `coord_mul_ne_U`, `coord_mul_ne_O`) are
  proven at the coord level in `CoordinateAlgebra`; `Deaxiomatize` restates them
  on the carrier as `sorry` pending an import-order reconciliation
  (`CoordinateAlgebra` imports `Deaxiomatize`, so the proofs can't yet flow back).
- `h_sufficient : True` in the axiom marks where the genuine hypothesis
  (dim ≥ 3 / Arguesian) belongs: the unrestricted statement is over-strong —
  the octonion projective plane is a complemented modular lattice that is *not*
  a subspace lattice.
- The prior era's σ-route (multiplication associativity via the
  dilation-as-monoid homomorphism `σ_mul`) was superseded by the `crux_at_C`
  proof and removed; it lives in git history.

## How the walls fell

`coord_mul_assoc`: the σ-closure was circular in the plane; it fell to a
center-`O` Desargues made non-degenerate by an off-plane witness `R` — the
in-plane stall relieved by a seat descended from above (`Foam/Seat/Descend.lean`).
`coord_mul_left_distrib`: left-multiplication is not a collineation, so its
concurrence (the old `DesarguesianWitness`) is a genuine second wall; it reduced
to the additivity of the E-projection and fell to `CrossParallelism`.
`fadd_assoc_total`: the degenerate associators (`a + (-a + c)`, `(a+a) + c`)
stalled for an era as 17 witness-incidence leaves plus a char-2 knot; all of it
was one missing law — τ_x ∘ τ_{−x} = id, the inverse case of translation
composition — and fell to `tau_inv_tower`, a double transport through an
auxiliary point off the tower line, seeded by one fresh good point.  The wall
was never 17 facts; it was one fact seen 17 times.
