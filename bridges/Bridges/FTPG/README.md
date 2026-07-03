# FTPG — the fundamental theorem of projective geometry, deaxiomatized

`../FTPG.lean` states classical FTPG as an axiom (`ftpg`): every complemented
modular bounded lattice is order-isomorphic to the subspace lattice of a vector
space over a division ring. It is the one imported posit of the classical bridge.

This directory is the effort to **discharge** it — construct the division ring
and the lattice iso from the lattice itself, deleting the axiom. It lifts the
von Staudt / von Neumann coordinatization (the prior era's, tag `the-between`),
now with the two hard walls proven.

## State

Both hard walls are proven, axiom-free-modulo-classical
(`[propext, Classical.choice, Quot.sound]`):

- **multiplicative associativity** — `MulAssoc.lean` (`coord_mul_assoc`)
- **distributivity** — `LeftDistrib.lean` / `Distrib.lean`

Open frontier:

- the coordinate ring's **additive group** — `Additive.lean`. Cancellation is
  proven (`AddCancel.lean`); associativity is reduced to two named geometric
  lemmas (`inv_absorb`, `double_left`) plus the characteristic-2 knot.
  The active route is no longer the 17 witness leaves: the master lemma
  **`tau_inv_tower`** — τ_x ∘ τ_{−x} = id on the auxiliary line q — is now
  PROVEN (axiom-clean-modulo-classical), subsuming all of them, the char-2 knot
  included.  Its camps: `neg_tower_reverse` (the reverse translation is the
  negative's tower, from `coord_add_left_neg`), `inv_aux_point` (the
  general-position point `z = (x ⊔ E) ⊓ (w' ⊔ X)`), `span_plane`, `q_covBy_π`.
  `inv_absorb_generic` and `char2_absorb` are now proven as its corollaries
  (`tower_meets_E_line`, `tower_inj` the connective tissue) — the 17 witness
  leaves and the char-2 sorry are gone.  Remaining: totalize
  `inv_absorb`/`double_left` at the `Coordinate` level.
- the **coordinate map / lattice iso** — `Iso.lean`, `Deaxiomatize.lean`,
  reduced to a single `PointSystem` residual (the *second* FTPG). Mathlib's
  `Projectivization.Subspace.submodule` supplies the last step for free.

## Floor-up

| file | content |
|---|---|
| `Projective` | projective incidence, Desargues, perspectivities — the foundation |
| `Coord`, `Parallelogram`, `AddComm` | coordinate addition |
| `Mul`, `Dilation`, `MulKeyIdentity` | coordinate multiplication |
| `Assoc`, `AssocCapstone`, `Neg`, `Distrib`, `LeftDistrib` | the ring laws (incl. both walls) |
| `Inverse` | multiplicative inverse |
| `AddCancel`, `Additive` | the additive group (cancellation proven; associativity frontier) |
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
