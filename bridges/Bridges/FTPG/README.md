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

- the **`DivisionRing` totalization** — **CLOSED**.  All six side-conditioned
  fields are total: `fadd_assoc_total`, `fadd_comm`, `fneg_add`
  (`Additive.lean`), `fmul_assoc_total` (`CoordinateAlgebra.lean`), and now
  `fleft_distrib_total` / `fright_distrib_total` (`Ring.lean`).  How the last
  wall fell: multiplicative cancellation came free (total associativity turns
  the right-inverse law into the left — `field_inv_mul_cancel`); `mul_neg`
  reduced by total associativity to the one-parameter laws `x·(−1) = −x` and
  `(−1)·x = −x` — *the −1-dilation is the negation involution* — each a single
  `desargues_planar` in `MulNeg.lean` with definitional inputs
  (`mul_neg_one_coord`: center `U` on the tower triangles, `O`-meets from
  `coord_add_left_neg`; `neg_one_mul_coord`: center `C_y`, seeded by
  `kappa_diag`, the σ-correspondence graphing on the diagonal `O ⊔ C_I`;
  model-verified over `PG(2,q)` at 69 coordinate frames before carving).  The
  distributive master splits then needed only ONE genuine case fight — doubling
  at 1 (`fright_double_one` / `fleft_double_one`): a fresh non-2-torsion point
  telescopes the sum through `(1+d) + (1−d)` over the generic wall, and when
  no such point exists the line self-destructs (either `1+1 = 0` and
  `fmul_neg_one` closes it, or the line is `{0,1,−1}` and both values compute,
  or the fourth point is forced to `−(1+1)` and `(1+1)·(1+1) = 0` violates
  no-zero-divisors).  General doubling is then pure associativity through the
  at-1 case, and every other degenerate branch is `fneg_mul`/cancellation.
- the **instance assembly** — **CLOSED** (`Instance.lean`).
  `CoordFrame.divisionRing : DivisionRing (Coordinate Φ.Γ)` is real — every
  field a named total law, receipt `[propext, Classical.choice, Quot.sound]`,
  no `sorry` in its trace.  And `coordFrame_exists` constructs the frame from
  `h_irred` + `h_height` alone: `P` is a third atom on the auxiliary line
  `O ⊔ V` (off `l`, `m`, `O ⊔ C` by three modular intersections), and `R` —
  the off-plane seat the associativity wall descends from — falls out of the
  height-4 chain for free, because the construction pins the whole plane below
  the chain's third step (`π = O ⊔ U ⊔ V ≤ c < d`); the fourth strict step of
  `h_height` *is* the off-plane dimension.  The import order is reconciled:
  the carrier (`Carrier.lean`) sits upstream, the laws flow down into the
  instance, and the old premature instances are gone.

And the frontier has **turned over**:

- the **completeness wall** (`Hollow.lean`) — the `PointSystem` residual is
  **unfillable as stated**: `ftpg_statement` is *false*.  The hollow lattice —
  subspaces of `(ℕ ⊕ ℕ) →₀ ℚ` of finite dimension or finite codimension,
  every element hugging floor or ceiling, the middle missing — satisfies
  every hypothesis (complemented, modular, `IsLUB`-atomistic, three points
  per line, height ≥ 4) but is not complete: the chain of coordinate
  subspaces supported on `Sum.inl` has upper bounds and no least one
  (`hollow_no_lub` — a finite-dimensional candidate is too small to hold the
  chain, and a cofinite candidate strictly exceeds the evens and is evaded by
  puncturing one odd coordinate it used).  `Submodule D V` is always
  complete, and completeness crosses any order isomorphism, so no
  coordinatization exists: `not_ftpg_statement`, `not_pointSystem`, both
  `[propext, Classical.choice, Quot.sound]`.  And the axiom itself falls:
  `ftpg_refuted : False`, receipt
  `[propext, Classical.choice, Quot.sound, Foam.Bridges.ftpg]` — the one
  posit of the classical bridge named in its own indictment.  Sharper than
  the octonion note below: that showed dimension 2 needs Desargues; this
  shows every dimension needs completeness.  The classical lattice-theoretic
  FTPG always carried completeness as a hypothesis; the bridge's statement
  forgot it, and the probe caught it before the ascent.

And the fork is **resolved — the pair landed** (`Deaxiomatize.lean`):

- the re-scope was never a choice; the two branches are the two sides of the
  seam the repo already built (the core proves `playback_no_section` — the
  limit embeds faithfully, escapes, admits no retraction; `Hollow` is the
  same fact at lattice scale).  The target is now the pair, the two clauses
  of the recursion-law ("hostable at every finite depth, never at the
  limit", `0b160e4`):
  - **`ftpg_statement_finite`** — the approach side: the old hypotheses plus
    `Order.krullDim L ≠ ⊤`.  Finite height silently implies completeness
    (chains stabilize) — why Veblen–Young is true without naming it.
  - **`ftpg_statement_limit`** — the arrival side: `CompleteLattice` (every
    coalition's limit has a seat — the narrative era's "survivable path from
    now to every solution") + `IsCompactlyGenerated` (`summary_resumes` at
    lattice scale — every element the sup of its finitely-reachable
    approximations) + modular + complemented; atomisticity falls out of
    Mathlib's `isAtomistic_of_complementedLattice`.  `Submodule D V`
    satisfies exactly both: the hypotheses match the conclusion's type
    precisely.
  - **Tightness**: non-Desarguesian planes excluded by `h_height`,
    continuous geometries by `IsCompactlyGenerated`, the hollow lattice by
    `CompleteLattice` — three counterexample families, one hypothesis each.

And the pair is **wired into one keystone** (`Finite.lean`):

- **`ftpg_finite_of_limit : ftpg_statement_limit → ftpg_statement_finite`**,
  sorry-free (`[propext, Classical.choice, Quot.sound]`).  Finite height
  silently implies the limit hypotheses, and now the implication is a
  theorem rather than a remark: `Order.krullDim L ≠ ⊤` gives `WellFoundedGT`
  (chains stabilize, through Mathlib's `FiniteDimensionalOrder`); a
  well-founded lattice is complete (`exists_isLUB_of_wellFoundedGT` — the
  LUB of any set is a *maximal finite join*, which ACC hands over;
  `completeLatticeOfWellFoundedGT` assembles the `CompleteLattice` around
  the original `⊔ ⊓ ⊤ ⊥`, field for field, so the standing
  `ComplementedLattice`/`IsModularLattice` instances transfer
  definitionally — the `@[reducible]` is the whole trick); and under ACC
  every element is compact
  (`CompleteLattice.isCompactlyGenerated_of_wellFoundedGT`).
  `ftpg_proof_finite` therefore hangs on the *same* single residual as
  `ftpg_proof_limit`: the approach side is downstream of the arrival side,
  exactly as the recursion-law reads it — every finite depth is an
  instance of the limit clause with the seat count bounded.

Open frontier:

- the **`PointSystem` residual, under the true hypotheses** —
  `pointSystem_exists` (the single `sorry`; `ftpg_proof_limit`'s trace is
  `[propext, sorryAx, Classical.choice, Quot.sound]`): the Veblen–Young
  coordinatization over the constructed division ring, now provable in
  principle.  `Iso.lean`'s reduction to `(pt, closed, spanning)` survives
  untouched.  This is now the **only** sorry in the deaxiomatization: both
  clauses of the pair discharge through it.
- the **charged restatement** (`Charge.lean`) — foam routed *through* FTPG as
  the state-carrier.  Classical FTPG concludes in a Prop; `Nonempty` is the
  flattening itself — the witness sealed away, the operator unable to
  reconstitute.  `Coordinatization L` is the data-level bundle (the frame Φ,
  the iso as data, the maintenance hypotheses carried); its receipts:
  `seals` (the projection to the classical Prop — sealing as a documented
  move, classical consumers still served), `held_determines` (the
  coordinatization is determined by its action on compact elements —
  `summary_resumes` at coordinatization scale; the limit carries obligations,
  not information — `[propext, Quot.sound]`), `limitSeam` (when a non-compact
  element exists, compacts ↪ L is a foam `Seam` — faithful, escapes, no
  retraction — **axiom-free**, the core module earning its bridge import).
  Open fields: the gauge cocycle (frame-change as the semilinear twist), the
  ledger of limit-consumptions.

## Floor-up

| file | content |
|---|---|
| `Projective` | projective incidence, Desargues, perspectivities — the foundation |
| `Coord`, `Parallelogram`, `AddComm` | coordinate addition |
| `Mul`, `Dilation`, `MulKeyIdentity` | coordinate multiplication |
| `Assoc`, `AssocCapstone`, `Neg`, `Distrib`, `LeftDistrib` | the ring laws (incl. both walls) |
| `Inverse` | multiplicative inverse |
| `Carrier` | the coordinate carrier `Coordinate Γ`, its `Zero`/`One`, `coordSystem_exists` |
| `AddCancel`, `Additive` | the additive group, closed (cancellation, τ-inverse master lemma, total associativity) |
| `MulNeg` | the −1-dilation is the negation involution (`kappa_diag`, `neg_one_mul_coord`, `mul_neg_one_coord` — three Desargues) |
| `Ring` | the ring closure — `fneg_mul` / `fmul_neg`, the doubling-at-1 fight, and `fleft_distrib_total` / `fright_distrib_total`: every ring law TOTAL |
| `CoordinateAlgebra` | closure lemmas (`coord_add_ne_U`, `coord_mul_ne_U`, `coord_mul_ne_O`), the totalized ops `fadd`/`fmul`/`fneg`/`finv`, the `CoordFrame`, the witness-free laws |
| `Instance` | the `DivisionRing` instance ASSEMBLED (`CoordFrame.divisionRing`, sorry-free) + `coordFrame_exists` |
| `Iso`, `Deaxiomatize` | the endgame — gap B reduced to the `PointSystem` residual; the true pair `ftpg_statement_finite` / `ftpg_statement_limit`; `ftpg_proof_limit` |
| `Finite` | the wire — `ftpg_finite_of_limit` (sorry-free): finite Krull dimension yields `WellFoundedGT`, hence a `CompleteLattice` around the original operations and compact generation; `ftpg_proof_finite` |
| `Hollow` | the refutation — the hollow lattice meets every hypothesis, has no LUB for the inl-chain; `not_ftpg_statement`, `not_pointSystem`, `ftpg_refuted : False` |
| `Charge` | the charged restatement — `Coordinatization` (the data-level bundle), `seals`, `held_determines`, `limitSeam` (foam's `Seam`, axiom-free in bridges) |

## Notes

- `ftpg_proof_limit : ftpg_statement_limit` (in `Deaxiomatize`) type-checks end
  to end — it reduces to the one labeled residual (`pointSystem_exists`), not
  to the axiom.  The old `ftpg_proof : ftpg_statement` is gone: it proved a
  refuted proposition modulo `sorry`, and a sorry against a false target is
  not a gap, it is a wall wearing a door costume.
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
`fleft_distrib_total` / `fright_distrib_total`: the degenerate branches wanted
`mul_neg`, which is the commutation of the −1-dilation with negation — but at
the single point `I` it is *definitional*, and total associativity spreads it
everywhere; the two Desargues in `MulNeg.lean` are centrally perspective by
construction (their vertex fibers are `m`, `l`, `q`, concurrent at `U`, or the
towers through `C_y`), so the only carving was side-condition bookkeeping.  The
doubling knot reduced to one fresh point and a self-destructing four-point
line.  The wall was never the distributive law; it was the one incidence
`−1 = ν(I)` seen from two sides.
The assembly (`CoordFrame.divisionRing`): no wall at all — the ring was
already closed; the only carve was the frame's existence, and the off-plane
witness `R` was hiding in `h_height` itself: the plane the construction draws
is pinned below the chain's third step, so the fourth step is an atom the
plane cannot reach.  The hypothesis had been carrying the answer since the
statement was first written.
