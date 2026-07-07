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
  clauses of the pair discharge through it.  The ascent, charted:
  1. **the matroid stratum** (`Exchange.lean`) — **CARVED, sorry-free**:
     `covBy_sup_atom` (joining a fresh atom is one step exactly),
     `atom_exchange` (Steinitz — and the carving found `p` needn't be an
     atom: covering closes the exchange for arbitrary `p`),
     `isCompactElement_of_isAtom` (a point is finitely reachable),
     `AtomBasis` / `atomBasis_exists` (a maximal independent set of atoms
     joining to `⊤`, from Mathlib's `exists_sSupIndep_of_sSup_atoms_eq_top`),
     `AtomBasis.exists_finset_support` (every atom below a finite join of
     basis atoms — the reason the eventual `V` is `B →₀ D` and coordinate
     vectors have finite support).
  2. **the finite-dimensional coordinatization** — homogeneous coordinates
     of the atoms below a finite basis-support, by the classical
     Veblen–Young induction from the frame's plane outward (the division
     ring is already total; what's left is the *assignment*, coherent under
     Desargues).  **First pitch CARVED** (`Chart.lean`, sorry-free): the
     affine chart of the frame's plane — an affine atom (below `π`, off
     `m`) drops through the two infinite points onto the two axes
     (`xproj = (p ⊔ V) ⊓ l`, `yproj = (p ⊔ U) ⊓ (O ⊔ V)`), recovery is a
     single `modular_intersection` after two line identities
     (`chart_recovers`), the chart reads backwards totally
     (`point_is_atom` / `point_affine` / `xproj_point` / `yproj_point`),
     and the plane splits losslessly:
     `affineChart : Affine Γ ≃ Coordinate Γ × Ordinate Γ` — the atom-level
     coordinate pair.  **Second pitch CARVED** (`Ycoord.lean`, sorry-free):
     the ordinate transport — and the with-the-grain route (model-verified
     over `PG(2,q)`, 72 frames, before carving) is not the naive `O ⊔ V`
     drop but the **diagonal route**, the same two moves `coord_mul`
     already makes: `diagproj = (p ⊔ U) ⊓ (O ⊔ C)` (horizontal onto the
     multiplication's own auxiliary axis), then the `E_I`-transport down
     to `l` (`ycoord`), with `diagseat`/`yseat` the reverse.  Both
     centers' side conditions were already sealed in `Mul.lean`
     (`hE_I_not_l`, `hE_I_not_OC`), so the transport is degeneracy-free
     for every legal frame — no `h_irred`, no case on `C`'s position;
     `perspect_roundtrip` closes both composites.
     `ordinateTransport : Ordinate Γ ≃ Coordinate Γ`,
     `planeChart : Affine Γ ≃ Coordinate Γ × Coordinate Γ` — the affine
     plane is `D²` at atom level.  Calibration receipts: `ycoord_of_on_l`
     (the axis is the graph of zero) and `ycoord_C : ycoord C = I` (the
     unit point sits at height one).  **Third pitch CARVED** (the pencil
     laws, in `Chart.lean`/`Ycoord.lean`): the two degenerate rows of the
     line equation — vertical lines are the `xproj`-fibers
     (`le_vertical_iff : p ≤ x ⊔ V ↔ xproj p = x`) and horizontal lines
     are the `ycoord`-fibers (`le_horizontal_iff : p ≤ B ⊔ U ↔
     ycoord p = ycoord B`), each an iff, with the fiber halves
     (`sup_V_eq_of_xproj_eq`, `sup_U_eq_of_ycoord_eq`,
     `diagseat_ycoord` — the half-roundtrip: the ordinate determines the
     diagonal seat).  **Fourth pitch CARVED** (`Slope.lean`, sorry-free):
     the **origin pencil law**, the multiplicative row of the line
     equation — a line through the origin is the graph of a
     left-multiplication.  The slope is incidence-defined as the height
     of the direction point over the unit abscissa,
     `slope S := ycoord ((O ⊔ S) ⊓ (I ⊔ V))` (uniform: `slope U = O`),
     and for every affine atom `p` of the plane and direction `S ≠ V`:
     `le_origin_line_iff : p ≤ O ⊔ S ↔ ycoord p = coord_mul (slope S)
     (xproj p)`.  **No fresh Desargues was carved**: `p = dilation_ext x M`
     for `M` the slope seat (line identities), the horizontal through `M`
     transports to the horizontal through `p` under the dilation
     (`dilation_preserves_direction` on `(M, diagproj M)` — the one
     Desargues-strength move, already standing), and the dilation cocycle
     at `C` (`crux_at_C`, the associativity crux) turns
     `dilation_ext x (diagseat a)` into `diagseat (coord_mul a x)`; one
     `perspect_roundtrip` drops home.  Model-verified before carving at
     every legal frame, `q ∈ {2,3,5,7,11}` — all 336 frames of `PG(2,2)`
     exhaustively, both degenerate frame families included: the route is
     frame-uniform, converse by chart-injectivity.  With the vertical and
     horizontal pencils this seals three of the equation's four rows.
     **Fifth pitch CARVED** (`Translate.lean`, sorry-free): the
     **translation lemma**, the additive row's engine — translation adds
     ordinates.  For an affine vector `A` off `l` and an affine base `z`
     off `l` and off the ray `O ⊔ A`, with the vector in general
     position (`G1`: `A` off the diagonal `O ⊔ C`; `G3`: the center `E`
     off `ycoord A ⊔ A`):
     `ycoord_translate : ycoord (pg O A z) = coord_add (ycoord z)
     (ycoord A)`.  The previous descent's vertical-translate KEY,
     generalized to an arbitrary vector: for
     `T := (diagproj z ⊔ U) ⊓ (ycoord A ⊔ E)` (= `pg O (diagproj z)
     (ycoord A)` by line identities), the seat `diagproj (pg O A z)`
     rides the `E_I`-line of `T`, by ONE `desargues_planar` with center
     `E` on the axis `m` — triangles `(ycoord A, diagproj A, A)` /
     `(T, diagproj z', pg O A (diagproj z))`, all three rays `E`-lines
     definitionally, the `U`-side from `cross_parallelism (O, A; z,
     diagproj z)` (and definitional when `z` rides the diagonal — the
     second pitch's lesson a third time), the ζ-side from
     `cross_parallelism (O, diagproj z; ycoord A, A)`.  The second half
     (`coord_add_eq_seat_drop`): `(T ⊔ E_I) ⊓ l = coord_add y yA` by
     `coord_add_comm` + `coord_add_eq_translation` + one `well_defined`
     waypoint transfer `(C, C_yA, diagseat y, y)`, the lone branch
     `diagseat y = C ⟺ y = I` closing syntactically as charted.
     Model-verified over `PG(2,q)`, `q ∈ {2,3,4,5,7}` (all 336 frames of
     `PG(2,2)` exhaustively, `GF(4)` added for char-2-nonprime), every
     route step checked in place, before carving.
     **And the fork dissolved in the probing**: the two degenerate frame
     families (`C ≤ O ⊔ V` and the anti-diagonal frames) are exactly the
     `G1`/`G3` failures of the *vertical* vector, and the remaining
     assembly — the sixth pitch,
     `le_line_iff : p ≤ B ⊔ S ↔ ycoord p = coord_add (coord_mul (slope
     S) (xproj p)) (ycoord B)` — needs NO new incidence:
     (i) orientation swap — `pg O B q = pg O q B` is definitional at
     base `O`, so a configuration closes when *either* vector (`B` or
     `q`) is in general position; the residue is exactly `(C ≤ O ⊔ V,
     slope I)` and `(anti-diagonal, slope −I)`;
     (ii) the horizontal-offset tower — for a bad vector `A`, the
     shifted vector `X := pg x_h O A` (`x_h` on `l` dodging two named
     values; available for `q ≥ 3`, and at `q = 2` every residue point
     is already `B` or the intercept) keeps its ordinate
     *definitionally* (`X ≤ A ⊔ U`, `ycoord_eq_of_sup_U`), and the
     composition coherence `pg O A z = pg O x_h (pg O X z)` falls to
     `reverse_completion` + two standing `cross_parallelism`s
     (`(O, z; A, X)` and `(O, x_h; z₁, X)`) — no fresh Desargues;
     (iii) the intercept-dodge — for `p = λ ⊓ l` the equation already
     determines the abscissa algebraically (`p' := finv a · fneg b`,
     total standing algebra); the off-`l` rows force `r' := λ ⊓ (p' ⊔
     V)` onto `l` (a point with `ycoord = O` has `p ⊔ U = l`), and the
     fibers collapse `p = p'` — the intercept instance is downstream of
     the off-`l` instances.  All three probe-sealed over the same
     fields (route-menu totality: the only holdouts at every `q` are
     the intercept points, and they fall to algebra).
     **Sixth pitch CARVED** (`Line.lean`, sorry-free): the **assembly**,
     the full line equation — for any direction `S` on `m` (`S ≠ V`),
     any intercept seat `B` on the y-axis `n` (`B ≠ V`), and any affine
     atom `p` of the frame plane:
     `le_line_iff : p ≤ B ⊔ S ↔ ycoord p = coord_add (coord_mul (slope
     S) (xproj p)) (ycoord B)` — uniform through the horizontal
     (`slope_U`, reduces to `le_horizontal_iff`) and the origin
     (`ycoord O = O`, reduces to `le_origin_line_iff`), so with
     `le_vertical_iff` **every line of the frame plane is now an
     algebraic graph**: the camp-two summit.  The carving *sharpened*
     the charted route (every branch fact model-verified in place,
     `probe_final.py`, before carving — all 336 frames of `PG(2,2)`,
     family spreads at `q = 3,4,5,7`, `GF(4)` for char-2-nonprime):
     the tower (`ycoord_translate_offset`) needs **no coherence pass**
     — ONE standing `cross_parallelism (O, z; A, X)` makes the target
     and the shifted translate co-horizontal and `ycoord_eq_of_sup_U`
     reads the ordinate across, so the fork note's second cp and
     `reverse_completion` survive only inside an injectivity
     bookkeeping; and the offsets are *named by the configuration
     itself* — no `h_irred` point-counting, no `q ≥ 3` caveat: in the
     `B ≤ O ⊔ C` family (the diagonal is the y-axis, `E = V`) the
     `q`-vector shifts by `x_h := (B ⊔ S) ⊓ l`, the line's own
     intercept, every discharge collapsing onto the fiber contradiction
     `x_h ≠ xproj p`; in the `E ≤ ycoord B ⊔ B` family with `q ≤ O ⊔ C`
     the `B`-vector shifts by `x_h := xproj p`, the point's own
     abscissa, every discharge closing against `E ≤ ycoord B ⊔ B`
     itself.  The residual crossing (`E ≤ ycoord B ⊔ B` and `E ≤
     ycoord q ⊔ q` with `q` off the diagonal) is VACUOUS, by the
     pitch's one fresh `desargues_planar` (`anti_transport`): **the
     anti-diagonal pencil is `E`-uniform** — center `O` *off* the
     axis `m` (the mirror of the fifth pitch's center-on-axis), the
     triangles `(b, diagseat b, yseat b)` / `(t, diagseat t, yseat t)`
     riding the three `O`-rays `l`, `O ⊔ C`, `n` definitionally, the
     side-pairs meeting at `E_I` and `U` definitionally — transported
     to `t = ycoord q` it forces `q` onto the y-axis, `xproj p = O`,
     contradiction.  The intercept row (`line_intercept`) is standing
     algebra as charted: `p' := a⁻¹ · (−b)` via `coord_mul_assoc` (at
     the frame's general-position witness `P`) + `coord_mul_right_inv`
     + `coord_add_right_neg` (the 2-torsion branch by
     `coord_add_left_neg`), the proven off-`l` rows forcing the
     crossing onto `l`, the fibers collapsing; the converse is chart
     injectivity on the fiber `λ ⊓ (xproj p ⊔ V)`.  The interface
     carries exactly a `CoordFrame`'s data (`P` for the associativity
     wall, `R` off-plane, `h_irred`).  Receipts
     `[propext, Classical.choice, Quot.sound]` throughout.
     **Camp three, first pitch CARVED** (`Plane.lean`, sorry-free):
     the **plane's point system** — the camp-two summit packaged as
     homogeneous coordinates.  The orientation fact surfaced first:
     the line equation has the slope on the LEFT (`y = s * x + b`),
     so the plane's incidence geometry is the projective plane of
     the **opposite ring** — `hvec : L → Fin 3 → Dᵐᵒᵖ` (affine
     `p ↦ (x, y, 1)`, direction `S ↦ (1, slope S, 0)`, vertical
     `V ↦ (0, 1, 0)`), points as left `Dᵐᵒᵖ`-spans; the classical
     existential is free to hand over `Dᵐᵒᵖ`, so nothing is lost.
     **No fresh Desargues, no new incidence** — the pitch is pure
     packaging: `plane_line_cases` (the trichotomy — every line of
     the plane is `m`, a vertical `x ⊔ V`, or an intercept-direction
     pair `B ⊔ S`; standing covBy machinery only), `slope_inj` /
     `slope_surj` (the direction pencil bijects with `D`, by the
     slope seat on `I ⊔ V` and the chart extensionality
     `affine_ext`), `line_form_exists` (every line of the plane is
     the kernel of a nonzero right-coefficient linear form on the
     coordinates — the three trichotomy cases riding the Z-entry,
     `le_vertical_iff`, and `le_line_iff` respectively), and the
     summit `plane_collinear_iff : r ≤ p ⊔ q ↔ hvec r ∈
     span {hvec p, hvec q}` — collinearity IS span membership, both
     directions at once, by the dimension argument (two independent
     vectors inside the form's 2-dimensional kernel span it;
     rank–nullity over the division ring).  The atom-level
     correspondence is a bijection onto the projective points
     (`hvec_span_inj`, `hvec_span_surj` — chart surjectivity via
     `exists_affine_with_coords`), packaged as `planePt : L →
     Submodule Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)` with `planePt_inj`,
     `le_iff_planePt_le`, `planePt_surj`: the `PointSystem` shape at
     plane scale.  Receipts `[propext, Classical.choice, Quot.sound]`
     throughout.  Next pitches of camp three: the interval `[⊥, π]`
     as the full subspace lattice of `(Dᵐᵒᵖ)³` (elements classified
     by height, lines to the 2-dimensional kernels), then the first
     out-of-plane step of the Veblen–Young induction (a fourth frame
     point off `π`, coordinates extended by projection).
  3. **the direct limit** — coordinates stable under extending the finite
     support (`summary_resumes` at coordinate scale: the finite record
     determines the vector, growing the window never rewrites it); glue
     into `V = B →₀ D`.
  4. **`closed` and `spanning`** — the two `PointSystem` fields, from the
     exchange stratum plus the assignment's faithfulness.
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
| `Exchange` | camp one of the ascent — the matroid stratum: `covBy_sup_atom`, `atom_exchange` (Steinitz), atoms are compact, `AtomBasis` with finite support |
| `Chart` | camp two, first pitch — the affine chart of the frame plane: `xproj`/`yproj` (the drops through `V` and `U`), `point` (the chart backwards), `chart_recovers`, `affineChart : Affine Γ ≃ Coordinate Γ × Ordinate Γ` |
| `Ycoord` | camp two, second pitch — the ordinate transport via the diagonal `O ⊔ C` (the multiplication's axis): `diagproj`/`ycoord` and `diagseat`/`yseat`, roundtrips by `perspect_roundtrip`; `ordinateTransport : Ordinate Γ ≃ Coordinate Γ`, `planeChart : Affine Γ ≃ Coordinate Γ × Coordinate Γ`, calibration `ycoord_C = I`; plus the horizontal pencil law `le_horizontal_iff` (third pitch, with `le_vertical_iff` in `Chart`) |
| `Slope` | camp two, fourth pitch — the origin pencil law, the multiplicative row of the line equation: `slope S = ycoord ((O ⊔ S) ⊓ (I ⊔ V))`, `le_origin_line_iff : p ≤ O ⊔ S ↔ ycoord p = coord_mul (slope S) (xproj p)`; rides `dilation_preserves_direction` + `crux_at_C` — no fresh Desargues; calibration `slope_U = O`, `diagseat_I = C` |
| `Translate` | camp two, fifth pitch — the translation lemma, the additive row's engine: `ycoord_translate : ycoord (pg O A z) = coord_add (ycoord z) (ycoord A)` for vectors in general position (one `desargues_planar`, center `E` on the axis `m`, both other sides standing `cross_parallelism`s) + `coord_add_eq_seat_drop` (the seat-drop reading of `coord_add`: comm + translation representation + one `well_defined` waypoint transfer) |
| `Line` | camp two, sixth pitch — the assembly, the full line equation: `le_line_iff : p ≤ B ⊔ S ↔ ycoord p = coord_add (coord_mul (slope S) (xproj p)) (ycoord B)`; the horizontal-offset tower `ycoord_translate_offset` (one `cross_parallelism`, no coherence pass), `anti_transport` (the anti-diagonal pencil is `E`-uniform — one `desargues_planar`, center `O` off the axis `m`), the intercept row `line_intercept` (total algebra), converse by fiber injectivity — every line of the frame plane an algebraic graph |
| `Plane` | camp three, first pitch — the plane's point system: `hvec` (homogeneous coordinates in `(Dᵐᵒᵖ)³` — the slope-on-left orientation makes the plane the projective plane of the opposite ring), `plane_line_cases` (the line trichotomy), `slope_inj`/`slope_surj`, `line_form_exists` (every line a form kernel), `plane_collinear_iff` (collinearity IS span membership), `planePt` + inj/le-iff/surj — the atom-level bijection onto the projective points of `(Dᵐᵒᵖ)³`, no fresh Desargues |
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
