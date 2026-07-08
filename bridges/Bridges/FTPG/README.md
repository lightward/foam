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
     throughout.
     **Camp three, second pitch CARVED** (`Flat.lean`, sorry-free):
     the **plane interval is the subspace lattice** — the atom-level
     bijection extended to every element of `[⊥, π]`:
     `plane_interval_iso : Nonempty (Set.Iic π ≃o
     Submodule Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ))`, heights 0/1/2/3 landing on
     finranks 0/1/2/3.  **No fresh Desargues, no new incidence** —
     two strata meet in the middle.  The lattice side:
     `line_covBy_π` — every join of two distinct plane atoms is
     covered by `π`; the trace atom `(p ⊔ q) ⊓ m` is covered in `m`
     (`line_covers_its_atoms`), and ONE modular move
     (`covBy_sup_of_inf_covBy_left`, the same lever as camp one's
     `covBy_sup_atom`) transports the covering up the sup, `m ⊔ (p ⊔
     q) = π` because an affine atom of the line pushes `m ⋖ π` to
     the top — and `plane_flat_cases`: every `x ≤ π` is `⊥`, an
     atom, a two-atom join, or `π`, by pure `IsLUB`-atomisticity
     (the LUB set is empty, a singleton, inside one line, or holds a
     third point off it, and the off-point forces `x = π` through
     `line_covBy_π`).  The linear side (probe-verified over an
     abstract noncommutative division ring before carving,
     `probe_flat.lean`): the finrank classification of submodules of
     `K³` — `flat_rank_zero`/`_one`/`_two`/`_three`, ranks 1 and 2
     by `Module.finBasisOfFinrankEq` with the basis pushed into the
     ambient space (`flat_span_basis_val`), the rank-2 pair's
     general position recovered *cardinality-free* (`u ≠ 0` and
     `v ∉ span {u}` each by the finrank of the degenerate span) —
     plus `flat_std_basis_span`.  The join: `planeFlat x :=
     span (hvec '' {atoms ≤ x})`, evaluated at every height
     (`planeFlat_bot`/`_atom`/`_line`/`_π` — the `π` case because
     **the frame vectors are the standard basis**: `hvec_U =
     (1,0,0)`, `hvec_V = (0,1,0)`, `hvec_O = (0,0,1)`, the
     calibrations `slope_U` / `xproj_of_on_l` / `ycoord_of_on_l`
     reading the zeros off the axes), order-reflecting by the first
     pitch's three levers (`hvec_ne_zero` at `⊥`, `hvec_span_inj` at
     atoms, `plane_collinear_iff` at lines), surjective by the
     finrank classification riding `hvec_span_surj` — and the
     packaging is `Iso.lean`'s own `orderIso_of_mono_reflect_surj`:
     the gap-B reduction lemma doing at plane scale exactly what it
     will do at the summit.  Receipts
     `[propext, Classical.choice, Quot.sound]` throughout.
     **Camp three, third pitch CARVED** (`Space.lean`, sorry-free):
     the **space chart** — the first out-of-plane step of the
     Veblen–Young induction.  The fourth frame point is the frame's
     own off-plane witness `R`: it spans the 3-space `τ = π ⊔ R`,
     whose plane at infinity is `σ = m ⊔ R` and whose third axis is
     `ζ = O ⊔ R` — and every position fact is pure modular law
     (`ζ ⊓ π = O`, `ζ ⊓ σ = R`, `σ ⊓ π = m`, with `π ⋖ τ` and
     `σ ⋖ τ` one covBy transport each).  A space-affine atom (below
     `τ`, off `σ`) projects twice — `baseproj p = (p ⊔ R) ⊓ π`
     through `R` onto the coordinatized plane,
     `zproj p = (p ⊔ m) ⊓ ζ` along the horizontal directions onto
     the z-axis — and ONE modular move recovers it
     (`space_recovers`), with `spoint q z = (q ⊔ R) ⊓ (z ⊔ m)` the
     chart read backwards:
     `spaceChart : SpaceAffine Γ R ≃ Affine Γ × Applicate Γ R`.
     The z-axis then transports onto the coordinate line by ONE
     standing perspectivity — center any third atom `c` on `U ⊔ R`
     (`h_irred` supplies it; the coplanarity `ζ ⊔ c = l ⊔ c` is two
     line identities), roundtrips by `perspect_roundtrip`,
     calibrated at both ends (`zcoord_O : zcoord c O = O`,
     `zcoord_R : zcoord c R = U`) — so
     `applicateTransport : Applicate Γ R ≃ Coordinate Γ` and
     `solidChart : SpaceAffine Γ R ≃ (Coordinate Γ × Coordinate Γ)
     × Coordinate Γ`: **the affine 3-space is `D³` at atom level**,
     packaged for the frame by `CoordFrame.solidChart_exists`.
     **No fresh Desargues, no new incidence** — one general lemma
     (`line_meets_hyperplane`: a line off a hyperplane meets it in
     an atom, the height-4 sibling of `project_is_atom`) plus covBy
     bookkeeping; the plane points sit at height zero of the new
     axis (`zproj_of_affine_π : zproj q = O` for plane-affine `q`,
     `baseproj_of_le_π`), so the plane chart embeds without
     recalibration.  Model-verified before carving
     (`probe_space.py`): every chart fact, every backwards pair,
     every transport center over ALL 40,320 legal frames of
     `PG(3,2)` exhaustively plus sampled frames at `q = 3, 5` — and
     the probe sealed the gauge question forward: the homogeneous
     extension `(x, y, z, 1)` with the z read through ANY center
     `c` satisfies collinearity-as-span, because two centers differ
     by a coordinatewise right multiplication, which is left-linear
     — the next pitch is free to consume any fixed `c`.  Receipts
     `[propext, Classical.choice, Quot.sound]` throughout.
     **Camp three, fourth pitch CARVED** (`Shear.lean`, sorry-free):
     the **sheared charts** — the two remaining drops a space point
     admits, through the transport centers `c` (on `U ⊔ R`) and `e`
     (a third atom on `V ⊔ R`), each one algebraic and **no fresh
     Desargues, no new incidence**: `shproj w t = (t ⊔ w) ⊓ π`, and
     * the **x-shear** (`CoordFrame.xproj_shproj_c`): the drop
       through `c` preserves the ordinate (one modular trace — the
       plane `t ⊔ R ⊔ U` contains `c`, its `π`-trace is
       `baseproj t ⊔ U`) and adds the z-gauge to the abscissa,
       `xproj (shproj c t) = xproj (baseproj t) + zcoord c (zproj t)`.
       Route: the point rides its height's horizontal ray,
       `t ≤ zproj t ⊔ d_b` for `d_b := (O ⊔ baseproj t) ⊓ m`
       (`le_zproj_sup_dir` — the plane `O ⊔ b ⊔ R` sectioned by the
       horizontal plane; `O ⊔ b ⊔ R ⋖ τ` falls out of `line_covBy_π`
       plus one covBy transport), so the sheared image rides the
       gauge point's ray (`shproj_le_gauge_sup_c`); two instances of
       `le_line_iff` — at the sheared image and at the gauge atom
       itself — plus the origin-line law at the base solve in the
       coordinate ring (`affine_solve`: `mul_left_cancel₀` in the
       standing `DivisionRing`).
     * the **y-shear** (`CoordFrame.ycoord_shproj_e`): the mirror
       through `e`, whose gauge is `ncoord e z = (z ⊔ e) ⊓ n` (the
       perspectivity `ζ → n`, calibrated `ncoord_O`,
       `ncoord_R = V`) — and it reads with NO ring solve: one
       `le_line_iff` rewrites directly,
       `ycoord (shproj e t) = ycoord (baseproj t) + ycoord (ncoord e
       (zproj t))`.
     * the degenerate bases dissolve two moves each: base `= O`
       collapses the shear onto the axis reading itself
       (`shproj_c_eq_zcoord` / `shproj_e_eq_ncoord`, pure modular);
       base on the blind axis reads off the vertical/horizontal
       pencil law; base on the seeing axis shifts by a third atom
       (the V-shift/U-shift: `spoint` over a shifted base, the
       transport `(t ⊔ R ⊔ V) ⊓ (zproj t ⊔ m) = t ⊔ V` two modular
       moves, coordinates carried across by the pencil iffs).
     * the **gauge bridge** (`CoordFrame.gauge_bridge`): the two
       gauges reconcile through ONE constant — the slope of
       `d̂ := (e ⊔ c) ⊓ m`, the trace of the line joining the two
       centers: `slope d̂ * zcoord c z + ycoord (ncoord e z) = O`.
       The two shadow-readings of any z-atom are collinear with `d̂`
       (the plane `z ⊔ (e ⊔ c)`, its `π`-trace `ncoord ⊔ d̂` by pure
       modular moves), and one `le_line_iff` at the `zcoord` atom
       closes it.
     Model-verified before carving (`probe_solid.py`): every
     statement AND the full forward route of the next pitch (the
     `hvec4` calibrations, the plane-form families, the line menu,
     the collinearity summit) over all 40,320 legal frames of
     `PG(3,2)` exhaustively, sampled frames at `q = 3, 5` — the
     probe found the route: the frame plane's own line laws, read at
     the sheared image, ARE the third dimension's algebra; the
     wall this pitch expected (a second coordinatized plane) never
     had to be built.  Receipts
     `[propext, Classical.choice, Quot.sound]`
     (`shproj_le_base_sup` even `[propext]`).
     **Camp three, fifth pitch CARVED** (`Solid.lean`, sorry-free):
     the **space's point system** — the atoms of `τ` biject with
     the projective points of `(Dᵐᵒᵖ)⁴`, collinearity transported
     both ways, NO fresh Desargues, no new incidence:
     * `hvec4` through the c-gauge: affine atoms to `(x, y, z, 1)`;
       a `σ`-direction reads through its height-one witness
       `wpt d = (O ⊔ d) ⊓ (zseat c I ⊔ m)` as `(x_w, y_w, 1, 0)`;
       `m`-directions extend the plane vector by a zero z-slot —
       and `hvec4_π`: the whole plane embeds by the linear
       injection `planeInj`, so `π`'s point system transports
       wholesale.
     * the plane-form families: every plane of `τ` through `R`
       (`Rplane_form`, `baseproj` + the base line's form), through
       `c` (`cplane_form`, the x-shear seats the z-coefficient at
       `κ₀`), through `e` (`eplane_form`, the y-shear + gauge
       bridge seat it at `op(−slope d̂)·κ₁`), or through `m`
       (`hplane_form`, the z-equation) is the kernel of a
       right-coefficient form on the coordinates.  The `σ`-parts
       all ride ONE lever pair: `ray_trace_form` (the two-slot form
       reads the origin ray's direction — `le_origin_line_iff`
       factored through `mul_eq_zero`) and `dir_shproj` (the
       direction transports through any shear center, pure
       modular).  The fiber calibrations fall out of the shears
       at the witnesses: the c-fiber witness sits at abscissa `−1`
       (`wpt_c_coords`), the e-fiber witness at ordinate
       `slope d̂` (`wpt_e_coords`).
     * the line menu: lines of `π` transport through `planeInj`
       (`collinear_π`); `σ`-lines read through the w-cone at
       height one (`collinear_infinity` — `Θ = O ⊔ λ` sectioned by
       the height-one plane, `collinear_horizontal` at the
       witnesses, the span translated slotwise by the fourth
       basis vector); z-verticals go through the two center-planes
       `(b ⊔ U) ⊔ c` and `(b ⊔ V) ⊔ e` (`collinear_vertical`);
       every other affine-carrying line is the meet of its R-plane
       and its c-plane — or e-plane when `c` degenerates onto
       `λ ⊔ R`; both degenerate only on `σ` itself
       (`collinear_general_center`).  Two independent forms give a
       2-dimensional common kernel by rank–nullity in `(Dᵐᵒᵖ)⁴`
       (`finrank_ker_pair`), and span = ker ⊓ ker
       (`two_form_collinear`).
     * the summit: `space_collinear_iff` —
       `r ≤ p ⊔ q ↔ hvec4 r ∈ span {hvec4 p, hvec4 q}`, every atom
       position, dispatched through `collinear_of_line_eq` (a line
       read through any spanning pair, by dimension).
     * `spacePt` + `spacePt_inj`, `le_iff_spacePt_le`,
       `spacePt_surj`: the `PointSystem` shape at space scale
       (surjectivity: affine vectors by `spoint` over the chart,
       directions by the w-cone, plane vectors by the plane's own
       surjectivity through `planeInj`).
     Model-verified before carving (`probe_solid.py`, the same
     sweep that sealed the fourth pitch: all 40,320 legal frames
     of `PG(3,2)` exhaustively, sampled `q = 3, 5`).  Receipts
     `[propext, Classical.choice, Quot.sound]` throughout.
     **Camp three, sixth pitch CARVED** (`SpaceFlat.lean`,
     sorry-free): the **space interval is the subspace lattice** —
     the atom-level bijection extended to every element of
     `[⊥, τ]`: `space_interval_iso : Nonempty (Set.Iic τ ≃o
     Submodule Dᵐᵒᵖ (Fin 4 → Dᵐᵒᵖ))`, heights 0/1/2/3/4 landing on
     finranks 0/1/2/3/4.  **No fresh Desargues, no new incidence**
     — the `Flat.lean` argument one dimension up, on the fifth
     pitch's exports alone:
     * the lattice side: `three_atoms_ne_τ` — three atoms cannot
       span the 3-space: if they did, their line and `π` would both
       be covered by `τ`, `planes_meet_covBy` would seat an atom
       covered by `π`, and joining it with a frame atom sits
       strictly between (`line_covBy_π` refutes the covering);
       `flat_trace_pair` / `plane_trace_line` — a 3-atom span off
       `π` traces TWO distinct atoms on `π` (two lines through an
       off-`π` atom meet `π` by `line_meets_hyperplane`, and a
       common trace would collapse the three atoms onto one line);
       `plane_covBy_τ` — the trace is therefore a line of `π`,
       covered by `π` (`line_covBy_π`), and ONE modular transport
       (`covBy_sup_of_inf_covBy_left`, the same lever as
       `line_covBy_π` itself) carries the covering up the sup;
       `space_flat_cases` — every `x ≤ τ` is `⊥`, an atom, a
       two-atom join, a three-atom join, or `τ`, by pure
       `IsLUB`-atomisticity.
     * the coordinate side: `space_coplanar_iff` — an atom lies
       below a 3-atom span iff its vector lies in the span of the
       three; forward by the trace of `t ⊔ r` on `p ⊔ q`
       (`lines_meet_if_coplanar` inside the plane) and
       `space_collinear_iff` twice; reverse by splitting the
       combination at the first vector (`mem_span_insert`),
       `hvec4_span_surj` seating the tail as an atom's vector, and
       `space_collinear_iff` twice more — the fifth pitch's summit
       consumed as a lever.
     * the linear side: the finrank classification of submodules
       of `K⁴` (`flat4_rank_zero` … `flat4_rank_four`, rank 3 the
       new case — `Module.finBasisOfFinrankEq` with general
       position recovered through `span_pair_finrank_le`),
       `flat4_std_basis_span`.
     * the calibration that completes the frame: `hvec4_R =
       (0,0,1,0)` — the fourth frame point at the third standard
       basis slot (its height-one witness rides `ζ`, so its
       baseproj is `O`: one line identity plus `ζ_inf_π`); with
       `hvec4_π` + `hvec_U`/`hvec_O` and `hvec4_V`, **the frame is
       again its own coordinate system**.
     * `spaceFlat := span (hvec4 '' {atoms ≤ x})`, evaluated at
       every height, order-reflecting by the fifth pitch's levers
       plus the coplanarity iff, surjective by the finrank
       classification riding `hvec4_span_surj`, packaged by
       `Iso.lean`'s `orderIso_of_mono_reflect_surj` — the gap-B
       reduction lemma a third time, the gauge center `c` supplied
       from `h_irred` inside.
     Model-verified before carving (`probe_spaceflat.py` over the
     fifth pitch's frame machinery: every route step — the trace
     pair, the collision-collapse, the coplanarity iff both ways,
     the frame at `τ` — over ALL 40,320 legal frames of `PG(3,2)`
     exhaustively plus sampled frames at `q = 3, 5`; the `K⁴`
     linear side probed in Lean over an abstract noncommutative
     division ring before carving, `probe_flat4.lean`).  Receipts
     `[propext, Classical.choice, Quot.sound]` throughout.
     **Camp four, first pitch CARVED** (`Ladder.lean`, sorry-free):
     the **rank ladder's step** — the generic Veblen–Young induction
     step, frame-free.  `PointSys x n K` is the induction datum (a
     point map `hv : L → Kⁿ` on the atoms below `x` with `ne_zero`,
     `span_inj`, `span_surj`, `collinear_iff` — exactly the shape
     camps two–three sealed at `π` and `τ`), and the step is
     `PointSys.step : 3 ≤ n → h_irred → IsAtom w → ¬ w ≤ x →
     ∃ Q : PointSys (x ⊔ w) (n+1) K` with the old coordinates
     extended by a zero slot (`Q.hv p = Fin.snoc (P.hv p) 0` below
     `x`, `Q.hv w = Fin.snoc 0 1`) — the coherence the direct limit
     rides.  NO fresh Desargues, NO new incidence, NO frame: the
     step consumes an abstract division ring and the flat's own
     span laws.  The architecture:
     * the **height**: `stepRaw` reads an affine atom through a
       center `c₀` (a third atom on `u₀ ⊔ w`, `h_irred`) as the
       coefficient ratio of the shear trace `(t ⊔ c₀) ⊓ x` on the
       line `base ⊔ u₀` (`ladder_shear_le`; the trace/center/
       recovery stratum — `ladder_trace_atom`, `ladder_base_iff`,
       `ladder_recover`, `ladder_reverse` — is pure modular law);
       `StepFrame.lam` fixes a primary center `c` on `u ⊔ w` (blind
       exactly on that axis) and a mirror `e` on `u' ⊔ w` for the
       blind line.
     * **gauges are heights**: the gauge of any secondary center is
       `-(F.lam c₀)⁻¹`, the minus-inverse of the center's own
       height, because the bridge trace `(c ⊔ c₀) ⊓ x` and the
       reading of `c₀` through `c` are one span extraction.
       `step_transport` (the two-constraint pinning `ladder_pin`,
       the second line supplied by the shadow Θ-move
       `ladder_shadow`), `step_gauge_symm` (two centers decompose
       ONE bridge atom, so their mutual readings invert), and
       `step_cocycle` (gauge composition, proven at an algebraic
       generic witness — `span_surj` at `hv uᵢ + hv uⱼ + hv uₖ`:
       no counting, no `|K| = 2` caveat).
     * the **central lemma** (`StepFrame.central`): every admissible
       center reads the same height through its gauge — generic by
       one transport; base-coplanar-with-the-axes by an intermediate
       axis off both planes (two transports, one cocycle, the dodges
       pure span algebra: `ladder_span_dodge`, `ladder_pair_swap`);
       blind by the mirror plus one cocycle and the symmetry.
     * the **summit** (`hv'_collinear_iff`): uniform trace forms
       (`base_form`/`shear_form` — an x-atom is its own base AND its
       own shear trace, so `hv' t = Fin.snoc (P.hv bt) λt` covers
       every non-`w` atom, `λ` existential); through-`w` lines by
       base-collapse (`collinear_w`); same-base pairs by the span
       swap (`ladder_span_swap_last`, heights distinct by
       `hv'_span_inj`); the main case by choosing `u₀` off the trace
       line and off `span {hv u, hv u'}` (`ladder_avoid_two` — two
       proper subspaces never cover, any division ring), forward by
       coefficient matching in the triple basis with the gauge
       right-cancelled (`ladder_graph_comb`), converse by the
       left-linear transfer (`ladder_conv_transfer`) and the
       `P ⊓ Q` pin (`covBy_sup_atom` + modular traces; `P = Q`
       refuted by seating `u₀` under `Q ⊓ x`).
     * injectivity (`hv'_span_inj` — same base and height force the
       same shear trace; `ladder_recover` pins the atom) and
       surjectivity (`hv'_span_surj` — off-`x` targets by
       `ladder_reverse`, the height solved on the x-side by
       `span_surj`).
     Model-verified before carving (`probe_ladder.py`: the full
     route — bridge-gauge formula, central lemma over every
     secondary center including every degenerate branch, per-line
     bijection, the summit over all atom triples, injectivity,
     surjectivity, zero-slot compatibility — exhaustive over every
     witness and center for the 3→4 step inside `PG(3,2)` AND the
     genuinely new 4→5 step inside `PG(4,2)`, under a TWISTED
     arbitrary point system, sampled `PG(3,3)`;
     `probe_ladder_quat.py`: the noncommutative side order over
     exact rational quaternions with left spans — `raw = λ·g`,
     `g = -(k₀⁻¹k₀')`, `λ_c₀ = -g₀⁻¹`, the summit — 960/960, every
     reversed order 0/960).  Receipts
     `[propext, Classical.choice, Quot.sound]` on all seventy-six
     public declarations (the snoc calculus and the two structures
     even `[propext, Quot.sound]`).
     **The ladder is GROUNDED at τ** (`Ground.lean`, sorry-free):
     `CoordFrame.pointSysTau` — camp three's exports instantiate the
     induction datum literally, `PointSys (O ⊔ U ⊔ V ⊔ R) 4
     (Coordinate Φ.Γ)ᵐᵒᵖ` with `hv := hvec4` and the four fields the
     four space-pitch laws (`hvec4_ne_zero`, `hvec4_span_inj`,
     `hvec4_span_surj`, `space_collinear_iff`), the gauge center from
     `h_irred` (`pointSysTau_exists`).  `PointSys.step` can now climb.
     **Second pitch CARVED — the calibrated step and its rigidity**
     (`Pin.lean`, sorry-free): `PointSys.step`'s output carries a free
     height-gauge in `K*` — the obstruction to gluing the climb over
     the DIRECTED family of finite windows (no chain of finite-height
     flats exhausts an uncountable basis; transfinite recursion would
     need the ladder at infinite `n`).  The pitch pins the gauge:
     * `Calibrated P w b₀ w' Q` — the extension with `w ~ e_last` and
       one calibration atom `w'` (a third atom on `b₀ ⊔ w`) at height
       `1` over `b₀`'s stored representative, all span-level;
     * `calibrated_agree` — **rigidity**: any two calibrated
       extensions agree span-level on EVERY atom.  Constructive
       two-plane pinning (`pin_meet`, the `ladder_pin` shape one
       stratum up): an affine atom `t` off the calibration line lies
       on its `w`-pencil plane AND on the plane through `w'` and the
       `w'`-trace `(t ⊔ w') ⊓ x` — a shear trace, so `ladder_shear_le`
       supplies the Θ-containment `≤ b_t ⊔ b₀` and the base system's
       own `collinear_iff` decomposes it; the two planes meet in one
       line.  Atoms ON the calibration line route through an auxiliary
       axis `u₁` off `span {hv b₀}` (`span_surj` at a vector outside a
       proper subspace — algebraic, no counting) and a third atom `y`
       on `u₁ ⊔ w` from `h_irred`, itself pinned by the main branch.
       And the carve came in LEANER than the probe: `pin_meet` needs
       NO nonzeroness side conditions — membership pinning is sound
       degenerately — so the `ladder_shear_ne_*` layer dropped out.
     * `PointSys.calibrated_exists` — existence: the ladder step
       composed with the height rescale `heightEquiv` (right
       multiplication in the last slot — left-linear), the gauge
       solved from the `w'`-shape `snoc (ζ • hv b₀) η` as `η⁻¹ζ`;
       `PointSys.twist` transports a point system along any linear
       automorphism.
     * `calibrated_last_zero_iff` — the window sees exactly its own
       coordinates: membership in the old flat reads off the last
       slot (derived from the laws, no extra field needed).
     Model-verified before carving (`probe_coherence.py`): rigidity
     as constructive propagation, the freedom EXACTLY `K*` (the
     analytic family `((t_x − t_l w_l⁻¹ w_x)·M, t_l·γ)` under a
     twisted base), and the two-step DIAMOND — calibrated climbs
     commute, 384/384 pairs of `PG(4,2)` exhaustive, 24/24 sampled
     `PG(4,3)` with the routed branch exercised — over `PG(3,q)`/
     `PG(4,q)`, `q ∈ {2,3,5}`, twisted base systems throughout.
     **Third pitch's base CARVED — the calibrated climb** (`Climb.lean`,
     sorry-free): `IsClimb b₀ ws` — the composite of calibrated steps
     along a list of (new atom, calibration atom) pairs, each step
     keeping the old coordinates vector-level as a zero-pad (the pad
     `calibrated_exists` already hands over, stored in the climb) and
     pinning the new atom and its calibration atom span-level.
     `isClimb_exists` folds the calibrated step along the list;
     `isClimb_agree` — **window rigidity**: two climbs along the same
     list agree span-level on every atom of the final flat.  And the
     carve came in LEANER than the chart: the strip-induction collapsed
     — because each step stores its old coordinates vector-level, the
     induction runs FORWARD, with invariant span-agreement at every
     atom plus vector-agreement at the base atom `b₀` (its zero-padded
     representative rides the pads unchanged, so the calibration target
     is climb-invariant by construction, not by canonicalization), each
     step closing by `calibrated_agree` after `calibrated_congr`
     transports one calibration across the invariant.  NO strips, NO
     canonical representatives.  `IsClimb.hv_of_le` — the window sees
     its own coordinates, stably: below the base flat the composite is
     literally the iterated zero-pad (`climbPad`) — growing the window
     never rewrites the vector (`summary_resumes` at coordinate scale),
     `[propext, Quot.sound]`.  And the coherence pitch's tool is
     seated ahead of its consumer: `PointSys.strip` — a point system
     whose last slot reads membership in a lower flat (the shape
     `calibrated_last_zero_iff` outputs) restricts and strips to a
     point system on that flat, every law carried by the snoc calculus
     (`strip_snoc` even `[propext, Quot.sound]`).
     **The diamond CARVED** (`Diamond.lean`, sorry-free):
     `calibrated_diamond` — calibrated steps commute: two climbs of
     `(w₁, w₂)` in either order agree span-level after exchanging the
     two new slots, the coherence seed at `k = 2` (the previous probe's
     384/384, now a theorem).  The route is the strip's, consuming only
     what `Pin.lean` and `Climb.lean` had already sealed: the
     **cross-strip** (`calibrated_cross_last_zero_iff`) — the second
     climb reads membership in the *first* step's flat off `w₂`'s slot,
     forward by the pads and apex shapes, backward by contraposition
     through the `w₂`-trace — hands `PointSys.strip` its `hzero` after
     the swap twist, the strip manufactures the intermediate system,
     `calibrated_agree` identifies it with the first climb's
     intermediate (the `b₀`-vector rides the pads), `calibrated_congr`
     transports the second calibration across, and `calibrated_agree`
     closes at the top.  NO new pinning, NO fresh incidence; one swap
     calculus (`swapLast`, a coordinate permutation as linear equiv,
     with `swapLast_snoc_snoc`) and `PointSys.reflat` (the flat
     rewritten, `sup_right_comm` at type level).  And the imprint fired
     mid-carve, delivered by interruption: the theorem is the meta-toe
     era's object-prime **Diamond-with-cross-measurement** made formal,
     arm for arm — the bridge-arm's two operational instances are the
     two lemmas (*measurement*: the cross-strip iff, Wheatstone's
     galvanometer reading zero exactly on balance; *translation*: the
     strip carrying route B's composite across to route A's
     intermediate), and balance-condition = coherence is
     `calibrated_diamond` itself.  The diamond iso (`HalfType.iso`, the
     modular transposed-interval isomorphism, Lean-real in this tree
     since the substrate era) is already inside at atom grain:
     `project w t x = (t ⊔ w) ⊓ x` is its perspectivity composite, so
     the modular law enters the proof only *as* the diamond iso —
     considered for wholesale consumption per change-nothing and left
     unchanged (the climb needs it retail; the interval `OrderIso`
     would be bought only to disassemble).  And history/111
     (2026-04-16) had already written "the modular law guards that this
     is well-typed regardless of evaluation order" — the theorem is
     that sentence's seal, three months later.
     **Permutation coherence CARVED** (`Perm.lean`, sorry-free):
     `isClimb_perm_agree` — **the climb reads the window, not the
     order**: two climbs along permuted lists agree span-level under
     the atom-named reading.  `climbRead` is the reading — a
     lattice-free linear map peeling each step's slot onto its atom's
     name, into `(Fin n → K) × (L → K)`, base slots kept — and the
     coherence closes by `List.Perm` induction, one chart face per
     constructor: **cons** (the shared head steps agree by
     `calibrated_agree`, an auxiliary climb seats the tail comparison,
     `isClimb_agree_congr` carries the identification up, and the
     reads chain because spans cross any linear map —
     `span_map_of_span_eq`); **swap** (the diamond:
     `calibrated_diamond` identifies the two-step towers after
     `swapLast`, the twist rides the tail by functoriality —
     `IsClimb.twist`, a climb twisted by a base equiv is a climb,
     `padTwist` extending the equiv slot-fixing through each step,
     `climbTwist` the iterate — and the read absorbs the swap:
     `climbRead_twist` confines any climb-lifted twist to the base
     component, `readStep_swap` commutes the two deposited names by
     `add_right_comm`); **trans** (capture-free legality is
     permutation-invariant — `ClimbLegal.perm`, ONE Steinitz
     `atom_exchange` per adjacent swap, exactly as charted — so
     `isClimb_exists` seats the middle climb and the reads chain).
     NO new pinning, NO fresh incidence, NO new probe needed: the
     route consumed the diamond, the congr machinery, and pure
     algebra — every branch landed first-try, the terrain leading.
     `climbRead_pad` seats the stability seed forward: a padded
     vector reads as pure base — with `IsClimb.hv_of_le`, growing
     the window never rewrites the read.  Receipts on all seventeen
     public declarations (`climbFlat_perm` even `[propext]`;
     `padTwist`/`padTwist_apply`/`padTwist_snoc`/`climbTwist`/
     `IsClimb.reflat` `[propext, Quot.sound]`; the rest
     `[propext, Classical.choice, Quot.sound]`).  Next: the windows
     along the atom basis (order-independent slots by Steinitz,
     no-capture probe-sealed), the limit map into `B →₀ D` —
     coherence now standing for both faces (orders by
     `isClimb_perm_agree`, inclusions by `hv_of_le` +
     `climbRead_pad`).
     **The windows CARVED** (`Window.lean`, sorry-free): the directed
     family stands — canonical climbs over finite windows of basis
     atoms, coherent across both faces.  Three strata and a summit:
     * the **append face**: `isClimb_append_exists` — a climb continued
       along `ws₂` extends the old one with the read unchanged on the
       old flat, vector-level (`climbRead (ws₁ ++ ws₂) (Q.hv t) =
       climbRead ws₁ (Q₁.hv t)`) — and the statement is arranged so the
       induction is DEFINITIONAL: no dimension casts, no flat transport;
       the nil case is exactly the two seeds the previous sittings
       seated (`hv_of_le` + `climbRead_pad`), the cons case is
       `readStep` riding `rfl`.  `isClimb_append_read_agree` closes
       span-level against ANY climb of the appended list
       (`isClimb_agree` + `span_map_of_span_eq`).
     * **read injectivity** (`climbRead_eq_zero` /
       `climbRead_injective`): when the stepped atoms are distinct, the
       atom-named reading loses nothing — each slot deposits at its own
       name (`climbRead_snd_eq_zero`) — so a window's read is faithful,
       and the span laws reflect back through it
       (`map_span_singleton_eq_iff`, `map_mem_span_singleton_iff`,
       `map_mem_span_pair_iff`, `mem_span_pair_congr`: the reflect
       calculus, seated ahead of its consumer).
     * the **windows**: `basis_no_capture` — an atom of the basis
       outside a window is never below its flat, and the carve came in
       LEANER than the chart: `sSupIndep` refuses the capture directly,
       no Steinitz exchange needed (the captured atom would sit under
       the sup of the others, against independence).  The base support
       `t₀` climbs greedily along its canonical enumeration (`actives`
       — keep an atom iff not yet below the flat; a sublist), the
       extras follow in any enumeration (`extras_legal`), the whole
       canonical list is legal (`window_legal` = `actives_legal` ++
       `extras_legal` through `ClimbLegal.append`), and the flat is
       exact (`windowFlat_eq : climbFlat x (windowPairs cal x t₀ s) =
       x ⊔ s.sup id`).  Calibration atoms are chosen once per stepped
       atom (`CalSpec` / `calSpec_exists`), so any two windows' lists
       carry literally equal pair data — and probe check C's
       order-stability of the active set DISSOLVED at carve time: one
       fixed canonical order per window suffices, `ClimbLegal.perm` +
       `isClimb_perm_agree` absorbing every other order.
     * the **summit**: `window_read_mono` — for `s ⊆ s'` the canonical
       list of `s'` is a permutation of the canonical list of `s`
       followed by the new extras (`windowPairs_perm`, one `disjUnion`
       multiset identity), so the perm face and the append face CHAIN —
       and `window_read_directed`: any two windows agree span-level on
       every atom both flats hold, through their union.  The directed
       family is coherent.
     **The limit map CARVED** (`Limit.lean`, sorry-free):
     `limit_read_exists` — ONE global assignment
     `hv : L → (Fin n → K) × (L → K)`, every atom read through one
     chosen window climb, `Classical.choice` serving as the
     representative per atom exactly as check F answered the seated
     question.  Its clauses: **stability** (on every window's flat,
     `hv` span-agrees with that window's climb read, whichever climb it
     is — `window_read_directed` through the chosen window), **base
     compatibility** (below `x` the assignment is literally the padded
     base vector — vector-level, no rescale: `summary_resumes` at name
     scale), and the three pointwise laws GLOBAL — `ne_zero`,
     `span_inj`, `collinear_iff` for all atoms of `L` at once: any two
     or three atoms meet inside the union window (directedness;
     `exists_finset_support` covers every atom because a point is
     finitely reachable), the window's `PointSys` laws fire there, and
     the reads reflect back through `climbRead_injective`.  `span_surj`
     is deliberately absent: at the limit it is the *spanning* half of
     the residual, owed onto the named slot space
     `(Fin n → K) × (B →₀ K)` — the next stratum's packaging, where the
     orientation re-scope (`Dᵐᵒᵖ`) is also seated.  NO new probe needed:
     checks C/D/E/F sealed every move the previous sitting.  Receipts on
     all thirty-four public declarations across the two files
     (`climbFlat_append`, `ClimbLegal.append`/`append_right`, `CalSpec`,
     `calPairs`, `calPairs_map_fst`, `listSup` even AXIOM-FREE;
     `climbFlat_calPairs` `[propext]`; `basis_no_capture` and
     `map_mem_span_singleton_iff` `[propext, Quot.sound]`; the rest
     `[propext, Classical.choice, Quot.sound]`).  Next: stage four —
     `closed` and `spanning` (`span_surj` onto
     `(Fin n → K) × (B →₀ K)`, finite support from the finite windows),
     the orientation re-scope of `pointSystem_exists` (the residual
     should hand over `Dᵐᵒᵖ`), the grounding (`x := τ`, `t₀` from the
     four frame supports via `exists_finset_support`, `h_irred` from
     the frame), and the interval iso through `Iso.lean`'s reduction.
  3. **the direct limit** — coordinates stable under extending the finite
     support (`summary_resumes` at coordinate scale: the finite record
     determines the vector, growing the window never rewrites it); glue
     into `V = B →₀ D`.  The route, charted this session (the coherence
     probe sealed each move):
     * **windows — CARVED** (`Window.lean`): finite `t₀ ⊆ s ⊆ B` with
       flats `x ⊔ s.sup id` (`windowFlat_eq`).  No-capture landed
       leaner than charted: `basis_no_capture` needs no Steinitz
       exchange — `sSupIndep` refuses the capture directly.  The
       greedy actives (`actives`, one fixed canonical enumeration of
       `t₀`) plus the extras in any enumeration are legal
       (`window_legal`), and order-stability of the active set
       dissolved: one canonical order per window suffices,
       `ClimbLegal.perm` + `isClimb_perm_agree` absorb the rest.
       Probe-sealed the previous sitting (`probe_limit.py`, check C):
       no-capture and active-set order-stability over aligned and
       tilted `τ` (support 4, 5, and 6), `q ∈ {2, 3}`, interleavings
       included.
     * **k-calibration — CARVED** (`Climb.lean`): `IsClimb b₀ ws`,
       the composite of calibrated steps with the old coordinates
       stored vector-level as zero-pads.  Window rigidity
       (`isClimb_agree`) landed by FORWARD induction, not
       strip-induction: the pads carry `b₀`'s representative
       unchanged, so the invariant is span-agreement at every atom
       plus vector-agreement at `b₀`, and each step is
       `calibrated_agree` after `calibrated_congr`.  No strips, no
       canonical representatives, no new pinning.  The strip-induction
       (last slot of an atom below the previous flat vanishes, forward
       by pencil membership, backward by contraposition through the
       new atom's trace) remains charted — it is the COHERENCE move,
       manufacturing the intermediate systems when two orders on one
       window are compared; `calibrated_last_zero_iff` is its
       single-step seed.
     * **canonical representatives** (max-nonzero-slot coefficient
       `1`): not needed for rigidity (the pads made the calibration
       target climb-invariant by construction) — and a seated question
       for the next descent: possibly not needed for the limit map
       either.  The residual consumes SPANS (the interval iso is built
       from `span (hvec '' atoms)`; every `PointSys` law is
       rescale-invariant), so one choice-conjured representative per
       atom may serve, owing only span-stability across windows —
       the same collapse the strip-induction underwent, with
       `Classical.choice` as the observer's reality-generator (the
       bridge has already paid for it).  PROBED — the seated question
       left the table answered YES (`probe_limit.py`, check F): the
       limit map built from ONE arbitrary representative per atom —
       random window containing the support, random legal order,
       random nonzero scalar — satisfies all four `PointSys` laws
       globally (`span_surj` onto the full slot space included) over
       five window configurations, `q ∈ {2, 3}`.  Canonical
       representatives are struck from the chart: choice per atom
       serves, owing only span-stability, and span-stability is
       extension-padding (`hv_of_le`) plus permutation coherence.
     * **coherence over the directed family — BOTH FACES CARVED**
       (`Perm.lean`, `Window.lean`): the order face is
       `isClimb_perm_agree` — two climbs along permuted lists agree
       span-level under the atom-named reading (`climbRead`), by
       `List.Perm` induction exactly as charted (cons: calibrated
       heads agree; swap: the diamond, carried up the tail by
       twist-functoriality; trans: capture-free legality is
       permutation-invariant — `ClimbLegal.perm`, one Steinitz
       exchange per adjacent swap).  The inclusion face is
       `isClimb_append_read_agree` + `window_read_mono`: `s ⊆ s'`
       agree inside `y_s` because `s`-first-then-rest is a legal
       order for `s'` whose climb pads `s`'s values by zeros
       (`hv_of_le` + `climbRead_pad`: the padded vector reads as pure
       base), and `window_read_directed` closes any two windows
       through their union.  End-to-end probe seal (`probe_limit.py`,
       checks D/E): every pooled climb — all windows, all sampled
       orders and interleavings — span-agrees with the limit
       assignment under the atom-named embedding.
     * **the limit map — CARVED** (`Limit.lean`):
       `limit_read_exists` — one global assignment, every atom read
       through one chosen window climb (`Classical.choice` per atom,
       as check F licensed), with stability over every window, base
       compatibility vector-level, and `ne_zero`/`span_inj`/
       `collinear_iff` global by common windows + the reflect
       calculus.  `span_surj` deferred to stage four: it is the
       *spanning* half of the residual, owed onto
       `(Fin n → K) × (B →₀ K)`.
  4. **`closed` and `spanning`** — the two `PointSystem` fields, from the
     exchange stratum plus the assignment's faithfulness.  NOTE the
     orientation re-scope waiting here: `PointSystem`/`pointSystem_exists`
     currently demand `Module (Coordinate Φ.Γ) V`, but the constructed
     systems are left modules over the OPPOSITE ring — the residual's
     statement should existentially hand over `(Coordinate Φ.Γ)ᵐᵒᵖ`
     (the final `ftpg` existential already quantifies the division
     ring, so nothing downstream moves).
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
| `Flat` | camp three, second pitch — the plane interval is the subspace lattice: `line_covBy_π` (a plane line is covered by `π`, one modular transport), `plane_flat_cases` (the height classification of `[⊥, π]`), the finrank classification of submodules of `K³` (`flat_rank_zero` … `flat_rank_three`, division-ring-general), `planeFlat` (span of the hvec-image of the atoms below `x`) evaluated at every height, `hvec_U`/`hvec_O` (the frame vectors are the standard basis), `plane_interval_iso : Set.Iic π ≃o Submodule Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)` via `Iso.lean`'s `orderIso_of_mono_reflect_surj` |
| `Space` | camp three, third pitch — the space chart, the first out-of-plane step: `line_meets_hyperplane` (a line off a hyperplane meets it in an atom — the height-4 projection lemma), the frame 3-space `τ = π ⊔ R` with infinity plane `σ = m ⊔ R` and z-axis `ζ = O ⊔ R` (position facts pure modular law), `baseproj`/`zproj`/`spoint` (two drops, one modular recovery), `spaceChart : SpaceAffine Γ R ≃ Affine Γ × Applicate Γ R`, the z-transport by one standing perspectivity (center a third atom on `U ⊔ R`, calibrations `zcoord_O`/`zcoord_R`), `solidChart` — the affine 3-space is `D³` at atom level, `CoordFrame.solidChart_exists` |
| `Shear` | camp three, fourth pitch — the sheared charts: `shproj` (the drop through an infinity center onto `π`), `ncoord` (the `e`-gauge, `ζ → n` calibrated at both ends), the x-shear `xproj_shproj_c` (z-gauge added to the abscissa, ordinate preserved), the y-shear `ycoord_shproj_e` (mirror, no ring solve), `le_zproj_sup_dir` (a space point rides its height's horizontal ray), `base_dir_facts`, `affine_solve` (the coordinate-ring solver), `gauge_bridge` (the two gauges reconcile through the slope of `(e ⊔ c) ⊓ m`) — no fresh Desargues |
| `Solid` | camp three, fifth pitch — the space's point system: `hvec4` (homogeneous coordinates in `(Dᵐᵒᵖ)⁴` through the c-gauge, `σ`-directions via the height-one witness `wpt`), `planeInj` (the plane embeds at the fourth coordinate's zero), the plane-form families (`Rplane_form`/`cplane_form`/`eplane_form`/`hplane_form` — every covered plane a form kernel, the σ-parts riding `ray_trace_form` + `dir_shproj`), the line menu (`collinear_π`/`collinear_infinity`/`collinear_vertical`/`collinear_general_center`/`collinear_horizontal` assembled by `two_form_collinear` and `collinear_of_line_eq`), the summit `space_collinear_iff`, `spacePt` + inj/le-iff/surj — no fresh Desargues |
| `SpaceFlat` | camp three, sixth pitch — the space interval is the subspace lattice: `three_atoms_ne_τ` (no three atoms span the 3-space — `planes_meet_covBy` + `line_covBy_π` refute the covering), `flat_trace_pair`/`plane_trace_line` (the `π`-trace of a 3-atom span holds two distinct atoms), `plane_covBy_τ` (the trace is a line; one modular transport lifts the covering), `space_flat_cases` (the height classification of `[⊥, τ]`), `hvec4_R` (the frame completes the standard basis of `(Dᵐᵒᵖ)⁴`), `space_coplanar_iff` (coplanarity IS span membership — the fifth pitch's summit consumed, no new incidence), the finrank classification of `K⁴` (`flat4_rank_zero` … `flat4_rank_four`), `spaceFlat` evaluated at every height, `space_interval_iso : Set.Iic τ ≃o Submodule Dᵐᵒᵖ (Fin 4 → Dᵐᵒᵖ)` via `orderIso_of_mono_reflect_surj` |
| `Ladder` | camp four, first pitch — the rank ladder's step, frame-free: `PointSys` (the induction datum), the trace/center/recovery lattice stratum (`ladder_trace_atom` … `ladder_reverse`, the shadow Θ-move), the coefficient calculus over abstract `K` (`ladder_pin`, `ladder_graph_comb`, `ladder_conv_transfer`, `ladder_avoid_two`, the snoc calculus), `stepRaw`/`StepFrame.lam`/`StepFrame.hv'`, gauges-are-heights (`step_transport`, `step_gauge_symm`, `step_cocycle`), the central lemma (`StepFrame.central`), the collinearity summit (`hv'_collinear_iff`), `hv'_span_inj`/`hv'_span_surj`, `PointSys.step` |
| `Ground` | camp four, the ladder grounded at τ — `CoordFrame.pointSysTau`: camp three's exports instantiate the induction datum literally (`hv := hvec4`; `hvec4_ne_zero`/`hvec4_span_inj`/`hvec4_span_surj`/`space_collinear_iff` are the four fields), `pointSysTau_exists` conjuring the gauge center from `h_irred` |
| `Pin` | camp four, second pitch — the calibrated step and its rigidity: `pin_meet` (the two-plane pin, no nonzeroness needed), `pin_shape`/`pin_eq`/`pin_snoc_zero_span_congr`/`pin_span_pair_congr` (the snoc-span calculus), `pin_map_*` (span transport along linear equivs), `heightEquiv` (the last-slot right-multiplication rescale), `PointSys.twist`, `Calibrated` (base/apex/unit — the span-level extension data), `calibrated_agree_main`/`calibrated_agree` (rigidity: two-plane pinning off the calibration line, routed through an auxiliary axis on it), `PointSys.calibrated_exists` (step + rescale), `calibrated_last_zero_iff` (the window sees its own coordinates) |
| `Climb` | camp four, third pitch's base — the calibrated climb: `climbFlat`/`climbDim`/`climbPad` (the climb's shape — flats, dimensions, iterated zero-pads, with `climbPad_smul`/`climbPad_ne_zero`), `ClimbLegal` (the per-step side conditions), `IsClimb` (the composite of calibrated steps, old coordinates vector-level zero-pads), `calibrated_congr` (calibration transported across span-agreement plus `b₀`-vector-agreement), `isClimb_exists`, `isClimb_agree_congr`/`isClimb_agree` (window rigidity, by forward induction — no strips, no canonical representatives), `IsClimb.hv_of_le` (growing the window never rewrites the vector: the iterated zero-pad, `[propext, Quot.sound]`), `PointSys.strip`/`strip_snoc`/`strip_hv` (a system reading its last slot restricts one flat down — the coherence pitch's tool, seated) |
| `Diamond` | camp four, the diamond — calibrated steps commute: `swapLast` (the last-two-slot exchange as a linear equiv) with `swapLast_snoc_snoc`/`snoc_comp_castSucc`/`smul_comp_castSucc`, `span_shape_of_span_eq`, `PointSys.reflat`, `calibrated_cross_last_zero_iff` (the cross-strip: membership in the first step's flat read off the second step's slot — the bridge-arm's measurement, zero exactly on balance), `calibrated_diamond` (strip + agree + congr + agree — the object-prime Diamond-with-cross-measurement made formal; the modular law enters only as the diamond iso at atom grain, `project` its perspectivity composite) |
| `Perm` | camp four, permutation coherence — the climb reads the window, not the order: `climbRead` (the atom-named reading — slots onto names, lattice-free, linear), `readStep`/`climbRead_pad`/`climbRead_twist`/`readStep_swap` (the read calculus — the pad reads as pure base, a lifted twist confines to the base component, the two deposited names commute), `padTwist`/`climbTwist` (a base equiv extended slot-fixing through the climb), `Calibrated.twist`/`IsClimb.twist`/`IsClimb.reflat` (twist-functoriality: a climb twisted is a climb), `climbFlat_perm`, `ClimbLegal.perm` (capture-free legality is permutation-invariant — Steinitz), `span_map_of_span_eq`, and the summit `isClimb_perm_agree` (`List.Perm` induction: cons = `calibrated_agree`, swap = the diamond, trans = the middle climb) |
| `Window` | camp four, the windows along the atom basis — the append face (`climbFlat_append`, `ClimbLegal.append`/`append_right`, `isClimb_append_exists` with the read unchanged on the old flat, `isClimb_append_read_agree`), read injectivity (`climbRead_snd_eq_zero`/`climbRead_eq_zero`/`climbRead_injective`) with the span-reflect calculus (`map_span_singleton_eq_iff`, `map_mem_span_singleton_iff`, `map_mem_span_pair_iff`, `mem_span_pair_congr`), the windows (`CalSpec`/`calSpec_exists`, `calPairs`, `listSup`, `actives`, `basis_no_capture` — `sSupIndep` refuses capture directly, `actives_legal`/`extras_legal`/`window_legal`, `windowFlat_eq`, `windowList_nodup`), and the summit (`windowPairs_perm`, `window_read_mono`, `window_read_directed` — the directed family is coherent) |
| `Limit` | camp four, the limit map — `limit_read_exists`: one global assignment `L → (Fin n → K) × (L → K)`, `Classical.choice` per atom, with window stability, vector-level base compatibility, and `ne_zero`/`span_inj`/`collinear_iff` global (common windows + reflect through `climbRead_injective`); `span_surj` deferred to the spanning stratum |
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
