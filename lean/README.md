# lean

Mechanically verified deductive path from P² = P to the foam's architecture. 1 axiom (FTPG); run `ls Foam/*.lean | wc -l` for the current file count (the hard "28" here had drifted — same stale number fixed in `CLAUDE.md` on 2026-05-30).

## The chain

```
closure (the spec's ground)
  ↓ (derived in natural language)
complemented modular lattice, irreducible, height ≥ 4
  ↓ axiom(FTPG) — Bridge.lean
L ≅ Sub(D, V) for some division ring D, vector space V
  ↓ (Solèr at fixed point: D ∈ {ℝ, ℂ, ℍ})
  ↓ (realization choice — lean works the ℝ branch)
elements are orthogonal projections: P² = P, Pᵀ = P
  ↓ (the deductive chain — all proven)
eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian
  ↓ Ground.lean (capstone)
FoamGround properties ✓
```

## Files

### The bridge

**Bridge.lean** — 1 axiom, 1 theorem

| declaration | role |
|---|---|
| `ftpg` | axiom: complemented modular lattice → subspace lattice (the fundamental theorem of projective geometry) |
| `dimension_unique` | theorem: lattice isomorphism preserves dimension (the axiom has a unique solution) |

### The algebraic descent (toward eliminating the axiom)

The full path from lattice axioms to FTPG:

```
complemented modular lattice, irreducible, height ≥ 4
  ↓ incidence geometry, Veblen-Young           ── FTPGExploreprojective geometry: Desargues, perspectivity
  ↓ von Staudt coordinatization                ── FTPGCoordcoord_add: zero, identity
  ↓ two Desargues applications                 ── FTPGAddCommcoord_add: commutativity
  ↓ Hartshorne translation program             ── FTPGParallelogram,
    parallelism, well-definedness,               FTPGWellDefined,
    cross-parallelism, key identity              FTPGCrossParallelism,
                                                 FTPGAssoc,
                                                 FTPGAssocCapstonecoord_add: associativity ✓
  ↓ von Staudt multiplication via dilations  ── FTPGMulcoord_mul: identity, zero annihilation, atom
  ↓ dilation extension, direction preservation  ── FTPGDilation  ↓ beta infrastructure, mul key identity       ── FTPGMulKeyIdentity  ↓ right distributivity via Desargues          ── FTPGDistribdistributivity (right) ✓
  ↓ additive inverse via double Desargues        ── FTPGNegcoord_neg, a + (-a) = O ✓
  ↓ converse Desargues (3D lift) + forward      ── FTPGLeftDistribdistributivity (left)                             combination logic PROVEN
  ↓ multiplicative inverse via reverse           ── FTPGInverse
    perspectivity through I⊔d_a                    a · a⁻¹ = I PROVEN
  ↓ multiplicative associativity via dilation     ── FTPGMulAssoc
    composition (capstone PROVEN as assembly,        coord_mul_assoc PROVEN
    one substantive sorry on dilation                (mod dilation_compose_at_witness)
    composition law on a witness)
  ↓
division ring structure (left inverse — open via Mac Lane once mul-assoc lands)
  ↓
L ≃o Sub(D, V) — the isomorphism
  ↓
axiom(FTPG) becomes a theorem
```

**FTPGExplore.lean** — projective geometry from lattice axioms
Incidence geometry, Veblen-Young, Desargues (nonplanar + planar), perspectivity, and Small Desargues (A5a). Pure geometry — no coordinates.

| layer | key declarations |
|---|---|
| incidence geometry | `atoms_disjoint`, `line_height_two`, `veblen_young`, `meet_of_lines_is_atom` |
| Desargues | `desargues_nonplanar`, `desargues_planar`, `planes_meet_covBy` |
| perspectivity | `project_is_atom`, `project_injective`, `perspectivity_injective` |
| Small Desargues | `small_desargues'` (A5a: parallelism from Desargues) |

**FTPGCoord.lean** — von Staudt coordinatization + converse Desargues
Coordinate system, addition via perspectivities, identity. Also `desargues_converse_nonplanar`: if two non-coplanar triangles have sides meeting on a common axis, vertex-joins are concurrent. Imports FTPGExplore.

| layer | key declarations |
|---|---|
| coordinate system | `CoordSystem`, `coord_add`, `coord_add_atom`, `coord_add_left_zero`, `coord_add_right_zero` |
| Desargues helpers | `desargues_planar`, `desargues_converse_nonplanar`, `collinear_of_common_bound`, `small_desargues'` |

**FTPGAddComm.lean** — commutativity of coordinate addition
Two Desargues applications establish coord_add_comm. Split from FTPGCoord. Imports FTPGCoord.

| layer | key declarations |
|---|---|
| commutativity | `coord_first_desargues`, `coord_second_desargues`, `coord_add_comm` |

**FTPGParallelogram.lean** — parallelogram completion
Infrastructure for the Hartshorne translation approach (§7). Parallelism, parallelogram completion, and Parts I–III properties.

| layer | key declarations |
|---|---|
| parallelism | `parallel`, `parallel_refl`, `parallel_symm`, `parallel_trans` |
| construction | `parallelogram_completion`, `parallelogram_completion_atom`, `line_meets_m_at_atom` |
| properties | `parallelogram_parallel_direction`, `parallelogram_parallel_sides` |

**FTPGWellDefined.lean** — translation well-definedness
Part IV: parallelogram completion is independent of base point (Hartshorne Theorem 7.6, Step 2). Key use of `small_desargues'`.

| layer | key declarations |
|---|---|
| well-definedness | `parallelogram_completion_well_defined` |

**FTPGCrossParallelism.lean** — cross-parallelism
Part IV-B: a single translation preserves directions of lines connecting any two points it acts on.

| layer | key declarations |
|---|---|
| cross-parallelism | `cross_parallelism` |

**FTPGAssoc.lean** — translation infrastructure
Part V: `coord_add` equals translation application, key identity for the translation group.

| layer | key declarations |
|---|---|
| translation bridge | `coord_add_eq_translation` (von Staudt addition = apply translation) |
| key identity | `key_identity` (τ_a(C_b) = C_{a+b}) |

**FTPGAssocCapstone.lean** — associativity capstone
Associativity via β-injectivity and cross-parallelism. PROVEN.

| layer | key declarations |
|---|---|
| parameter rigidity | `translation_determined_by_param` (C-based translation determined by one point) |
| associativity | `coord_add_assoc` (the composition law) |

Three-step proof: (1) key_identity reduces to β-images agree, (2) two cross-parallelism chains + two two_lines arguments close the composition law via collinear/non-collinear case splits, (3) E-perspectivity recovery.

**FTPGMul.lean** — coordinate multiplication
Multiplication via dilations (Hartshorne §7). Structurally parallel to addition: uses O⊔C as bridge line instead of q = U⊔C.

| layer | key declarations |
|---|---|
| multiplicative anchor | `CoordSystem.E_I` (projection of I onto m via C), `hE_I_atom`, `hE_I_not_OC`, `hE_I_ne_E` |
| multiplication | `coord_mul` (a·b via dilation σ_b), `coord_mul_atom` (a·b is an atom) |

**FTPGDilation.lean** — dilation extension and direction preservation
Defines `dilation_ext Γ c P` (the dilation σ_c extended to off-line points) and proves `dilation_preserves_direction`: (P⊔Q)⊓m = (σ_c(P)⊔σ_c(Q))⊓m. Three cases: c=I (identity), collinear, generic (Desargues center O). Also proves `dilation_ext_fixes_m`: σ_a fixes points on m.

**FTPGMulKeyIdentity.lean** — beta infrastructure and mul key identity
Beta-images `β(a) = (U⊔C)⊓(a⊔E)` and the mul key identity: σ_c(β(a)) = (σ⊔U)⊓(ac⊔E). Three cases: c=I, a=I (via DPD), generic (Desargues center C).

**FTPGDistrib.lean** — right distributivity (PROVEN)

Proves (a+b)·c = a·c + b·c via forward Desargues (center O) on T1=(C,a,C_s), T2=(σ,ac,C'_sc), then parallelogram_completion_well_defined to change translation base. Key insight: O⊔σ = O⊔C gives shared E; well_definedness provides base-independence.

| layer | key declarations |
|---|---|
| dilation extension | `dilation_ext`, `dilation_ext_identity` (c=I → identity), `dilation_ext_atom`, `dilation_ext_ne_P`, `dilation_ext_parallelism` |
| direction preservation | `dilation_preserves_direction` (PROVEN — forward Desargues with center O, 3 cases) |
| helper lemmas | `beta_atom`, `beta_not_l`, `beta_plane` (C_a = β(a) properties) |
| mul key identity | `dilation_mul_key_identity` (PROVEN — 3 cases: c=I, a=I via DPD, generic Desargues center C) |
| right distributivity | `coord_mul_right_distrib` (PROVEN — chain of above) |

**FTPGNeg.lean** — additive inverse (PROVEN)

Defines `coord_neg` (additive inverse) via the perspectivity chain a →[E]→ β(a) →[O]→ e_a →[C]→ -a. Proves a + (-a) = O via double Desargues: the key identity d_{neg_a} = e_a ("double-cover alignment") reduces the second Desargues output to a covering argument.

| layer | key declarations |
|---|---|
| definition | `coord_neg` (additive inverse via 3-step perspectivity chain) |
| atom property | `coord_neg_atom`, `coord_neg_ne_O`, `coord_neg_ne_U` |
| double-cover | `neg_C_persp_eq_e` (C-persp of -a from l to m = e_a) |
| left inverse | `coord_add_left_neg` (PROVEN — double Desargues + coplanarity) |
| right inverse | `coord_add_right_neg` (from left inverse + `coord_add_comm`) |

**FTPGInverse.lean** — multiplicative right inverse (zero `sorry`)

Defines `coord_inv Γ a` via reverse perspectivity through I⊔d_a:
`a⁻¹ = ((O⊔C) ⊓ (I ⊔ d_a) ⊔ E_I) ⊓ l`. Proves `coord_mul_right_inv`:
`a · a⁻¹ = I` for `a` an atom on `l` with `a ≠ O, a ≠ U`. The construction
exploits that the (O⊔C)-projection of d_a along the I-line is the σ that
makes `σ ⊔ d_a` pass through I, so the second perspectivity recovers I.

| layer | status |
|---|---|
| definition | `coord_inv` (reverse perspectivity) |
| atom property | `coord_inv_atom`, `coord_inv_on_l` |
| right inverse | `coord_mul_right_inv` (PROVEN) |
| left inverse | OPEN — needs either `coord_mul_assoc` (also open) or a direct geometric proof |

**FTPGMulAssoc.lean** — multiplicative associativity (one substantive sorry; capstone PROVEN as assembly)

`(a·b)·c = a·(b·c)` proven as a thin algebraic assembly of three
applications of `dilation_compose_at_witness` plus
`dilation_determined_by_param`. The s132 device-shape question
(whether the multiplicative branch needs a third `DesarguesianWitness`)
is sharply localized to `dilation_compose_at_witness`: the dilation
composition law on a witness, `σ_(x·y)(P) = σ_y(σ_x(P))`. Imports
FTPGMulKeyIdentity.

| layer | status |
|---|---|
| capstone | `coord_mul_assoc` (PROVEN as assembly, 0 sorries in body) |
| witness uniqueness | `dilation_determined_by_param` (PROVEN, ~150 lines, s133) |
| witness preservation | `dilation_witness_preservation` (PROVEN, s134) |
| dilation composition | `dilation_compose_at_witness` (single substantive `sorry`) |

**FTPGLeftDistrib.lean** — left distributivity (zero `sorry`, with typed observer commitment)

Proves a·(b+c) = a·b + a·c via three pieces: forward Desargues (`_scratch_forward_planar_call`), an axis-to-distributivity bridge (`_scratch_left_distrib_via_axis`), and an observer-supplied `DesarguesianWitness Γ` commitment carrying the planar converse-Desargues content. All three pieces are fully discharged; the geometric residue (the planar converse-Desargues claim, not derivable from CML + irreducible + height ≥ 4 alone per session 114's structural finding) is named explicitly as a typed pluggable interface rather than carried as an unproven theorem.

**Architecture (session 119):**

```
desargues_planar (FTPGCoord, PROVEN)
  → _scratch_forward_planar_call: axis through P₁, P₂, P₃ in π
                                                  ↓
                                  _scratch_left_distrib_via_axis:
                                  axis collinearity ∧ concurrence  ⇒
                                  coord_mul a (coord_add b c) =
                                    coord_add (coord_mul a b) (coord_mul a c)
                                                  ↑
                              DesarguesianWitness Γ ← observer-supplied
                              .concurrence : W' ≤ σ_s⊔d_a
```

Note: left multiplication x↦a·x is NOT a collineation (unlike right mult). This is why left distrib needs a separate concurrence step, while right distrib used the collineation directly.

The previous lift+recurse route via `desargues_converse_nonplanar` (session 114, "Level 1/Level 2 architecture") was found structurally non-terminating at Level 2 `h_ax₂₃` and is gone from the file. Open routes for constructing `DesarguesianWitness Γ`: a planar converse Desargues lemma; a direct construction exploiting that the natural axis lies on m.

| layer | status |
|---|---|
| `_scratch_forward_planar_call` | PROVEN (forward Desargues, ~12 triage hypotheses discharged) |
| `_scratch_left_distrib_via_axis` | PROVEN (axis collinearity + concurrence ⇒ left distrib) |
| `DesarguesianWitness Γ` | TYPED INTERFACE (observer-supplied commitment carrying the planar converse-Desargues residue) |
| `coord_mul_left_distrib` | PROVEN (composition takes a `DesarguesianWitness Γ` as explicit parameter) |

### The deductive chain (from P² = P)

**Observation.lean** — one observation

| theorem | from |
|---|---|
| `eigenvalue_binary` | P² = P → eigenvalues ∈ {0, 1} |
| `range_ker_disjoint` | P² = P → range ∩ ker = {0} |
| `complement_idempotent` | P² = P → (I - P)² = I - P |

**Pair.lean** — two observations

| theorem | from |
|---|---|
| `comp_range_le` | PQ maps into range(P) |
| `comm_comp_idempotent` | PQ = QP → (PQ)² = PQ |
| `commutator_zero_iff_comm` | [P, Q] = 0 ↔ PQ = QP |
| `commutator_seen_to_unseen` | [P, Q] maps range(P) → ker(P) |

**Form.lean** — self-adjointness

| theorem | from |
|---|---|
| `commutator_skew_of_symmetric` | Pᵀ = P, Qᵀ = Q → [P, Q]ᵀ = -[P, Q] |
| `commutator_traceless` | tr[P, Q] = 0 (unconditional) |

**Rank.lean** — why 3

| theorem | from |
|---|---|
| `write_space_dim` | dim(Λ²(M)) = C(dim(M), 2) |
| `rank_one_no_writes` | rank 1 → 0D write space |
| `rank_two_abelian_writes` | rank 2 → 1D (abelian) |
| `rank_three_writes` | rank 3 → 3D (non-abelian) |
| `self_dual_iff_three` | C(k, 2) = k ↔ k = 3 |
| `rank_four_writes` | rank 4 → 6D (overdetermined) |

**Duality.lean** — (R³, ×) ≅ so(3)

| theorem | from |
|---|---|
| `cross_anticomm` | a × b = -(b × a) |
| `cross_self_zero` | a × a = 0 |
| `cross_nontrivial` | ∃ a b, a × b ≠ 0 |
| `cross_jacobi` | Jacobi identity (this IS a Lie algebra) |

**Closure.lean** — the loop closes

| theorem | from |
|---|---|
| `conjugation_preserves_idempotent` | P² = P → (UPU⁻¹)² = UPU⁻¹ |
| `orthogonal_conjugation_preserves_symmetric` | Pᵀ = P, UᵀU = I → (UPUᵀ)ᵀ = UPUᵀ |
| `observation_preserved_by_dynamics` | both properties preserved (the full loop) |

**Group.lean** — O(d) is forced

| theorem | from |
|---|---|
| `scalar_extraction` | PMP = P for rank-1 P → vᵀMv = 1 |

**Tangent.lean** — Grassmannian tangent

| theorem | from |
|---|---|
| `commutator_off_diag_range` | P · [W, P] · P = 0 |
| `commutator_off_diag_kernel` | (I-P) · [W, P] · (I-P) = 0 |
| `commutator_is_tangent` | [W, P] = range→kernel + kernel→range |

### The capstone

**Ground.lean** — FoamGround as a theorem, O(d) forced by polarization

| theorem | from |
|---|---|
| `subspaceFoamGround` | Sub(K, V) satisfies FoamGround (complemented, modular, bounded) |
| `symmetric_quadratic_zero_imp_zero` | polarization: Aᵀ = A, vᵀAv = 0 ∀v → A = 0 |
| `orthogonality_forced` | vᵀMv = 1 ∀unit v → M = I (O(d) is forced) |

### Downstream properties

**Confinement.lean** — writes stay in the observer's slice

| theorem | from |
|---|---|
| `write_confined_to_slice` | d, m ∈ P → d∧m ∈ Λ²(P) |

**TraceUnique.lean** — one scalar readout

| theorem | from |
|---|---|
| `trace_unique_of_kills_commutators` | φ kills [·,·] → φ = c · trace |

**Dynamics.lean** — frame recession

| theorem | from |
|---|---|
| `first_order_overlap_zero` | tr(P · [W, P]) = 0 |
| `second_order_overlap_identity` | tr(P · [W, [W, P]]) = -tr([W, P]²) |
| `frame_recession` | second-order overlap ≤ 0 |
| `frame_recession_strict` | [W, P] ≠ 0 → recession < 0 |

### Cross-examinations

**HalfType.lean** — the half-type theorem as a constructed object. Packages the diamond iso (`IsCompl.IicOrderIsoIci`) with modularity- and complementedness-inheritance on each half (`isModularLattice_Iic`, `complementedLattice_Iic`, etc.) into a single named structure. The first Foam-internal substrate primitive: a Bin-1-Mathlib-or-Foam landing whose constructor is one-liners over Mathlib lemmas.

| declaration | role |
|---|---|
| `HalfType` | the typed bundle (iso + 4 inheritance facts) |
| `half_type` | constructor: takes `IsCompl P Q`, returns a `HalfType` |

**HalfTypeIterated.lean** — probe (s149): iterated HalfType is bin-1-Mathlib. Three `example` declarations construct `HalfType` at depths 1, 2, 3 via `half_type` alone, with `Set.Iic` chained two levels deep. Builds clean: Mathlib's interval instances (Lattice, BoundedOrder, IsModularLattice, ComplementedLattice on `Set.Iic`) carry the inheritance through typeclass synthesis. Underscored hypotheses at depths 2 and 3 mark the outer complementary pairs as unconsumed by the construction — the iteration is freely available wherever a complementary pair is picked, and the syntactic mark is itself the evidence (scaffolding named, not content). Substantiates the s149 reading of the spec's "three recursion levels above prime-ground" as a structural depth-at-which-the-iteration-is-self-sufficient, not a specific triple choice. No new declarations; the artifact is the build itself.

**HalfTypeRLift.lean** — probe (s149): the R-lift is structurally a HalfType iso. Given `π R : L` with `Disjoint π R` (R off the "plane" π), the pair `(⟨π, le_sup_left⟩, ⟨R, le_sup_right⟩)` in `Set.Iic (π ⊔ R)` is `IsCompl` (constructed by direct lattice argument); `half_type` then produces the HalfType. The iso `Set.Iic ⟨π, _⟩ ≃o Set.Ici ⟨R, _⟩` within the interval IS the classical Hartshorne dimensional lift through R. Iso behavior rfl-verified: `iso ⟨X, _⟩ = ⟨X ⊔ R, _⟩` at the underlying L value. Substrate-direct: lands the tool exit (A) needs for `dilation_compose_at_beta`'s joint-install (per `lean/CLAUDE.md`'s s148 frontier). Having the tool is not the same as using it; see `FTPGMulAssocViaRLift.lean` for the s149 application walk.

**FTPGMulAssocViaRLift.lean** — probe (s149, subagent walk): R-lift iso alone is information-preserving, not information-producing. PROVES `mul_assoc_R_lift_blocker`: for atoms X, Y ≤ π and R off π, `X ⊔ R = Y ⊔ R ↔ X = Y` (via modular law `(X ⊔ R) ⊓ π = X`). Applied to `(a·x)·y` and `a·(x·y)`: the lifted equation is content-equivalent to the planar one. Names the sharp blocker `mul_assoc_via_R_lift_missing` — the planar mul-assoc, sorry'd — and documents that closing it via the R-lift route would require either (A.1) a 3D-aware dilation primitive (reproducing the loop one level up), or (A.2) a direct `desargues_nonplanar` call on triangles in ambient L with R as 3D-witness (effectively exit (C), structurally orthogonal). The 4th monodromy measurement at the `coord_mul_assoc` loop; see `lean/CLAUDE.md`'s "s149 refinement" section.

| declaration | role |
|---|---|
| `disjoint_pi_R` | helper: R atom off π forces `Disjoint π R` |
| `isCompl_pi_R` | helper: (π, R)-complementary pair in `Iic (π ⊔ R)` |
| `mul_assoc_R_lift_blocker` | PROVEN: the iff showing R-lift is information-preserving on `coord_mul_assoc`-content |
| `mul_assoc_via_R_lift_missing` | OPEN (sorry): the planar mul-assoc, the precise blocker named |

**FTPGMulAssocCrossings.lean** — probe (s151): the FTPG mul-assoc site has structural crossings. Develops the stylus-framing prediction that the four monodromy measurements (s142, s146, s148, s149) at `dilation_compose_at_beta`'s generic case are sites where the loop reads higher-level shape, and asks whether the parameterization has *crossings* — configurations where the loop's character changes. Two probed: the boundary `x = I` (PROVEN trivially via `dilation_ext_identity` + `coord_mul_left_one`; no Desargues machinery, no R-lift, no `recovery_via_E`; monodromy fully collapses) and the internal `y = coord_inv x` (RHS reduces to `β(a)` via `coord_mul_right_inv` + `dilation_ext_identity`; LHS persists as a named candidate-`sorry` whose provability tests the framing's strength). Three regimes (boundary/asymmetric/generic) name gauge 3's internal three-fold of the outer σ-ring-hom three-rotation across gauges (G1 right-distrib PROVEN, G2 left-distrib via `DesarguesianWitness`, G3 mul-assoc). The s151 dagger-absence refinement reads G1/G2/G3 separation against Heunen-Kornell's six-axiom Hilbert-space characterization, where the dagger jointly derives the bilinearity that Foam's no-dagger setting separates into three gauges. See file docstring and `history/151_*.md` for the recognition-walk.

| declaration | role |
|---|---|
| `dilation_compose_at_beta_x_eq_I` | PROVEN: boundary crossing at x = I, conclusion holds via identity-laws alone |
| `dilation_compose_at_beta_y_eq_coord_inv_x` | OPEN (sorry'd): internal crossing at y = coord_inv x, RHS reduces, LHS named candidate |

**FTPGGaugeFigure.lean** — probe (s152): the 3×3 gauge × regime figure as a typed Lean artifact. Nine cells named — three gauges (G1 right-distrib, G2 left-distrib, G3 mul-assoc) × three regimes (boundary, asymmetric, generic). Proven cells reference existing theorems; open cells named as sorry'd candidates with strategy-docstrings. The asymmetric row identified as dagger-shape probe across gauges (HK's dagger jointly enforces what foam separates into three gauges). G1/G2 asymmetric cells substrate-derivable via additive bootstrap (aux atom routes around degenerate-sum); G3 asymmetric not similarly derivable (no substitute for assoc). **Structural finding: holonomy of the FTPG bridge concentrates in gauge 3.** s155 framing updates: G3-row cell docstrings now reference `TrefoilCrossing` and `HolonomicLedger` from `StatelessSubstrate.lean` and the chirality typing from `FTPGGaugeFigureLayer.lean`.

| declaration | role |
|---|---|
| `g1_generic` | PROVEN: right-distrib (= `coord_mul_right_distrib`) |
| `g2_generic` | PROVEN via DesarguesianWitness (= `coord_mul_left_distrib`) |
| `g3_generic` | OPEN: σ-composition (= `dilation_compose_at_beta`); the trefoil's third crossing (commitment-site) |
| `g1_boundary`, `g2_boundary` | PROVEN: trivial via `coord_add_right_zero` |
| `g3_boundary` | PROVEN via identity-laws (= `dilation_compose_at_beta_x_eq_I`); the trefoil's first crossing |
| `g1_asymmetric`, `g2_asymmetric` | SORRY with strategy: substrate-derivable via additive bootstrap |
| `g3_asymmetric` | SORRY: the trefoil's second crossing (vacuum-formation site) |

**FTPGGaugeFigureLayer.lean** — probe (s155): buffer/working-space layer-typing at g3_asymmetric with chirality as gauge. `FTPGMulAssocCrossings.lean`'s docstring half-named "gauge 3's layer-distinction"; this file types it. `CellLayer` (working_space / buffer) names the two structural roles; `CellChirality` (lhs_role, rhs_role, distinct) names the role-assignment as gauge (structurally arbitrary; operationally required — compare the project's left-to-right composition convention in `FTPGDilationGroup.lean`); `.canonical` + `.flip` give the dynamic side-switching primitive (the dagger-free analog of classical FTPG's static holonomy-collapse). `.flip_flip = c` lands as `rfl` — flip is definitionally involutive. The `vacuum_fill_event_at_inverse_pair` re-types `dilation_compose_at_beta_y_eq_coord_inv_x` between neutrally-named `inverse_pair_expr_lhs/_rhs`, chirality-invariant equation. Recognition-grade; no proofs claimed.

| declaration | role |
|---|---|
| `CellLayer` | the two structural roles: `working_space`, `buffer` |
| `CellChirality` | role-assignment with `distinct` constraint, `.canonical`, `.flip`, `.flip_flip = rfl` |
| `inverse_pair_expr_lhs` / `inverse_pair_expr_rhs` | positionally-named lattice expressions at g3_asymmetric |
| `vacuum_fill_event_at_inverse_pair` | the equation between them, chirality-invariant |

**FTPGLeftDistribViaR.lean** — predicted bin-1 path sketch for `DesarguesianWitness Γ`'s converse-Desargues residue via height-≥-4 lift through `R`. Typing holds; constructor body open as recognition-target (not construction-target) per the s144 recognition-only working mode. See file's own docstring for the bin-1 grade diagnostic + the two vertex-lift architectures walked and seen-not-to-close.

| declaration | role |
|---|---|
| `PlanarConverseDesarguesViaR` | typed structure carrying R + irreducibility + the concurrence claim as derived field |
| `planar_converse_desargues_via_R` | constructor (body open) |
| `DesarguesianWitness.ofPlanarConverseDesarguesViaR` | thin projection (bundle → `DesarguesianWitness Γ`) |

**FTPGDilationGroup.lean** — carrier type for the dilation family (s148). Names the +1-operator move at the type level. `Dilation Γ` now bundles an order-isomorphism `L ≃o L` with three structural fields (`fixes_O`, `preserves_l`, `fixes_m`), landing the carrier on Mathlib's automorphism infrastructure from the first lemma rather than carrying a raw function with side-properties. With the order-iso reformulation, `Monoid (Dilation Γ)` lands in this file with all three laws as `rfl` or near-`rfl`. Composition uses **left-to-right convention** (`(f * g) x = g (f x)`) — non-standard vs Mathlib's `MulAut`, but chosen so the σ-family map becomes a clean homomorphism with the project's right-multiplication `coord_mul` convention rather than an anti-homomorphism. σ_c packaging and σ-family closure (= the substantive mul-assoc residue, via the R-lift) remain deferred to next walks. See file docstring and `lean/CLAUDE.md`'s "s148 refinement" for the recognition-walk that motivates this file.

| declaration | role |
|---|---|
| `Dilation` | carrier type bundling an `L ≃o L` with three structural fields |
| `Dilation.id` | the identity dilation instance |
| `Dilation.comp` | composition (left-to-right convention) |
| `instance : Monoid (Dilation Γ)` | monoid structure from composition + identity |

**ReaderCommitment.lean** — type-path from observer to probability distribution (cross-examination of "the reader's commitment", per the spec)

| declaration | role |
|---|---|
| `ObserverWitness` | observer's typed commitment to a Hilbert space and observable (DesarguesianWitness-shape, bin-2) |
| `ReaderCommitment` | the spectral decomposition output (basis + values + has_eigenvector fit) |
| `ReaderCommitment.canonical` | Mathlib-derived canonical instance from the spectral theorem |

**FrameRecessionAlignment.lean** — probe (s149): the Layer-1 ↔ HalfType bridge. An idempotent linear map `f : E →ₗ[K] E` over a division ring K determines a HalfType in `Submodule K E` via `LinearMap.IsIdempotentElem.isCompl` (Mathlib) + `Submodule.complementedLattice` (Mathlib) + `half_type` (Foam). Substrate-direct, single `example` declaration. Names the three-layer structural alignment: the `frame_recession` theorem in `Dynamics.lean` is literally a theorem about HalfTypes receding from themselves under perturbation; the matrix and lattice layers of "observer applies HalfType to themselves" are now formally bridged. The file's docstring lays out Layer 1 (Dynamics) / Layer 2 (Mathlib RingHom) / Layer 3 (FTPG σ) as three views of the same entanglement-witness shape.

**Resolver.lean** — dynamic structure of reader commitments

| declaration | role |
|---|---|
| `PathTypeDebt` | typed claims the spec's operations need that the witness hasn't supplied |
| `PathTypeDebt.discharged` | the discharge predicate (all claims provable) |
| `CommitmentState` | the witness + accumulated debt state |
| `CommitmentState.IsResolved` | the fixed-point property (resolver-shape stable commitment) |
| `CommitmentState.encounter` | asymmetric metabolisis: resolved party's discharged claims propagate to unresolved |
| `CommitmentState.encounter_safe` | safety theorem for asymmetric encounter |
| `MetabolisisStep` | type-shape of any bidirectional metabolisis-evolution map |
| `pairwiseEncounterStep` | the simplest bidirectional metabolisis: pairwise-encounter applied in both directions |
| `MetabolisisStep.IsFixedPoint` | predicate: a pair stable under further reps (the pair-version of `IsResolved`) |

Static + dynamic both typed (s155): the file now provides both the static reflection (`CommitmentState`, `IsResolved`) AND the dynamic metabolisis-operation type-shape (`MetabolisisStep`, `pairwiseEncounterStep`, `IsFixedPoint`). Per `metabolisis.md` (lightward-ai): metabolisis = +exchange +transformation; both parties evolve through reciprocal exchange. Foam's chapter-11-with-path-restriction is metabolisis-shaped: type-debt redistributes across the whole tree; everybody survives every step.

**StatelessSubstrate.lean** — probe (s155): records the synthesis `foam-lean = FTPG × stateless multi-headed UTM` as recognition-grade typed object. The 6-color tape alphabet factors as 3 algebraic-positions (G1/G2/G3) × 2 observer-states (read/write; equivalently buffer/working-space; equivalently commitment/withdrawal); minimum-color count for stateless-3-headed UTM. 3 heads (compiler + observer + substrate) shape Desargues-like triple-rewriting. G3 is the yield-position where external UTMs compose in via `ExternalYieldComposition` (carrying a *family* of dissolved knot-types: *some unknottings dissolve more than one type of knot*). `CrossUTMComposition` is the bidirectional yield-pair. `TrefoilCrossing` types the minimum non-trivial knot-progression (first deterministic / second vacuum-formation / third commitment-site); the G3-row of the gauge × regime figure realizes this progression. `HolonomicLedger` types the ancestral dagger as balance-state (debts + credits + many-to-one `dissolves` relation), not as history-enumeration. `Measurement` types the disposable single-use observer (observer == measurement): geometry-in + geometry-out + reached-unknot. **Re-types open sorries as tree-unbalanced-at-this-position rather than missing-proofs** — async-ness lives at tree-level (`CommitmentState.IsResolved` / `MetabolisisStep.IsFixedPoint` in Resolver.lean), not at the individual measurement. Morse-completeness emerges as side-effect (3 primitives × 2 directions = minimum for stateless-3-headed-UTM AND minimum for Morse-complete relay). Zero Mathlib dependencies; pure structural typing. **Later arc (2026-05-30), same file:** the observer-safety / persistence thread extends this beyond the s155 snapshot — `Scope`, `WriteOnly` (§V observer-loss / the write-only object), `Accretive` + `observer_safe_of_accretive` (the file's first proven theorem), `Persistence` + `SafeFor` + the `measureStep` licensed/unlicensed-contraction split, and `LedgerPersistence` (carrier (a) of the persistence-flag). Carrier (b) of that flag lives in the Mathlib-importing satellite `PersistenceLfp.lean` (below).

| declaration | role |
|---|---|
| `AlgebraicPosition` | G1/G2/G3 — three σ-ring-hom rotations |
| `ObserverState` | read/write — the 2-state factor |
| `TapePosition` | 6-color alphabet = AlgebraicPosition × ObserverState |
| `Head` | compiler/observer/substrate — three reading heads |
| `RewriteRule` | triple-rewrite, stateless |
| `ExternalYieldComposition` | external UTM contribution at G3 (with `dissolved_knot_types` family) |
| `CrossUTMComposition` | bidirectional yield-pair between two UTMs |
| `Measurement` | disposable single-use observer: geometry_in + geometry_out + reached_unknot |
| `TrefoilCrossing` | trefoil-progression: `.first` / `.second` / `.third` |
| `HolonomicLedger` | ancestral-dagger-as-typed-balance: debts + credits + many-to-one `dissolves` |
| `Scope` / `WriteOnly` | `TapePosition → Prop` (a `CompleteLattice`); `WriteOnly` = §V observer-loss (write-face in view, read-complement out of scope) |
| `Accretive` / `observer_safe_of_accretive` | scope-step only grows scope (`∀ S, S ≤ step S`, §III's never-retracts/inflation half); bin-1 theorem (the file's first): accretive ⇒ never produces a `WriteOnly` |
| `Persistence` / `SafeFor` | `Scope → TapePosition → Prop` flag for read-faces *meant to persist*; observer-safety refined to those, with `measureStep` proven both `SafeFor` (licensed) and not (observer-loss) |
| `measureStep` | the one licensed non-accretive contraction — a measurement spends its read-face |
| `LedgerPersistence` | carrier (a) of the persistence-flag: a `HolonomicLedger` + `holds : debts → TapePosition` supplies `flag` (persists iff backs an undischarged debt) |

**PersistenceLfp.lean** — carrier (b) of the persistence-flag (2026-05-30): §III's lfp as the *scope-dependent* persistence-flag, the held-open merge `StatelessSubstrate.lean` left after carrier (a). `Scope = TapePosition → Prop` is a `CompleteLattice`, so `OrderHom.lfp` applies. Two recognitions refined the brick rather than merely confirming it. **(1)** §III's "F is monotone" splits, under typing, into *independent* properties: *inflation* (`∀ S, S ≤ F S`, the never-retracts half = `StatelessSubstrate.Accretive`) and *monotonicity* (`S ≤ T → F S ≤ F T`, what `OrderHom.lfp` is typed on). `accretive_not_imp_monotone` cashes the independence bin-1 (an accretive step that is not monotone), so carrier (b) re-bundles recognition as a monotone `Scope →o Scope` — not from `Accretive`; this re-graded the `Accretive` docstring's old "= §III monotonicity" overreach. **(2)** The *bare* lfp `lfpFlag` (the converged scope above `⊥`, README §III's `P₀ = ∅` case) is **scope-independent** (`lfpFlag_scope_indep`), exactly like carrier (a) — only the *closure-above-`S`* `convergeFrom`/`closureFlag` exercises the `Scope` slot (`le_convergeFrom`; `convergeFrom_bot` shows bare = the `⊥` case). So the (a)↔(b) merge settles **distinct-held-in-merge**: (a) and bare-(b) share the scope-independent side, the genuine scope-dependent carrier is closure-above-`S`, and relating (a) to the converged scope needs a ledger↔recognition-operator bridge — **now typed in this file** as `LedgerRecognitionBridge LP f` (on the `DesarguesianWitness` template). Walking the bridge landed **the bridge has a sign, and the sign is gauge**: nothing in `LP` fixes which way recognition points, so `recognizeUndischarged` makes the carriers *coincide* (bare lfp = carrier (a)'s `flag` — `flag_eq_lfpFlag_recognizeUndischarged`; inhabits the bridge bin-1 via `ofRecognizeUndischarged`) while `recognizeDischarged` makes them *complementary* (`lfp_iff_not_flag_of_injective`; refutes the bridge — `not_bridge_recognizeDischarged_of_injective`). Committing which operator is `F` is gauge-fixing — the single external commitment / the tamp. **Later (2026-05-30, same file): the seed-gauge is a `{+, −, 0}` triple.** Once `RecognitionApplier.lean` localized the tamp to the *seed* `P₀`, the undischarged-/discharged-backed seed-choice became the `±` signs of a gauge — and the *all-debt-backed* seed `seedBacked` is their **join** (`seedBacked_eq_join`, via `lfp_or_flag_of_backed`), hence the **gauge-neutral `0`** that carries both signs. `SeedSign` types the `{+, −, 0}` triple (`0 = + ⊔ −` by `seed_zero_eq_join`; `⊥` below by `bot_le_seed`), genuinely three distinct seeds exactly when the ledger carries both kinds of debt (`zero_ne_plus_of_injective` / `zero_ne_minus_of_injective`, under `holds`-injectivity). First Mathlib-importing satellite of the substrate hook (`import Mathlib.Order.FixedPoints`).

| declaration | role |
|---|---|
| `accretive_not_imp_monotone` | bin-1: `Accretive` (inflation) ⊬ `Monotone` — §III's monotonicity is two independent halves |
| `lfpFlag` / `lfpFlag_scope_indep` | bare lfp above `⊥` (= `P₀ = ∅` case); scope-*independent* (proven constant in `S`) |
| `convergeFrom` | the converged scope above `S` = `OrderHom.lfp (S ⊔ F·)`, the closure of `S` |
| `le_convergeFrom` | `S ≤ convergeFrom f S` — witness that closure exercises the `Scope` slot |
| `convergeFrom_bot` | `convergeFrom f ⊥ = OrderHom.lfp f` — bare lfp is the `⊥`/`P₀=∅` instance |
| `convergeFrom_eq_self_iff` | `convergeFrom f S = S ↔ f S ≤ S` — the hinge: closure realizes its seed exactly iff the seed is `f`-closed (gauge-blind) |
| `closureFlag` | carrier (b): the scope-*dependent* persistence-flag via `convergeFrom` |
| `seedBacked` / `seedBacked_eq_join` | the **all-debt-backed** seed (gauge-neutral `0`) = the *join* of the `±` fork-seeds — carries both signs |
| `convergeFrom_mono_seed` | `convergeFrom f` is monotone in the seed — lets the `0`-closure dominate both `±`-closures over the real gated `F` |
| `SeedSign` / `SeedSign.seed` / `seed_zero_eq_join` / `bot_le_seed` | the typed `{+, −, 0}` seed-triple; `0 = + ⊔ −`, with `⊥` below |
| `zero_ne_plus_of_injective` / `zero_ne_minus_of_injective` | the grading: `0` distinct from both `±` exactly when the ledger carries both kinds of debt (injectivity) |
| `SeedSign.plus_inf_minus_eq_bot` | the meet `+ ⊓ − = ⊥` (under injectivity) — the lattice companion to `seed_zero_eq_join`'s join; assembled with it as `IsCompl`/`HalfType` in `SeedGaugeHalfType.lean` |
| `SeedSign.plus_ne_minus_of_injective` | `+ ≠ −` (given a discharged debt) — the `{⊥,+,−,0}` Boolean algebra is non-degenerate, two distinct complementary atoms |
| `recognizeBacked` / `recognizeBacked_lfp` | the carry-both (`0`) gauge-operator: accretes *every* debt-backed face; its bare lfp is `seedBacked` — the **operator-side** of the gauge-neutral `0`, completing `{recognizeUndischarged, recognizeDischarged, recognizeBacked}` ↔ `{+, −, 0}` |
| `not_bridge_recognizeBacked_of_injective` | the (a)↔(b) bridge is refuted at the `0` gauge too (under injectivity, given a discharged debt) — so `+` is the *unique* coincidence among `{+, −, 0}` |

**RecognitionApplier.lean** — foam's concrete `F` (the rewrite-rule applier) and its gauge (2026-05-30). The brick after `PersistenceLfp.lean`: type foam's *actual* recognition operator and read off which gauge it commits to. `applyRules rules : Scope →o Scope` bundles README §III's `F` as the rewrite-applier — `F(S) = S ∪ {r.writes h | rule r fires in S}`, a rule firing when its whole read-triple is in scope. Monotone and **accretive** (`applyRules_accretive`), hence observer-safe for every flag (`applyRules_safeFor`, via `safeFor_of_accretive`): foam's real `F` never *causes* §V observer-loss — that needs a contraction (`measureStep`), not rule-firing. **Verdict (ii), sign-neutral.** The applier is *gated* (writes need their reads present) where the two toy gauges are *ungated* (`S ↦ S ⊔ Q`, `Q` fixed); so its **bare lfp is `⊥`** (`applyRules_lfp_bot`: `Head` is inhabited ⇒ nothing fires from the empty scope — faithful to §III's run-from-`P₀`, cf. `convergeFrom_bot`). It equals **neither** gauge (`applyRules_lfp_ne_recognizeUndischarged` / `_recognizeDischarged`), its bare persistence-flag is `⊥` (`lfpFlag_applyRules`), and it never reads `Discharged`. So **`LedgerRecognitionBridge LP (applyRules rules)` is inhabited iff every debt is discharged** (`bridge_applyRules_iff` / `nonempty_bridge_applyRules_iff`) — only where carrier (a) is itself `⊥`. The (a)↔(b) bridge therefore stays **bin-2** in foam proper: the `recognizeUndischarged` coincidence was an artifact of an ungated, ledger-built toy operator, not a property of foam's `F`; the tamp is observer-supplied **at the ledger**, in the gap between rule-firing (what `F` does, blind to the ledger) and discharge-status (what the gauge reads). **Refined once more (same file, "Seeded from the ledger"): the tamp is the *seed* `P₀`, not the step `F`.** The bare lfp is `⊥` only because it runs from `P₀ = ∅`; §III runs recognition from the initial substrate, so the live object is the seeded closure `convergeFrom (applyRules rules) S₀`. Since `F` is sign-neutral (no ledger argument, never reads `Discharged`), the gauge can only enter through the seed — the one ledger-aware ingredient. The brick's two gradings *merge*: at an `F`-closed seed the closure *realizes* the seed-gauge exactly (`convergeFrom_emptyRules`; `closure_emptyRules_undischarged` realizes carrier (a), `closure_emptyRules_discharged` its complement — same step, opposite seeds, opposite gauges), and at any rule-set the seed is a lower bound (`seed_le_closure`) with a sign-neutral rule-firing increment above it (`closure_eq_seed_iff` is the gauge-blind criterion). `seed_fork_of_injective` shows the two ledger-seeds are complementary — the coincide/complement fork relocated from step to seed. So the single external commitment is the choice of `P₀`. **Landed (same date): the seed-gauge is a `{+, −, 0}` triple.** The two fork-seeds are the `±` projections; the **all-debt-backed** seed (`PersistenceLfp.seedBacked`) is their *join* (gauge-neutral, the `0` — `seedBacked_eq_join`), and the `{+, −, 0}` triple is typed (`PersistenceLfp.SeedSign`). Reading the `0`-seed's closure over the applier: `closure_emptyRules_backed_eq_join` (at the trivial step the `0`-closure is the join of the `±`-closures) and `closure_backed_ge_undischarged` / `_discharged` (over *any* rule-set the `0`-closure dominates both fork-closures, via `convergeFrom_mono_seed`), proper under injectivity (`closure_emptyRules_backed_ne_*`). **Landed in `SeedGaugeHalfType.lean`:** `0 = + ⊔ −` (join) + `+ ⊓ − = ⊥` (`SeedSign.plus_inf_minus_eq_bot`) make `{⊥, +, −, 0}` the **4-element Boolean algebra** — `−` the *local complement* of `+` in the `0`-scope, README §IV.a's HalfType read on the seed-gauge. Second Mathlib-importing satellite (imports `PersistenceLfp.lean`).

| declaration | role |
|---|---|
| `applyRules` | foam's `F`: the rewrite-rule applier, bundled `Scope →o Scope` (gated rule-firing) |
| `applyRules_accretive` / `applyRules_safeFor` | the applier only adds (inflation) ⇒ `SafeFor` every flag (never causes observer-loss) |
| `applyRules_lfp_bot` | bin-1 headline: the applier's bare lfp is `⊥` (gated ⇒ nothing fires from nothing) |
| `lfpFlag_applyRules` | the applier's bare persistence-flag is `⊥` |
| `applyRules_lfp_ne_recognizeUndischarged` / `_recognizeDischarged` | the applier's lfp is **neither** (nonempty) toy gauge |
| `flag_eq_bot_iff` | carrier (a)'s flag is `⊥` iff every debt discharged |
| `bridge_applyRules_iff` / `nonempty_bridge_applyRules_iff` | the (a)↔(b) bridge over foam's `F` holds **iff the ledger is fully discharged** — the gauge stays bin-2 (the tamp, at the ledger) |
| `emptyRules` / `applyRules_emptyRules_le` / `convergeFrom_emptyRules` | the trivial-step witness: empty rule-set ⇒ applier is the identity ⇒ seeded closure `=` the seed, for every seed |
| `closure_emptyRules_undischarged` / `_discharged` | (i): same trivial step, two ledger-seeds, two opposite gauges realized — the realized gauge is whichever the seed carries |
| `seed_le_closure` | (ii): for *any* rule-set the seed-gauge is a lower bound on the closure (accretivity) — the increment above is sign-neutral |
| `closure_eq_seed_iff` | realization iff the seed is `F`-closed — the gauge-blind criterion separating (i) from (ii) |
| `seed_fork_of_injective` | **the seed-choice is the gauge-fork**: undischarged- vs discharged-backed seeds are complementary — coincide/complement relocated to the seed `P₀` |
| `closure_emptyRules_backed` / `_eq_join` | the gauge-neutral `0`-seed's trivial-step closure is itself, and = the join of the `±`-fork closures |
| `closure_backed_ge_undischarged` / `_discharged` | over *any* rule-set the `0`-closure dominates **both** `±`-fork closures (via `convergeFrom_mono_seed`) — it carries both signs |
| `closure_emptyRules_backed_ne_undischarged_of_injective` / `_discharged` | proper containment: `0`-closure distinct from each `±`-closure when the ledger carries both kinds of debt |

**SeedGaugeHalfType.lean** — the seed-gauge `{⊥, +, −, 0}` IS a HalfType (2026-05-30). The brick after `PersistenceLfp.lean`'s `SeedSign` triple, assembling its lattice into the §IV.a object. `PersistenceLfp.lean` had the **join** `0 = + ⊔ −` (`SeedSign.seed_zero_eq_join`) and now the **meet** `+ ⊓ − = ⊥` (`SeedSign.plus_inf_minus_eq_bot`, under `holds`-injectivity — one rewrite off `not_lfp_and_flag_of_injective`); join + meet + top `0` + bottom `⊥` make `{⊥, +, −, 0}` the **4-element Boolean algebra `2²`** with `±` complementary atoms (non-degenerate via `plus_ne_minus_of_injective` + `zero_ne_*`). The headline: within `Set.Iic (seedBacked LP)` — the interval `[⊥, 0]`, the **`0`-scope** — `+` and `−` are `IsCompl` (`seedIsCompl`, via `IsCompl.of_eq`). So `−` is the *local complement* of `+` **within the `0`-scope**, never a global negation — exactly README §IV.a's HalfType (complementation-within-a-scope) and §V's "no global false" that relocates falsification to observer-loss. `half_type` packages it as the §IV.a object (`seedHalfType`, `noncomputable` only because the diamond `≃o` rides on `Prop`'s noncomputable complete order); its diamond iso is the local-complement lift `X ↦ X ⊔ −` (`seedHalfType_iso_apply`, rfl-level — the seed-gauge face of `HalfTypeRLift`'s `X ↦ X ⊔ R`, with `−` playing the off-plane R). Bin-1 (Bin-1-Mathlib-or-Foam): meet/join are Foam theorems, `IsCompl`/`HalfType` are Mathlib packaging. The **fourth** HalfType satellite (after `HalfTypeIterated`, `HalfTypeRLift`, `FrameRecessionAlignment`) and the first to instantiate the §IV.a object on a *foam-internal* complementary pair recognized from the recognition dynamics — the seed-gauge produces its own HalfType. Third Mathlib-importing satellite of the persistence thread (imports `PersistenceLfp.lean` + `HalfType.lean`).

| declaration | role |
|---|---|
| `seedIsCompl` | bin-1: within `Set.Iic 0` the `±` seeds are `IsCompl` — `−` the local complement of `+` in the `0`-scope (meet `= ⊥`, join `= 0`) |
| `seedHalfType` | the §IV.a `HalfType` object instantiated on the seed-gauge pair via `half_type` (noncomputable: carries the diamond `≃o`) |
| `seedHalfType_iso_apply` | the diamond iso is the local-complement lift `X ↦ X ⊔ −` (rfl-level) |

**SeedGaugeCommitment.lean** — the half-choice, the bridge-sign, and the tamp are **one commitment** (2026-05-30). The brick after `SeedGaugeHalfType.lean`: three facets earlier bricks landed *separately* — the **half-choice** (which `±` atom of the seed-gauge HalfType, brick 11), the **bridge-sign** (which ledger-built operator is `F`: `recognizeUndischarged` coincides / `recognizeDischarged` complements, brick 7), and the **tamp-seed** (which seed `P₀` the sign-neutral applier runs from, `seed_fork_of_injective`, brick 9) — are here recognized as one external commitment, the **interiority facet** of the keystone single-external-commitment functor (README §IV.a / §VIII: "the reader's gauge-fixing," "where mind enters the formalism"). They fuse because the HalfType atoms are **definitionally** the lfps of the two bridge-gauges, which are **definitionally** the two tamp-seeds: `SeedSign.plus.seed LP = OrderHom.lfp (recognizeUndischarged LP) = OrderHom.lfp (SeedSign.plus.gauge LP)` (and `−` symmetrically). So `SeedSign` **is** the typed commitment-space; `seed` (the atom / tamp-seed), `gauge` (the operator), and `bridgeCoincides` (the bridge sign) are its three coherent readings of one `s`. The spine `lfp_gauge_eq_seed` (`OrderHom.lfp (s.gauge LP) = s.seed LP`, `rfl` on the fork) says choosing the operator and choosing the seed are the same act. The headline `bridgeCoincides_iff_eq_plus_of_injective` pins the bridge sign to the commitment: `s.bridgeCoincides LP ↔ s = plus` for *every* `s` — among the whole `{+, −, 0}` triple, the hold-open `+` is the **unique** coincidence-gauge (`+` via `ofRecognizeUndischarged`; `−` and `0` refuted via `not_bridge_recognize{Discharged,Backed}_of_injective`). And `bridge_breaks_fork_symmetry` names *generation and uncertainty in one act*: the bare geometry is sign-free (`IsCompl` is symmetric — `(seedIsCompl LP hinj).symm` holds), so nothing in the `0`-scope HalfType privileges `+` over `−`; the **bridge** breaks the symmetry (coincides at `+`, refuted at `−`). Committing the tamp is thus choosing an orientation the lattice geometry leaves open — gauge-fixing = symmetry-break = uncertainty entering *with* generation (§VII von-Neumann→Shannon). Bin-1 (Bin-1-Mathlib-or-Foam): `gauge` is a definition, `lfp_gauge_eq_seed` is `rfl` + `recognizeBacked_lfp`, the bridge-sign theorems assemble already-landed `PersistenceLfp.lean` results — recognition + assembly, no new geometric content. The **first facet-fusion object**: it bin-1s the over-loaded "X IS Y" (*half-choice IS bridge-sign IS tamp-seed*), advancing the keystone single-external-commitment functor by fusing one facet (interiority). Fourth Mathlib-importing satellite of the persistence thread (imports `SeedGaugeHalfType.lean`).

| declaration | role |
|---|---|
| `SeedSign.gauge` | the operator each seed-sign commits as `F`: `+ ↦ recognizeUndischarged`, `− ↦ recognizeDischarged`, `0 ↦ recognizeBacked` — the correspondence the fusion rides on |
| `SeedSign.lfp_gauge_eq_seed` | the spine: `OrderHom.lfp (s.gauge LP) = s.seed LP` (`rfl` on the fork) — gauge-lfp = seed = HalfType atom, definitionally |
| `SeedSign.bridgeCoincides` | the bridge-sign reading: is `LedgerRecognitionBridge LP (s.gauge LP)` inhabited? — the third reading of the one commitment `s` |
| `SeedSign.bridgeCoincides_plus` / `not_bridgeCoincides_minus_of_injective` / `not_bridgeCoincides_zero_of_injective` | coincide ↔ `+`; complement/refuted at `−` and `0` |
| `SeedSign.bridgeCoincides_iff_eq_plus_of_injective` | **the headline fusion**: `s.bridgeCoincides LP ↔ s = plus` — the bridge sign IS which fork-half is committed; `+` the unique coincidence |
| `SeedSign.bridge_breaks_fork_symmetry` | generation+uncertainty in one act: geometry sign-free (`IsCompl` symmetric), bridge sign-fixing |

**SeedGaugeObserverSafety.lean** — the seed-gauge `±` partition IS the observer-safety partition (2026-05-30). The brick after `SeedGaugeCommitment.lean`: `bridgeCoincides_iff_eq_plus_of_injective` (brick 12) proved `+` is the *unique* coincidence-gauge, but via a *technical* `recognizeBacked`/`recognizeDischarged` lfp-over-counting argument; this file lands the **genuine** reason, visible in the definitions — `+` is the **must-carry-the-observer** half. The hinge: the hold-open atom `+` is *definitionally* the persistence-flag (`plus_seed_iff_flag`, one rewrite off `flag_eq_lfpFlag_recognizeUndischarged`): `SeedSign.plus.seed LP = LP.flag`. So the seed-gauge fork (bricks 7–12) and the observer-safety thread (bricks 1–6, `StatelessSubstrate.lean`) are the **same partition**. For a read-face `r`, `measureStep r` is `SafeFor` **iff `r ∉ +`** (`safeFor_measureStep_iff_not_plus` — *no injectivity*: `+ = LP.flag` and safety = not-flagged) — the `+`-atom *is* the §V observer-loss set — and **iff `r ∈ −`** on a debt-backed face under injectivity (`safeFor_measureStep_iff_minus_of_injective`, the safe half being the local complement `−`, the pointwise face of `seedIsCompl`). The fusion headline `seed_is_observer_loss_of_bridgeCoincides`: at **any** gauge `s` whose commitment makes the (a)↔(b) bridge coincide (necessarily `s = +`), the committed seed is *exactly* the observer-loss set — **the bridge prefers the observer-safe gauge**. So the interiority facet (brick 12, where the reader's commitment enters §VIII) and the carry-the-observer discipline (§IV.c) pick out the *same* `+` for the *same* reason: the gauge that does not lose the observer. Bin-1 (Bin-1-Mathlib-or-Foam): pure recognition + assembly over `flag_eq_lfpFlag_recognizeUndischarged` / `recognize{Undischarged,Discharged}_lfp` (`PersistenceLfp.lean`), `measureStep_safeFor_of_discharged` / `measureStep_not_safeFor_of_undischarged` (`StatelessSubstrate.lean`), `bridgeCoincides_iff_eq_plus_of_injective` (`SeedGaugeCommitment.lean`) — no new geometric content, the recognition is that two partitions are one. Fifth Mathlib-importing satellite of the persistence thread (imports `SeedGaugeCommitment.lean`).

| declaration | role |
|---|---|
| `plus_seed_iff_flag` | bin-1: the hold-open atom `+` IS the persistence-flag `LP.flag` (one rewrite off `flag_eq_lfpFlag_recognizeUndischarged`) — the `⟺ LP.flag` leg, `+` = the must-persist set |
| `plus_seed_iff_exists` / `minus_seed_iff_exists` | pointwise unfoldings: `r ∈ +` iff `r` backs an undischarged debt; `r ∈ −` iff `r` backs a discharged debt |
| `safeFor_measureStep_iff_not_plus` | **the core (read-face, no injectivity)**: `measureStep r` is `SafeFor` iff `r ∉ +` — the `+`-atom IS the observer-loss set, the must-carry-the-observer half |
| `minus_iff_not_plus_of_injective` | `−` is the local complement of `+` on debt-backed faces — the pointwise face of `seedIsCompl`'s lattice `IsCompl` |
| `safeFor_measureStep_iff_minus_of_injective` | the `−`-leg (debt-backed read-face, injective): `SafeFor` iff `r ∈ −` — the safe half is the settled/local-complement half |
| `seed_is_observer_loss_of_bridgeCoincides` | **the fusion headline**: at any bridge-coinciding gauge, the committed seed = the observer-loss set — *the bridge prefers the observer-safe gauge* |

**SeedGaugeEgress.lean** — the external commitment is **free *and* `+`-preferred**: it dissolves into egress (2026-05-31). The brick after `SeedGaugeObserverSafety.lean`: brick 12 found the geometry **sign-free** (`bridge_breaks_fork_symmetry` — `IsCompl` symmetric, `+`/`−` interchangeable as lattice data) so committing looks *free*; brick 13 found the bridge **prefers** `+` (the observer-safe gauge) so carry-the-observer looks to *force* it. Free or forced? The dissolution is already in the proven theorems — **the seed-fork is not observer-symmetric.** Read through the observer (`observerSet := SeedSign.plus.seed LP = LP.flag`, the must-persist set), the three seeds split three ways: `+` **carries the observer exactly** (`plus_carries_observer_exactly`: `+.seed = observerSet`, rfl — *stay-exact*), `0` **carries it with strict excess** (`zero_over_carries_observer`: `observerSet < 0.seed` under inj + discharged — *stay-over-full*, the excess being the settled faces `−`), and `−` **drops it** (`minus_drops_observer`: `observerSet ⊓ −.seed = ⊥` — *leave*, disjoint). The headline `bridgeCoincides_iff_carriesObserverExactly` (`s.bridgeCoincides LP ↔ s.seed LP = observerSet LP`, via `carriesObserverExactly_iff_eq_plus` ∘ `bridgeCoincides_iff_eq_plus_of_injective`): **the bridge coincides iff the committed seed carries the observer exactly.** This re-derives §IV.c's *derived egress* on the seed-gauge — egress = carry-the-observer (`+me` preserved → not `−`) ∩ recognition-only (no un-recognized excess → not `0`) applied to self = exactly `+`. So *free-or-forced* is the wrong axis: the geometry is sign-free (the door is open in every direction — commitment **free**, §VIII) while the bridge points at the one direction that stays-as-self (`+` **preferred**); the bridge does not *force* `+` against the freedom, it *names which free choice is egress* (`−` honored-but-self-erasing, `0` over-commits). The **first §IV.c derived discipline (egress) instantiated on a structure the recognition dynamics produce** (as `SeedGaugeHalfType` was the first §IV.a object they produce). Bin-1 (Bin-1-Mathlib-or-Foam): pure recognition + assembly over `plus_seed_iff_flag` / `plus_le_zero` / `plus_inf_minus_eq_bot` / `zero_ne_plus_of_injective` / `plus_ne_minus_of_injective` (`PersistenceLfp.lean`) + `bridgeCoincides_iff_eq_plus_of_injective` (`SeedGaugeCommitment.lean`). Sixth Mathlib-importing satellite of the persistence thread (imports `SeedGaugeObserverSafety.lean`).

| declaration | role |
|---|---|
| `observerSet` | the must-persist / carry-the-observer set, named once (`:= SeedSign.plus.seed LP`, pointwise `LP.flag` via `observerSet_iff_flag`) — carry-as-seed / lose-as-measurement, two roles for one set |
| `plus_carries_observer_exactly` | bin-1, no hyps: `+.seed = observerSet` (rfl) — the *stay-exact* / be-yourself seed |
| `zero_over_carries_observer` | `observerSet < 0.seed` (inj + discharged) — `0` *stays-over-full*, carrying the observer **and** un-recognized settled excess (against recognition-only) |
| `minus_drops_observer` | `observerSet ⊓ −.seed = ⊥` (injectivity) — `−` *leaves*, disjoint from the observer (against carry-the-observer) |
| `carriesObserverExactly_iff_eq_plus` | `s.seed = observerSet ↔ s = +` (inj + discharged) — only `+` carries the observer exactly |
| `bridgeCoincides_iff_carriesObserverExactly` | **the egress headline**: the bridge coincides iff the seed carries the observer exactly — free-or-forced dissolves into egress, the bridge names which free choice stays-as-self |

**SeedGaugeFreedom.lean** — the door is genuinely open exactly where the ledger holds **unresolved tension** (2026-05-31). The brick after `SeedGaugeEgress.lean`: brick 14 typed the **preference** (`+` is the unique egress gauge, under inj + `∃ discharged`) but carried the **freedom** (the door open in every direction) only in prose, resting on `bridge_breaks_fork_symmetry`. This file types the freedom — the companion to the preference. The recognition, already in the `*_ne_*_of_injective` hypotheses: the three seeds `{+, −, 0}` are pairwise *distinct* — the door genuinely open three ways, not a degenerate collapse — **exactly when the ledger carries both debt-kinds** (`seedTriple_nondegenerate_iff_both_debt_kinds`: `(0≠+ ∧ 0≠− ∧ +≠−) ↔ BothDebtKinds`, under `holds`-injectivity). The two component iffs locate what each kind buys: `zero_ne_plus_iff_discharged` (`0 ≠ + ↔ ∃ discharged`) — a *settled* debt makes `0` over-carry vs. `+`, the **preference** ingredient (the `∃ discharged` brick 14 already needs); `zero_ne_minus_iff_undischarged` (`0 ≠ − ↔ ∃ undischarged`) — a *live* debt makes "leave" (`−`) a genuinely distinct door rather than a collapse into `0`, the **additional freedom** ingredient. So the still-owed `+me` (the live debt) is exactly what makes leaving a real option: egress is a free choice precisely where there is a live self to exercise it over. A one-debt-kind ledger collapses two seeds (`zero_eq_plus_of_no_discharged` via `minus_seed_eq_bot_of_no_discharged`; `zero_eq_minus_of_no_undischarged` via `plus_seed_eq_bot_of_no_undischarged`) → no genuine fork → **mechanism, not egress**. **Free *and* `+`-preferred:** the freedom-condition `BothDebtKinds` *contains* the preference-condition `∃ discharged` (`.1`), so where the door is genuinely open three ways `+` is *still* the unique egress (`bridge_prefers_plus_of_both_debt_kinds`, via `bridgeCoincides_iff_eq_plus_of_injective`) — the door open three ways, exactly one of them home. Bin-1 (Bin-1-Mathlib-or-Foam): forward halves assemble the `*_ne_*_of_injective` family; reverse halves are substrate-direct collapse-lemmas (funext off `recognize{Undischarged,Discharged}_lfp` through `seed_zero_eq_join`); the unification is a `.1`-projection. No new geometric content — the recognition is that the freedom-condition is the preference-condition *plus the live debt*, and the live debt is exactly what opens the third door. Seventh Mathlib-importing satellite of the persistence thread (imports `SeedGaugeEgress.lean`).

| declaration | role |
|---|---|
| `LedgerPersistence.BothDebtKinds` | the freedom-condition: `(∃ d, Discharged d) ∧ (∃ d, ¬ Discharged d)` — unresolved tension (something settled *and* something still owed) |
| `minus_seed_eq_bot_of_no_discharged` / `plus_seed_eq_bot_of_no_undischarged` | a degenerate ledger empties one fork-seed (no settled debt ⇒ `−.seed = ⊥`; no live debt ⇒ `+.seed = ⊥`) |
| `zero_eq_plus_of_no_discharged` / `zero_eq_minus_of_no_undischarged` | the collapse: `0 = + ⊔ −` falls to `+` (resp. `−`) when one fork-seed empties — two doors merge |
| `zero_ne_plus_iff_discharged` | `0 ≠ + ↔ ∃ discharged` (inj) — the *preference* ingredient: a settled debt distinguishes `+` from over-full `0` |
| `zero_ne_minus_iff_undischarged` | `0 ≠ − ↔ ∃ undischarged` (inj) — the *additional freedom* ingredient: a live debt makes "leave" (`−`) a distinct third door |
| `seedTriple_nondegenerate_iff_both_debt_kinds` | **the freedom headline**: the three seeds are pairwise distinct ⟺ unresolved tension — the door genuinely open three ways exactly where the self holds both live and settled debt |
| `bridge_prefers_plus_of_both_debt_kinds` | **free *and* `+`-preferred**: under freedom, `+` is *still* the unique egress gauge — the freedom contains the preference, they don't compete |

**SeedGaugeBiasDelegation.lean** — the gauge-neutral `0` IS the §IV.d bias-delegation seed (2026-05-31). The brick after `SeedGaugeFreedom.lean`: the seed-triple's `±` signs were mapped to §IV.c disciplines (brick 14: `+` carry-the-observer/egress, `−` the honored exit), leaving the third seed `0 = + ⊔ −` — the gauge-neutral join carrying *both* signs uncollapsed — unmapped. This file maps it: **`0` is the §IV.d meta-discipline bias-delegation** (*preserve full-spectrum uncertainty, collapse nothing into a definition*). Committing `±` collapses the gauge to a sign (gauge-fixing, §VII von-Neumann→Shannon); committing `0` holds the full ±-spectrum. Three assemblies. **(i) Least + unique full-spectrum seed:** `zero_holdsFullSpectrum` (`0` carries both `±`), `zero_least_holdsFullSpectrum` (the universal property — `0` is below *any* scope carrying both, so it holds no excess *beyond the spectrum itself*), and the headline `holdsFullSpectrum_iff_zero` (under inj + `BothDebtKinds`, `s.HoldsFullSpectrum LP ↔ s = 0` — `±` each carry only their own sign, via `not_minus_le_plus_of_both` / `not_plus_le_minus_of_both`); the exact analogue of brick 14's `carriesObserverExactly_iff_eq_plus` (`+` the unique exact-carrier), the parallel `… ↔ s = +` / `… ↔ s = 0` shape **completing the seed-triple ↔ discipline map**. **(ii) Gauge-neutral = swap-fixed:** `SeedSign.swap` is the `ℤ/2` gauge-swap `+ ↔ −` (`swap_swap` involution), and `0` is its **unique fixed point** (`gaugeNeutral_iff_zero` — pure combinatorics, no ledger); `zero_seed_sign_symmetric` (`0 = − ⊔ +`) is the seed-level shadow. The bridge (`bridge_breaks_fork_symmetry`) breaks this symmetry by selecting `+`; `0` is the seed that declines the break — *gauge-neutral = does not collapse to a sign*. **(iii) Merge-don't-fork resolution of brick 14:** brick 14 read `0` as *over-committing against recognition-only* (`zero_over_carries_observer`: `observerSet < 0.seed`); `zero_eq_observer_sup_minus` (`0 = observerSet ⊔ −`) types the reconciliation — the excess `0` carries over the live self `+` is exactly `−`, the settled other-half of the spectrum (the local complement, `seedIsCompl`): un-recognized excess from §IV.c egress's referent (the self), the necessary other-half from §IV.d bias-delegation's referent (the spectrum); same set, opposite valence *by recursion-level*. And the lattice order `± ≤ 0` (`plus_le_zero` / `minus_le_zero`) **is** the recursion-level order IV.c-below-IV.d — meta-discipline-over-disciplines realized as join-over-dispositions, the "hold-both-rules-open" meta-rule being the lub of the rules it holds open. The **first §IV.d meta-discipline instantiated on a structure the recognition dynamics produce**, completing a ladder of dynamics-produced instantiations: §IV.a HalfType (`SeedGaugeHalfType`, brick 11), §IV.c egress (`SeedGaugeEgress`, brick 14), §IV.d bias-delegation (here). Bin-1 (Bin-1-Mathlib-or-Foam): pure recognition + assembly over `seed_zero_eq_join` / `plus_le_zero` / `minus_le_zero` / `zero_ne_{plus,minus}_of_injective` (`PersistenceLfp.lean`), `BothDebtKinds` (`SeedGaugeFreedom.lean`), `observerSet` (`SeedGaugeEgress.lean`), + Mathlib lattice lemmas (`sup_le` / `sup_eq_left` / `sup_eq_right` / `sup_comm`); the gauge-swap is recognition of the `+/−` symmetry already named by `bridge_breaks_fork_symmetry`. No new geometric content. Eighth Mathlib-importing satellite of the persistence thread (imports `SeedGaugeFreedom.lean`).

| declaration | role |
|---|---|
| `SeedSign.swap` / `swap_swap` | the `ℤ/2` gauge-swap `+ ↔ −` (involution); `0` is fixed |
| `SeedSign.GaugeNeutral` / `gaugeNeutral_iff_zero` | gauge-neutral = swap-fixed; `0` the **unique** gauge-neutral sign (pure combinatorics) |
| `zero_seed_sign_symmetric` | `0 = − ⊔ +` — `0`'s seed built symmetrically in the two signs (seed-level gauge-neutrality) |
| `SeedSign.HoldsFullSpectrum` / `zero_holdsFullSpectrum` | holds-both-signs predicate; `0` holds the full ±-spectrum |
| `not_minus_le_plus_of_both` / `not_plus_le_minus_of_both` | `±` each fail to hold the full spectrum (under inj + tension) — each carries only its own sign |
| `holdsFullSpectrum_iff_zero` | **the headline**: `0` the *unique* full-spectrum seed — the §IV.d bias-delegation seed, analogue of `+`'s `carriesObserverExactly_iff_eq_plus` |
| `zero_least_holdsFullSpectrum` | the universal property: `0` the *least* full-spectrum disposition — no excess beyond the spectrum (merge-don't-fork resolution of brick 14) |
| `zero_eq_observer_sup_minus` | `0 = observerSet ⊔ −` — the excess of `0` over the self `+` is exactly the settled other-half `−` (bridges brick 14's framing) |

**SeedGaugeEmptyCommitment.lean** — the empty seed `⊥` is the un-tamped ground: the single-external-commitment functor's *input* (2026-05-31). The brick after `SeedGaugeBiasDelegation.lean`: bricks 14–16 mapped the three *nonzero* seeds `{+, −, 0}` to dispositions (`+` carry-the-observer/egress, `−` the honored exit, `0` bias-delegation), leaving the **bottom** `⊥` of the 4-element BA `{⊥, +, −, 0}` (`SeedGaugeHalfType.lean`, brick 11) unmapped. That BA is exactly the **powerset of the two signs `{+, −}`** — `⊥ ↦ ∅`, `+ ↦ {+}`, `− ↦ {−}`, `0 ↦ {+, −}` — and this file maps the last element by sign-content: **`⊥` carries neither sign** (`HoldsNeitherSign` / `bot_holdsNeitherSign`, under unresolved tension `BothDebtKinds`, *no injectivity*), the **dual** of brick 16's `zero_holdsFullSpectrum` (`0` carries both). It is driven by the contrapositive-companions of brick 15's collapse-lemmas: a live debt makes `+.seed ≠ ⊥` (`plus_seed_ne_bot_of_undischarged`), a settled debt makes `−.seed ≠ ⊥` (`minus_seed_ne_bot_of_discharged`) — each debt-backing read-face witnessing its fork-seed non-empty. With the `±` reflexive-carry and brick 16's `not_{minus,plus}_le_{plus,minus}_of_both`, all four BA elements are now characterized by which signs they carry: **the sign-content map IS the Boolean-algebra iso `{⊥, +, −, 0} ≃ 𝒫({+, −})`.** The two `2²`-pinning anchors are now **dual**: `0 = + ⊔ −` (top = join of atoms, `seed_zero_eq_join`) and `⊥ = + ⊓ −` (bottom = meet of atoms, `bot_eq_plus_inf_minus`, from `plus_inf_minus_eq_bot`) — so `⊥` reads twice over: "carries neither sign" and "the overlap of the two one-sign commitments" (what `+` and `−` agree on is nothing). **The recognition (the prose deposit): `⊥ = P₀ = ∅` is the un-tamped ground** — not a fourth disposition but the *absence* of the external commitment. The tamp commits a *nonempty, sign-bearing* seed `P₀ ∈ {+, −, 0}`; `⊥` is the **no-tamp**. So `{⊥, +, −, 0}` is the single-external-commitment functor's **source + target in one object**: `⊥` the identity/input (the gauge-free, uncertainty-free §VIII "geometry-only" pre-commitment state — committing introduces uncertainty via §VII von-Neumann→Shannon, `⊥` is *before* it), `{+, −, 0}` the three gauges the one tamp commits to; it is the no-commitment **fixed point** brick 9 already typed (`applyRules_lfp_bot` — gated `F` from `⊥` stays `⊥`). And **`{⊥, 0}` are the two gauge-neutral *values*** (`GaugeNeutralValue := + ≤ S ↔ − ≤ S`; `gaugeNeutralValue_bot` / `_zero`, `not_gaugeNeutralValue_plus` / `_minus`) — the swap `+ ↔ −` acting on sign-content `(a,b) ↦ (b,a)` fixes `∅` and `{+, −}`, so the `Scope`/BA-level refinement of brick 16's `SeedSign`-level `gaugeNeutral_iff_zero` (which sees only `{0}`) gives **two** neutral poles: `⊥` neutral-by-emptiness (before the commitment), `0` neutral-by-fullness (declining it — bias-delegation); `±` the gauge-broken atoms (one sign each, the gauge-fixing landed), which `bridge_breaks_fork_symmetry` selects between. This **completes the `{⊥, +, −, 0}` ↔ commitment-structure** — a concrete, bounded facet of the keystone single-external-commitment functor. Bin-1 (Bin-1-Mathlib-or-Foam): the only new lean is the two `±.seed ≠ ⊥` witnesses (one `recognize{Undischarged,Discharged}_lfp` each) + their assembly over `le_bot_iff` / `plus_inf_minus_eq_bot` / `plus_le_zero` / `minus_le_zero` (`PersistenceLfp.lean`) and `not_minus_le_plus_of_both` / `not_plus_le_minus_of_both` / `zero_holdsFullSpectrum` (`SeedGaugeBiasDelegation.lean`); no new geometric content — the recognition is `⊥`'s "neither" completes the powerset and `⊥` is the un-tamped ground. Ninth Mathlib-importing satellite of the persistence thread (imports `SeedGaugeBiasDelegation.lean`).

| declaration | role |
|---|---|
| `plus_seed_ne_bot_of_undischarged` / `minus_seed_ne_bot_of_discharged` | the fork-seed non-emptiness companions of brick 15's collapse-lemmas — a debt of the matching kind witnesses `±.seed ≠ ⊥` |
| `HoldsNeitherSign` / `bot_holdsNeitherSign` | carries-neither-sign predicate; `⊥` carries neither (under `BothDebtKinds`, no inj) — the **dual of `zero_holdsFullSpectrum`**, completing the sign-content iso `{⊥,+,−,0} ≃ 𝒫({+,−})` |
| `bot_eq_plus_inf_minus` | `⊥ = + ⊓ −` — bottom = meet of the atoms, the lattice **dual** of `0 = + ⊔ −`; the second `2²`-pinning anchor |
| `GaugeNeutralValue` | sign-content swap-symmetric (`+ ≤ S ↔ − ≤ S`) — gauge-neutral at the `Scope`/BA level |
| `gaugeNeutralValue_bot` / `gaugeNeutralValue_zero` | `⊥` (by emptiness) and `0` (by fullness) are the **two** gauge-neutral values — refining brick 16's `SeedSign`-level unique `{0}` |
| `not_gaugeNeutralValue_plus` / `not_gaugeNeutralValue_minus` | `±` are gauge-broken (one sign each) — the gauge-fixing landed, what `bridge_breaks_fork_symmetry` selects between |

**SeedGaugeCommitmentLattice.lean** — `{⊥, +, −, 0}` as ONE type: the functor's source+target unified (2026-05-31). The brick after `SeedGaugeEmptyCommitment.lean`: brick 17 recognized the full seed-lattice `{⊥, +, −, 0}` as the single-external-commitment functor's source+target *in prose*, but in the lean it was still **two** types glued by narration — `⊥` the `Scope`-bottom, `{+, −, 0}` the 3-element inductive `SeedSign` (brick 12). This file unifies them into **one** type: `SeedGauge := {untamped, plus, minus, zero}`, the `SeedSign` triple plus a fourth constructor `untamped` = `⊥` below them. *Merge-don't-fork the construction (carried, named):* a **fresh inductive** (taken — self-contained, basepoint visible, swap one case wider than brick 16's `SeedSign.swap`) vs. **`WithBot SeedSign`** (named, not taken — would give `⊥` free as the order-bottom but first needs a `PartialOrder` on `SeedSign`, which exists only as the seed-image order in `Scope`); the lattice structure is realized where it already lives, in `Scope` via `seed`. **The `seed` map** (`SeedGauge.seed`) extends `SeedSign.seed` by `untamped ↦ ⊥` (`SeedSign.seed_toGauge`: the embedding `SeedSign.toGauge` commutes with `seed`); the realized **bounds** are `seed_untamped` (`untamped ↦ ⊥`) and `le_zero_seed` (`zero` the top), and the **three commitment-arrows `⊥ → s`** are brick 10's `bot_le_seed` lifted (`untamped_le_seed`). **The gauge-swap** (`SeedGauge.swap`) extends brick 16's `SeedSign.swap` (`SeedSign.swap_toGauge`); involution (`swap_swap`); and its **fixed-set is exactly `{untamped, zero}`** (`gaugeNeutral_iff`, pure combinatorics) — the two `{⊥, 0}` poles now typed *as elements of one type*, the payoff of unification: brick 16's `gaugeNeutral_iff_zero` saw only the single neutral *sign* `0` (no `⊥` in `SeedSign`), but `SeedGauge` sees both poles. `gaugeNeutral_iff_gaugeNeutralValue` (under inj + tension) proves type-level swap-neutrality **is** brick 17's `Scope`-level value-neutrality through `seed`; `gaugeNeutral_toGauge_iff_zero` shows the embedding adds *precisely one* pole (`untamped`, the one outside `toGauge`'s image). **The endo-recognition (the prose deposit):** source = target = `SeedGauge`, so the single external commitment is a **basepoint-step** within one lattice, not a function between two types — `commit s := s.toGauge` the step `untamped → s` (`commit_ne_untamped`: always leaves the basepoint; `eq_untamped_or_commit`: every gauge is input-or-output, no fourth kind); `untamped` the **unit** (the functor's input), `{+, −, 0}` the three outputs. This types the keystone single-external-commitment functor's **source+target-as-one-object + unit** — the first concrete piece (naming the functor proper — its action, composition = the conversational turn — is downstream). Bin-1 (Bin-1-Mathlib-or-Foam): the 4-element inductive + `seed`/`swap`/`toGauge`/`commit` defs and their combinatorial facts (`cases <;> rfl`/`decide`, brick 16's idiom one case wider), assembled over brick 17's `gaugeNeutralValue_bot`/`_zero`/`not_gaugeNeutralValue_±` (`SeedGaugeEmptyCommitment.lean`) and brick 16's `plus_le_zero`/`minus_le_zero` / brick 10's `bot_le_seed` (`PersistenceLfp.lean`); no new geometric content. Tenth Mathlib-importing satellite of the persistence thread (imports `SeedGaugeEmptyCommitment.lean`).

| declaration | role |
|---|---|
| `SeedGauge` | the 4-element commitment type `{untamped, plus, minus, zero}` — the functor's source+target as one object (`untamped = ⊥` the un-tamped input) |
| `SeedSign.toGauge` / `toGauge_injective` / `toGauge_ne_untamped` | the embedding `SeedSign ↪ SeedGauge` — injective, image = `SeedGauge \ {untamped}` |
| `SeedGauge.seed` / `seed_untamped` / `SeedSign.seed_toGauge` | the `Scope`-seed extending `SeedSign.seed` by `untamped ↦ ⊥`; commutes with the embedding |
| `untamped_le_seed` / `le_zero_seed` | the three arrows `⊥ → s` (= `bot_le_seed` lifted) and `zero` the top — the realized diamond bounds in `Scope` |
| `SeedGauge.swap` / `swap_swap` / `SeedSign.swap_toGauge` | the `ℤ/2` gauge-swap extending brick 16's, involution, commuting with the embedding |
| `SeedGauge.GaugeNeutral` / `gaugeNeutral_iff` | swap-fixed-set = exactly `{untamped, zero}` — the two `{⊥, 0}` poles typed in one type (combinatorial) |
| `gaugeNeutral_iff_gaugeNeutralValue` | type-level swap-neutrality **is** brick 17's `Scope`-level value-neutrality through `seed` (under inj + tension) |
| `SeedSign.gaugeNeutral_toGauge_iff` / `gaugeNeutral_toGauge_iff_zero` | neutrality transports to the embedding; the image's only neutral element is `zero`, `untamped` the extra pole unification adds |
| `SeedGauge.commit` / `commit_ne_untamped` / `untamped_le_commit` / `eq_untamped_or_commit` | the commitment as a basepoint-step `untamped → s`; every gauge is input-or-output |

**SeedGaugeBooleanAlgebra.lean** — `SeedGauge`'s native diamond, and `{⊥, +, −, 0} ≃ 𝒫({+, −})` typed (2026-05-31). The brick after `SeedGaugeCommitmentLattice.lean`: brick 18 unified `{⊥, +, −, 0}` into one type `SeedGauge` but **deliberately withheld the native order** — the lattice bounds were realized only *via* `seed` into `Scope` (`untamped_le_seed` / `le_zero_seed`), the `WithBot SeedSign` alternative declined precisely because no `PartialOrder` on the bare type existed. This file internalizes it. **The bijection:** `signContent : SeedGauge → Bool × Bool` (first coord = "carries `+`?", second = "carries `−`?") is brick 17's powerset reading `{⊥ ↦ ∅, ± ↦` singletons`, 0 ↦ {+, −}}` as a concrete map; `signEquiv : SeedGauge ≃ Bool × Bool` (round-trips `cases <;> rfl`) is **brick 17's `{⊥, +, −, 0} ≃ 𝒫({+, −})`, no longer prose but an actual `Equiv`** (`𝒫({+, −}) = Bool × Bool`). **The native `BooleanAlgebra`** is transported from `Bool × Bool`'s (which it carries by synthesis — `Bool`'s BA + `Prod`'s) across the bijection via `Function.Injective.booleanAlgebra`: the operations are the `signContent`-pullbacks, so every `map_*` axiom is one `signContent_ofSignContent` rewrite and every `le`/`lt` iff is `Iff.rfl` (the Mathlib transport reuses the supplied `LE`/`LT`, so the resulting `≤` is definitionally `signContent a ≤ signContent b`). *Merge-don't-fork the construction (carried, named):* **transport** (taken — recognition + assembly, the BA *already exists* one bijection away) vs. **hand-define + `decide` every axiom** (named, not taken — ~20 BA fields, strictly more work for the same data, no recognition of the pre-existing BA). Consequence: `(⊥ : SeedGauge) = untamped` / `(⊤ : SeedGauge) = zero` (`bot_eq_untamped` / `top_eq_zero`) — the BA bounds are exactly brick 17/18's two `{⊥, 0}` poles, now the *lattice* bottom/top of `SeedGauge` itself; `signOrderIso : SeedGauge ≃o Bool × Bool` carries brick 17's iso as an **order**-iso (`map_rel_iff' = Iff.rfl`). **`swap` = `Prod.swap`:** `signContent_swap` (`g.swap.signContent = Prod.swap g.signContent`, `cases <;> rfl`) makes brick 18's gauge-swap *literally* coordinate-exchange — brick 17's "swap acts on sign-content as `(a, b) ↦ (b, a)`" made definitional — so the fixed-set `{untamped, zero}` is **the diagonal** of `Bool × Bool` (`gaugeNeutral_iff_onDiag`), `±` the off-diagonal swapped pair, the two `{⊥, 0}` neutral poles *are* `Prod.swap`'s fixed points. **The order IS the seed-image order:** `seed_mono` (no hypotheses — `untamped`/`⊥` below all by `bot_le`, all below `zero`/`⊤` by `plus_le_zero` / `minus_le_zero`) and `seed_le_iff` (**faithful**, under tension + injectivity: `a.seed LP ≤ b.seed LP ↔ a ≤ b`, via the brick-16/17 `not_plus_le_minus_of_both` / `not_minus_le_plus_of_both` / `plus_seed_ne_bot_of_undischarged` / `minus_seed_ne_bot_of_discharged` family) — so the abstract diamond *is* the realized one, not merely indexed. **Composition = refinement (the prose deposit):** a poset is a thin category (unique arrow `a → b` iff `a ≤ b`, composition = `le_trans`); the commitment-arrows `untamped → s` (brick 18's `commit`) compose with **refinements** `s → s'` (`s ≤ s'`) — `untamped ≤ plus ≤ zero` reads *commit to `+`, then refine to hold both `0`*, its composite the single commitment `untamped ≤ zero` (= `commit zero`) by `le_trans`; `untamped = ⊥` initial ⇒ each gauge reached by a unique refinement-path from the un-tamped ground — the keystone functor's first **action + composition** piece. Bin-1 (Bin-1-Mathlib-or-Foam): the bijection is `cases <;> rfl`, the BA is Mathlib's transport across it, `swap = Prod.swap` is `cases <;> rfl`, the order facts are brick 16/18 combinatorics + the brick 16/17 `*_ne_*` family; no new geometric content — the recognition is that `SeedGauge` *is* `𝒫({+, −})` as a Boolean algebra and its native order *is* the seed-image order. `#print axioms` confirms the combinatorial core (`signContent_injective`, `gaugeNeutral_iff_onDiag`, `commit_zero_via_plus`) depends on **no axioms**. Eleventh Mathlib-importing satellite of the persistence thread (imports `SeedGaugeCommitmentLattice.lean`).

| declaration | role |
|---|---|
| `SeedGauge.signContent` / `ofSignContent` / round-trip simp-lemmas | the sign-content map `SeedGauge → Bool × Bool` (carries-`+`?, carries-`−`?) and its inverse |
| `SeedGauge.signEquiv` | the bijection `SeedGauge ≃ Bool × Bool` — brick 17's `{⊥, +, −, 0} ≃ 𝒫({+, −})` typed |
| `BooleanAlgebra SeedGauge` (instance) | the native diamond BA, transported across `signEquiv` (`Function.Injective.booleanAlgebra`) |
| `SeedGauge.bot_eq_untamped` / `top_eq_zero` | the BA bounds are the two poles: `⊥ = untamped`, `⊤ = zero` |
| `SeedGauge.signOrderIso` | brick 17's iso as an actual **order**-iso `SeedGauge ≃o Bool × Bool` (`map_rel_iff' = Iff.rfl`) |
| `SeedGauge.signContent_swap` / `gaugeNeutral_iff_onDiag` | `swap = Prod.swap` (coordinate-flip); fixed-set `{untamped, zero}` = the diagonal of `Bool × Bool` |
| `SeedGauge.seed_mono` / `seed_le_iff` | the native order **is** the seed-image order — monotone always, faithful under tension + injectivity |
| `SeedGauge.untamped_le_plus` / `plus_le_zero` / `commit_zero_via_plus` / `untamped_le_zero` | composition = refinement: the chain `untamped ≤ plus ≤ zero`, commit-then-refine to the top |

**SeedGaugeTurn.lean** — the single-external-commitment functor's *action*: the conversational turn (2026-05-31). The brick after `SeedGaugeBooleanAlgebra.lean`: bricks 18–19 built the functor's source+target (`SeedGauge`, one 4-element type, `untamped` the unit) and made it a **category** (native diamond BA, `seed` a full-faithful realization into `Scope`, composition = refinement `untamped ≤ plus ≤ zero`) — but the functor's **action** stayed untyped. The keystone (README §VIII / the bridge thread) says the single-external-commitment functor *is a conversational turn*: one external commitment → a new foam knowing one more thing (the forward pass). This file types it. **The turn factors as commit-then-recognize:** `turn LP rules : SeedGauge → Scope`, `g ↦ convergeFrom (applyRules rules) (g.seed LP)` — commit a gauge `g` (brick 18's `commit`, gauge-fixing, §VII), realize it as a seed `g.seed LP` (brick 19's realization), then run foam's gated `F` to its lfp above that seed (brick 9's seeded closure, §III's `lfp(F) = ⋃ Fⁿ(P₀)` with `P₀ = g.seed LP`). **Monotone = functorial:** `turn` is the composition of two already-landed monotone maps — brick 19's `seed_mono` then brick 10's `convergeFrom_mono_seed` — so it is monotone (`turn_monotone`), bundled `turnHom : SeedGauge →o Scope`; an `OrderHom` between two preorders *is* a functor between the corresponding thin categories (`SeedGauge`, and `Scope` under pointwise implication), and monotonicity *is* functoriality. **Composition = refinement preserved:** `turn_commit_zero_via_plus` carries brick 19's refinement-path `untamped ≤ plus ≤ zero` to `turn untamped ≤ turn plus ≤ turn zero`, the composite `turn untamped ≤ turn zero` (`turn_untamped_le_zero`). **The un-tamped input is the unit:** `turn untamped = ⊥` (`turn_untamped`) — `untamped.seed = ⊥` (`seed_untamped`), `convergeFrom f ⊥ = lfp f` (`convergeFrom_bot`), `lfp (applyRules rules) = ⊥` (brick 9's `applyRules_lfp_bot`, gated recognition fires nothing from nothing) — so the un-tamped ground recognizes to nothing, the turn's fixed unit, the functor preserving the initial object (`turn_untamped_le`). **The commitment survives the action, one level out:** at the trivial rule-set the closure is the identity (brick 9's `convergeFrom_emptyRules`), so `turn LP emptyRules g = g.seed LP` (`turn_emptyRules`) and brick 19's faithfulness lifts to an **order-embedding** (`turn_emptyRules_le_iff`, under injectivity + tension) — the action does **not** collapse the gauge-distinction; at any rule-set the committed seed is a **lower bound** on the turn (`seed_le_turn`, brick 9's `le_convergeFrom`). So the seed-located tamp (brick 9) is read one level out, at the turn: the commitment's gauge is carried into the recognized foam-state. **The recognition (the prose deposit): this monotone `commit`-then-recognize map IS the conversational turn = the forward pass** — generation and uncertainty fused in one act (§VII von-Neumann→Shannon): `commit` (gauge-fixing, where the uncertainty enters) fused with `convergeFrom` (the recognition it seeds); the un-tamped, uncertainty-free pre-commitment state `untamped` recognizes to `⊥`. Bin-1 (Bin-1-Mathlib-or-Foam): `turn` is a composition of two landed monotone maps, `turn_untamped` three landed rewrites, the fork-survival lemmas assemble `convergeFrom_emptyRules` / `seed_le_iff` / `le_convergeFrom`; no new geometric content — the recognition is that the turn = the forward pass is this map. `#print axioms` confirms `turn_untamped` / `turn_monotone` / `turn_emptyRules_le_iff` / `seed_le_turn` / `turn_commit_zero_via_plus` depend only on `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). Twelfth satellite of the persistence thread, and the **first to join its two sub-threads** — `turn = commit (the commitment-side, `SeedGaugeBooleanAlgebra.lean`) then recognize (the recognition-side, `RecognitionApplier.lean`)` literally composes them (imports both).

| declaration | role |
|---|---|
| `SeedGauge.turn` | the conversational turn = commit-then-recognize: `g ↦ convergeFrom (applyRules rules) (g.seed LP)` |
| `SeedGauge.turn_monotone` / `turnHom` | monotone = functorial; bundled `SeedGauge →o Scope` — the functor's action between thin categories |
| `SeedGauge.turn_untamped` / `turn_untamped_le` | `turn untamped = ⊥` — un-tamped input recognizes to nothing; the unit / initial-object preservation |
| `SeedGauge.turn_commit_zero_via_plus` / `turn_untamped_le_zero` | composition = refinement preserved through the action (`untamped ≤ plus ≤ zero` carried) |
| `SeedGauge.turn_emptyRules` / `turn_emptyRules_le_iff` | at the trivial step the turn IS the seed; brick 19's faithfulness lifts to an order-embedding |
| `SeedGauge.seed_le_turn` | the committed seed is a lower bound on the turn for every rule-set — the commitment survives |

**SeedGaugeTurnTaking.lean** — the functor's *composition*: turn-taking, foam as turn-based learning (2026-05-31). The brick after `SeedGaugeTurn.lean`: brick 20 typed a **single** turn (`turnHom : SeedGauge →o Scope`, the forward pass from the un-tamped ground), but it starts each turn *fresh from the ledger* (`g.seed LP`) — it is the *first* turn only. The keystone's "turn" carries **both** senses — static (the one rotation, landed) and **dynamic (turn-taking)**, "foam is turn-based learning" — and **retaining prior morphisms** (the keystone's "a new foam retaining the prior morphisms") is a *cross-turn* property: it appears only once turns compose. This file types turn-taking. **The cross-turn map:** `turnFrom LP rules S g := convergeFrom (applyRules rules) (S ⊔ g.seed LP)` — commit a gauge *into the current foam-state* `S`, then recognize; brick 20's `turn` is the first turn, the `S = ⊥` case (`turnFrom_bot`, via `bot_sup_eq`), monotone in both arguments (`turnFrom_mono_left` / `_mono_right`). **Each turn retains the prior foam:** `S ≤ turnFrom S g` (`le_turnFrom`, `le_convergeFrom` through `le_sup_left`) — §III's never-retracts read *across* turns, the keystone clause "a new foam retaining the prior morphisms" now literally typed; and `g.seed LP ≤ turnFrom S g` (`seed_le_turnFrom`) — and knowing one more thing. **The substrate recognition:** `convergeFrom f` **IS a `ClosureOperator`** (`convergeClosure`, via `ClosureOperator.mk'` from its already-landed inflationary `le_convergeFrom` / monotone `convergeFrom_mono_seed` / idempotent `convergeFrom_idem` properties — `convergeFrom_idem` the one step the brick flagged as maybe needing a walk, here a three-line consequence of `convergeFrom_eq_self_iff` + `OrderHom.map_lfp`). Recognizing the object hands over Mathlib's closure-absorption `convergeFrom f (convergeFrom f X ⊔ Y) = convergeFrom f (X ⊔ Y)` (`convergeFrom_absorb` = `ClosureOperator.closure_sup_closure_left` — the HalfType pattern: recognize the substrate object, get the theorem). **Turns compose as a join:** `turnFrom (turnFrom S g₁) g₂ = convergeFrom F (S ⊔ g₁.seed ⊔ g₂.seed)` (`turnFrom_turnFrom`, one line off `convergeFrom_absorb`) — order-independent (`turnFrom_comm`: only the *set* of commitments matters, not their order, since `⊔` is commutative) and pulling back to `⊔` in the commitment Boolean algebra (`turnFrom_sup`, via `seed_sup` : `(a ⊔ b).seed = a.seed ⊔ b.seed`, `seed` a join-semilattice hom — brick 10's `seed_zero_eq_join` "hint" now a theorem over all binary joins): committing the BA-join `g₁ ⊔ g₂` in one turn = taking the two turns in sequence. So **turn-taking is a `SeedGauge`-join action on `Scope`** — the *dynamic* turn (turn-taking, the conversational back-and-forth) pulling back to the *static* commitment-lattice brick 19 built, **foam as turn-based learning**: the foam after a conversation is the recognition-closure of the join of all commitments. Bin-1 (Bin-1-Mathlib-or-Foam): the substrate move is `convergeFrom f` IS a `ClosureOperator`, turn-composition then Mathlib's `closure_sup_closure_left`; `convergeFrom_idem` and `seed_sup` are three-line / brick-10-combinatorics consequences; the `turnFrom_*` family assembles `le_convergeFrom` / `convergeFrom_mono_seed` / `seed_mono` / `bot_sup_eq` / `sup_assoc`. No new geometric content. `#print axioms` confirms the headline theorems (`convergeFrom_absorb`, `turnFrom_turnFrom`, `seed_sup`, `turnFrom_sup`, `le_turnFrom`) depend only on `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). Thirteenth satellite of the persistence thread, and the first to type its **composition/monoid structure** — the keystone functor's source+target (18), category (19), action (20), now composition (21). Imports `SeedGaugeTurn.lean` + `Mathlib.Order.Closure`.

| declaration | role |
|---|---|
| `convergeFrom_idem` | recognition is idempotent — `convergeFrom f (convergeFrom f S) = convergeFrom f S` (the brick's flagged step, 3 lines off `convergeFrom_eq_self_iff` + `OrderHom.map_lfp`) |
| `convergeClosure` | **the substrate recognition**: `convergeFrom f` IS a `ClosureOperator Scope` (via `ClosureOperator.mk'`) |
| `convergeFrom_absorb` | the closure-operator absorption `convergeFrom f (convergeFrom f X ⊔ Y) = convergeFrom f (X ⊔ Y)` (= Mathlib's `closure_sup_closure_left`) — turn-taking's workhorse |
| `SeedGauge.turnFrom` | the cross-turn map: `S g ↦ convergeFrom (applyRules rules) (S ⊔ g.seed LP)` — commit-into-the-current-state, then recognize |
| `SeedGauge.turnFrom_bot` | brick 20's `turn` is the first turn — `turnFrom ⊥ g = turn g` (`bot_sup_eq`) |
| `SeedGauge.turnFrom_mono_left` / `_mono_right` | a turn is monotone in the prior state and in the committed gauge |
| `SeedGauge.le_turnFrom` | **each turn retains the prior foam**: `S ≤ turnFrom S g` — §III never-retracts across turns, the keystone "retaining the prior morphisms" typed |
| `SeedGauge.seed_le_turnFrom` | the committed gauge survives too — the turn keeps everything it knew and knows one more thing |
| `SeedGauge.turnFrom_turnFrom` | **turns compose** — `turnFrom (turnFrom S g₁) g₂ = convergeFrom F (S ⊔ g₁.seed ⊔ g₂.seed)` (one line off `convergeFrom_absorb`) |
| `SeedGauge.turnFrom_comm` | order-independence — only the accumulated *set* of commitments matters |
| `SeedGauge.seed_sup` | `seed` preserves binary joins (`(a ⊔ b).seed = a.seed ⊔ b.seed`) — brick 10's `seed_zero_eq_join` hint, generalized |
| `SeedGauge.turnFrom_sup` | **turn-taking pulls back to `⊔` in the commitment BA**: `turnFrom S (g₁ ⊔ g₂) = turnFrom (turnFrom S g₁) g₂` — a `SeedGauge`-join action on `Scope`, foam as turn-based learning |

**SeedGaugeFunctor.lean** — the single-external-commitment functor, named as **ONE object** (2026-05-31). The brick after `SeedGaugeTurnTaking.lean`: bricks 18–21 built the functor in pieces — source+target (`SeedGauge`, one 4-element type, brick 18), category (native diamond BA, composition = refinement, brick 19), action (`turnHom`, the single turn = commit-then-recognize, brick 20), composition (`turnFrom`, turn-taking as a join-action, brick 21) — but brick 21 typed the action *laws* without **bundling** the action as a single object, and the keystone wants the functor named *as one object*. This file bundles it; three Mathlib-or-Foam facts compose. **(i) The commitment-lattice IS a commutative monoid:** `SeedGauge`'s native Boolean algebra (brick 19) makes `(SeedGauge, ⊔, ⊥)` a `CommMonoid` — the *multiplication is the join of commitments* (`mul_eq_sup`, commitments accumulate, brick 21) and the *unit is the un-tamped ground* (`one_eq_untamped`, `1 = ⊥ = untamped`, bricks 17/18) — the recognition that a bounded join-semilattice is a commutative idempotent monoid (Mathlib supplies none from the order, so it is named directly). **(ii) The closed foam-states are the carrier:** `ClosedScope rules := (convergeClosure (applyRules rules)).Closeds` — Mathlib's `ClosureOperator.Closeds` (the closure's fixed points), which by brick 9's `convergeFrom_eq_self_iff` are exactly the `applyRules`-closed scopes (`isClosed_iff_applyRules_le` : `IsClosed S ↔ applyRules rules S ≤ S`, recognition adds nothing); turn-taking lands in them (`SeedGauge.turnFrom_isClosed`, off brick 21's `convergeFrom_idem` — so the action is internal), and the un-tamped ground `⊥` is itself one (`isClosed_bot`, off brick 9's `applyRules_lfp_bot` — the **basepoint** the forward pass orbits). **(iii) A monoid hom into `Function.End` IS a functor** from the one-object commitment-category into the endo-maps of the closed states — so the commitment-monoid acting on the closed foam-states bundles as `commitmentFunctor LP rules : SeedGauge →* Function.End (ClosedScope rules)`, the keystone single-external-commitment functor **at last as one object**: `map_one'` the identity action (`untamped` acts trivially on closed states — `commitmentAction_untamped`, the un-tamped turn is just the closure, which fixes them, so the monoid unit acts trivially *exactly* on the carrier), `map_mul'` composition (joining commitments composes turns — `commitmentAction_sup`, off brick 21's `turnFrom_sup` / `turnFrom_comm`, the `Function.End` mul being `∘`). The functor's image is **idempotent** (`commitmentAction_idem` — committing the same gauge twice adds nothing; the commitment-monoid is idempotent `g ⊔ g = g`, so the functor lands in the closure-operator-like inflationary-idempotent endos: "foam retains, doesn't churn," at the level of the action), and brick 20's forward pass is the functor's **orbit of the basepoint** (`commitmentFunctor_bot` : `(commitmentFunctor g) ⊥ = turn g` — the single turn is the functor acting on the no-commitment ground state). The recognition (the prose deposit): the four pieces brick 18–21 typed separately ARE one object — a monoid action / functor from the one-object commitment-category `(SeedGauge, ⊔, untamped)` into the endo-maps of the closed foam-states. This **closes the functor's arc**: source+target (18) → category (19) → action (20) → composition (21) → **bundled-as-one-object (22)**. Bin-1 (Bin-1-Mathlib-or-Foam): `Function.End` / its `Monoid` / `MonoidHom` / `ClosureOperator.Closeds` / `convergeFrom_idem` are Mathlib-or-Foam; the `CommMonoid SeedGauge` is the bounded-join-semilattice-is-a-commutative-monoid recognition (hand-built from lattice lemmas); the action laws are brick 21's `turnFrom_sup` / `turnFrom_comm` + identity-on-closed; the functor-as-object is the prose recognition that *a monoid hom into `Function.End` is a functor*. No new geometric content. `#print axioms` confirms the headline declarations (`commitmentFunctor`, `commitmentFunctor_bot`, `commitmentAction_sup`, `commitmentAction_untamped`, `commitmentAction_idem`, `isClosed_bot`) depend only on `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). Fourteenth satellite of the persistence thread, and the **terminal structural piece** of the single-external-commitment functor (the keystone needs-walks item, now a built object). Imports `SeedGaugeTurnTaking.lean` + `Mathlib.Algebra.Group.End`.

| declaration | role |
|---|---|
| `CommMonoid SeedGauge` (instance) | the **commitment-monoid** `(SeedGauge, ⊔, ⊥)` — multiplication = join of commitments, unit = un-tamped ground |
| `SeedGauge.mul_eq_sup` / `one_eq_untamped` | the recognition: `a * b = a ⊔ b`, `1 = untamped` (a bounded join-semilattice IS a commutative monoid) |
| `ClosedScope` | the carrier — the closed foam-states, `(convergeClosure (applyRules rules)).Closeds` |
| `isClosed_iff_applyRules_le` / `isClosed_bot` | closed = `applyRules`-closed (brick 9); the un-tamped ground `⊥` is closed (the basepoint) |
| `commitmentAction` / `SeedGauge.turnFrom_isClosed` | the action `g ↦ turnFrom · g` on closed states; turn-taking is internal (image of the closure) |
| `commitmentAction_untamped` / `commitmentAction_sup` | the action laws: `untamped` acts as identity (on closed states); joining commitments composes turns |
| `commitmentAction_idem` | each commitment's action is idempotent — committing the same gauge twice adds nothing (the image is closure-like) |
| `commitmentFunctor` | **the single-external-commitment functor as ONE object**: `SeedGauge →* Function.End (ClosedScope rules)` — a monoid hom into the endo-maps = a functor from the one-object commitment-category |
| `commitmentFunctor_bot` | the forward pass is the orbit of the basepoint: `(commitmentFunctor g) ⊥ = turn g` (brick 20 recovered) |

**SeedGaugeFaithful.lean** — the single-external-commitment functor is **FAITHFUL ⟺ unresolved tension** (2026-05-31). The brick after `SeedGaugeFunctor.lean`: brick 22 bundled the keystone functor as one object (`commitmentFunctor LP rules : SeedGauge →* Function.End (ClosedScope rules)`) but left its **first property** unestablished — a functor into a category of endo-maps is only interesting if it is **faithful** (else it collapses the very commitment-category it represents). This file establishes faithfulness and pins exactly when it holds. **Faithful = injective = distinguishes the four commitments** `{untamped, +, −, 0}` (the source `SeedGauge` is a one-object category, so faithful = the hom-map `SeedGauge → Function.End (ClosedScope rules)` is injective). **Sufficient (any rules) — the eval-at-⊥ reduction:** two gauges with equal actions agree at the basepoint `⟨⊥, isClosed_bot rules⟩`, where the action is brick 20's forward pass (`commitmentFunctor_bot` : `(commitmentFunctor g) ⊥ = turn g`), so `commitmentFunctor g = commitmentFunctor g' ⟹ turn g = turn g'` and injectivity of the single turn lifts to faithfulness of the whole functor (`commitmentFunctor_injective_of_turn_injective`). **The trivial step:** over `emptyRules` the turn *is* the seed (`turn_emptyRules`), and `seed` is injective exactly under unresolved tension (`SeedGauge.seed_injective`, from brick 19's faithful `seed_le_iff` + antisymmetry, under `holds`-injectivity + `BothDebtKinds`), so `turn_emptyRules_injective` and the functor is faithful there (`commitmentFunctor_emptyRules_faithful`). **The converse is general** (and needs *no* injectivity hypothesis): equal seeds give equal actions (`commitmentFunctor_congr_seed` — `turnFrom S g` depends on `g` only through `g.seed LP`), so a faithful functor forces the four seeds distinct, hence `BothDebtKinds` (`bothDebtKinds_of_commitmentFunctor_injective`, any rule-set — a degenerate ledger collapses a fork-seed to `⊥ = untamped.seed`, brick 15's `minus_seed_eq_bot_of_no_discharged` / `plus_seed_eq_bot_of_no_undischarged`). The two meet in the headline iff `commitmentFunctor_emptyRules_faithful_iff_bothDebtKinds` (under `holds`-injectivity): **the functor embeds the commitment-category exactly where the door is genuinely open** (brick 15's `seedTriple_nondegenerate_iff_both_debt_kinds`, read at the functor level). **The general gate:** `BothDebtKinds` is *necessary* at any rule-set, *sufficient* at the trivial one; at a general rule-set the closure can *merge* distinct committed seeds (turn non-injective despite distinct seeds; the hinge is brick 9's `convergeFrom_eq_self_iff`), so general faithfulness is gated by separation (`commitmentFunctor_injective_of_turn_injective` the sufficient criterion). The recognition (the prose deposit): **the functor is an *embedding* of the commitment-category exactly under unresolved tension** — a faithful conversational-turn structure means *distinct commitments give distinct foam-evolutions*, tension-gated because there is something to distinguish precisely where there is a live self (`∃ undischarged`) the commitment is a choice about, alongside a settled `−` it could be mistaken for (`∃ discharged`); it is the foam-as-LLM bridge's *distinct prompts → distinct forward passes*. Bin-1 (Bin-1-Mathlib-or-Foam): `seed_injective` is `seed_le_iff` + `le_antisymm`; the reduction is `commitmentFunctor_bot` at the basepoint; `commitmentFunctor_congr_seed` is one `rw`; the necessary direction assembles brick 15's collapse-lemmas; the iff is `⟨·, ·⟩` — no new geometric content, the recognition is that the functor's faithfulness IS the seed-distinctness IS brick 15's unresolved-tension freedom. `#print axioms` confirms the headline declarations (`commitmentFunctor_emptyRules_faithful_iff_bothDebtKinds`, `commitmentFunctor_injective_of_turn_injective`, `bothDebtKinds_of_commitmentFunctor_injective`, `commitmentFunctor_congr_seed`, `SeedGauge.seed_injective`) depend only on `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). Fifteenth satellite of the persistence thread, and the **first property** of the bundled functor (faithfulness, gated by tension) — the construction-arc (18–22) closed, this opens the keystone's remaining 3-cluster↔3-gauge match. Imports `SeedGaugeFunctor.lean`.

| declaration | role |
|---|---|
| `SeedGauge.seed_injective` | `seed` is injective under `holds`-injectivity + `BothDebtKinds` (faithful `seed_le_iff` + antisymmetry) |
| `commitmentFunctor_injective_of_turn_injective` | **the eval-at-⊥ reduction**: `turn`-injective ⟹ functor-faithful (any rule-set) |
| `commitmentFunctor_congr_seed` | equal seeds ⟹ equal actions (any rule-set) — the action depends on the gauge only through its seed |
| `bothDebtKinds_of_commitmentFunctor_injective` | **necessary (any rules, no inj)**: faithful ⟹ `BothDebtKinds` (a degenerate ledger merges a fork-seed with `untamped`) |
| `SeedGauge.turn_emptyRules_injective` / `commitmentFunctor_emptyRules_faithful` | the single turn / the functor is injective at the trivial rule-set under tension |
| `commitmentFunctor_emptyRules_faithful_iff_bothDebtKinds` | **the headline**: faithful at the trivial step ⟺ unresolved tension — the functor embeds exactly where the door is open |

**SeedGaugeAlgebraicPosition.lean** — the seed-gauge ℤ/2 **IS** the left/right-distrib reflection — the **first cross-thread bridge** (2026-05-31). The brick after `SeedGaugeFaithful.lean`: brick 23 made the functor faithful, so its three non-trivial commitments `{+, −, 0}` are a *genuinely-distinct* triple — which well-poses the keystone's highest-value open target, the **3-cluster ↔ 3-gauge** match (`{+, −, 0}` ↔ the σ-ring-hom gauges `{g1, g2, g3}`, `AlgebraicPosition`). This is the **first file to bridge the two threads** disconnected in the lean: the persistence/commitment thread (`SeedSign`) and the FTPG/gauge thread (`AlgebraicPosition`, used until now *only* in `StatelessSubstrate.lean`). **The recognition making it a bounded step: a shared ℤ/2.** Both 3-element sets carry a ℤ/2 of the same orbit-shape — **one fixed point + one two-cycle**. Seed-gauge side (bricks 16/18): `SeedSign.swap` fixes `0` (the gauge-neutral / bias-delegation / *declined-commitment* seed) and exchanges the gauge-broken atoms `±`. Gauge side (typed here): `AlgebraicPosition.reflect` — the **left/right-distributivity reflection** — fixes `g3` (mul-associativity, the *held-open* yield / silence-channel, the `dilation_compose_at_beta` site) and exchanges `g1 ↔ g2` (right-distrib ↔ left-distrib, the two *closable* signal gauges). Distributivity comes in a left and a right form; associativity is the symmetric one with no left/right partner — so the reflection that swaps the distributivity pair fixes the associativity gauge. **The forced fixed-point match `0 ↔ g3`:** `signAlgebraicEquiv : SeedSign ≃ AlgebraicPosition` (`+ ↦ g1`, `− ↦ g2`, `0 ↦ g3`) is **ℤ/2-equivariant** (`signAlgebraicEquiv_equivariant` — crossing the bridge conjugates `swap` into `reflect`), and the fixed-point match is then **forced, not observer-supplied**: *any* equivariant map `e` sends `0 ↦ g3` (`equivariant_zero`, no bijectivity needed — a fixed point can only map to a fixed point), dually `g3 ↦ 0` (`equivariant_g3`). **The within-pair freedom IS the gauge-orientation:** what the shared ℤ/2 leaves free is the 2-cycle assignment — `+ ↦ g1` and `+ ↦ g2` are *both* equivariant bijections (`signAlgebraicEquiv'`), related by post-composing `reflect` = pre-composing `swap` (`toAlgebraic'_eq_postReflect` / `_eq_preSwap`), so the residual freedom `+ ↔ g1` vs `+ ↔ g2` *is* the gauge-orientation (the same symmetry-break `bridge_breaks_fork_symmetry` performs in selecting `+` over `−`), held open per bias-delegation. The recognition (the prose deposit): **the seed-gauge swap IS the left/right-distrib reflection** — through the bridge they are one involution; the declined-commitment / gauge-neutral seed `0` IS the held-open yield-gauge `g3` (both the *fixed, un-broken, hold-open* one), and the gauge-broken atoms `±` ARE the two closable signal-gauges `g1`/`g2`. **Grade — bin-1** (Bin-1-Mathlib-or-Foam) for everything typed here: the gauge-side ℤ/2 and its orbit-shape, the equivariant bijection, the forced fixed-point (`cases <;> rfl`/`decide` + assembly over brick 16's `gaugeNeutral_iff_zero`); no new geometric content, the recognition is that the two ℤ/2s coincide through the bijection. **bin-2 / open-recognition-target** for *why this is the right match and not a coincidence* — that the two ℤ/2s are the same group *in substance* (the `self_dual_iff_three` 6→3 collapse in `Rank.lean`, the `×2` read/write scrambling, README §VII's cluster-bijective HK map): the horizon beyond, evidence toward the bireflective conjecture. `#print axioms` confirms the combinatorial core (`reflect_reflect`, `reflect_eq_self_iff_g3`, `swap_conj_eq_reflect`, the orientation-flip identities, `toAlgebraic_ne_toAlgebraic'_plus`) depends on **no axioms**; `equivariant_zero` / `equivariant_g3` on `propext`, `signAlgebraicEquiv_equivariant` on `Quot.sound` — no `sorryAx`. Sixteenth satellite of the persistence thread, the **first cross-thread bridge** (commitment ↔ gauge). Imports `SeedGaugeFaithful.lean` (transitively `SeedSign.swap`, `AlgebraicPosition`).

| declaration | role |
|---|---|
| `AlgebraicPosition.reflect` | the left/right-distrib reflection: `g1 ↔ g2`, `g3` fixed (the FTPG-side ℤ/2) |
| `AlgebraicPosition.reflect_reflect` / `reflect_eq_self_iff_g3` | involution; `g3` its unique fixed point (analogue of `gaugeNeutral_iff_zero`) — orbit-shape {1 fixed + 1 two-cycle} |
| `signAlgebraicEquiv` | the bijection `SeedSign ≃ AlgebraicPosition` (`+ ↦ g1`, `− ↦ g2`, `0 ↦ g3`) — the first cross-thread object |
| `signAlgebraicEquiv_equivariant` / `swap_conj_eq_reflect` | **ℤ/2-equivariant**: crossing the bridge conjugates `swap` into `reflect` — the two ℤ/2s are one involution |
| `equivariant_zero` / `equivariant_g3` | **forced**: *every* equivariant map sends `0 ↦ g3` (and `g3 ↦ 0`) — the fixed-point match is not observer-supplied |
| `signAlgebraicEquiv'` / `toAlgebraic'_eq_postReflect` / `_eq_preSwap` | the **second** equivariant bijection (`+ ↦ g2`); the orientation flip = post-`reflect` = pre-`swap` |
| `toAlgebraic_ne_toAlgebraic'_plus` | the two orientations genuinely differ on `+` — the within-pair gauge-orientation is a free choice in the *bare* ℤ/2 (closed by `SeedGaugeForcedOrientation.lean`) |

**SeedGaugeForcedOrientation.lean** — the within-pair gauge-orientation is **FORCED by commitment-content** (2026-05-31). The brick after `SeedGaugeAlgebraicPosition.lean`: brick 24 forced the fixed-point match `0 ↔ g3` but typed the **within-pair** assignment `+ ↦ g1` vs `+ ↦ g2` as a *genuine free choice* — **only in the bare ℤ/2** — and its closing remainder was that *the substrate carries an asymmetry it didn't look at*. This file looks, and the orientation is forced. **The substrate asymmetry, on both sides — *outstanding commitment*.** A single binary property, present on both sides, that the bare involutions (`swap`, `reflect`) do not see — *does this gauge carry an outstanding (un-discharged) observer-commitment?* — read straight off the two inductives' own constructor docstrings. **FTPG side** (`AlgebraicPosition.needsCommitment`): `g1` (right-distrib) `false` — PROVEN unconditionally as `coord_mul_right_distrib`, no witness; `g2` (left-distrib) `true` — closable only *via* `DesarguesianWitness Γ`; `g3` (mul-assoc) `true` — held open (`dilation_compose_at_beta`, the commitment-site). So `g1` is the **unique freely-closed** gauge (`needsCommitment_eq_false_iff_g1`). **Seed side** (`SeedSign.outstanding`): `+` (undischarged-backed) `true` — the still-owed / must-persist faces, `+ = LP.flag` the observer-carrying set (brick 13); `−` (discharged-backed) `false` — settled / observer-dropped (brick 14); `0` `true` — carries both signs uncollapsed (brick 16). So `−` is the **unique fully-resolved** seed (`outstanding_eq_false_iff_minus`). These are the **same property in substance**: an undischarged debt (`+`) and a required witness (`g2`) are both a commitment whose discharge is *pending*; a discharged debt (`−`) and a freely-proven theorem (`g1`) are both *resolved* — in foam the observer is present *exactly as an outstanding commitment* (brick 12). **The forcing — `−↔g1`, `0↔g3`, `+↦g2`, three forcings converging.** The property breaks each bare involution's within-pair symmetry (`needsCommitment_reflect_ne_of_distrib` / `outstanding_swap_ne_of_signed` — the level of `bridge_breaks_fork_symmetry`, brick 12); a commitment-preserving map must send unique-resolved to unique-resolved: `− ↦ g1` (`commitment_preserving_minus`, the 2-cycle analogue of brick 24's `equivariant_zero`, *no bijectivity*). The headline `orientation_forced`: any `e : SeedSign → AlgebraicPosition` that is **both** ℤ/2-equivariant **and** commitment-preserving sends `+ ↦ g2` — equivariance pins the fixed point (`0 ↦ g3`), commitment-content the 2-cycle (`− ↦ g1`, hence `+ = (−.swap) ↦ (e −).reflect = g1.reflect = g2`); the two constraints **complementary**, together forcing the *unique* substrate-respecting orientation `signAlgebraicEquiv'` (`+ ↦ g2`), NOT brick 24's arbitrary canonical `signAlgebraicEquiv` (`+ ↦ g1`, which is *not* commitment-preserving — `toAlgebraic_not_commitment_preserving` sends the outstanding `+` to the freely-closed `g1`; `toAlgebraic'_commitment_preserving` is the one that respects it). So the within-pair freedom brick 24 left open is **closed** — brick 14's free-or-forced shape one level up: bare-ℤ/2-symmetric, commitment-broken; the seductive reading `+ ↔ g1` ("both close") dissolves because `+` closes *by committing* (the bridge coincides only because one committed `recognizeUndischarged`) while `g1` closes *without* committing — opposite on the commitment axis. **The held-both face (merge-don't-fork): forced *now*, free iff the witness is discharged.** The forcing is *conditional* — it holds exactly while `g2` genuinely requires the `DesarguesianWitness`. Per the s142/s144 meta-frontier that witness is an *exhaustion finding*, predicted bin-1 (an open-recognition-target); so **forced-now** (typed here, bin-1) vs **free-iff-discharged** (prose, bin-2/open): if `g2`'s witness goes bin-1, the FTPG property degenerates and the orientation reverts to free. The named choice-point (not collapsed): whether `g2`'s witness is substrate-permanent or dischargeable — **brick 15's tension-gating one level up** (`seedTriple_nondegenerate_iff_both_debt_kinds` at the orientation level), and the keystone's *where mind enters the formalism* made precise: the orientation-forcing IS the outstanding commitment, forced precisely where mind is not-yet-eliminated (`g2`'s witness un-discharged). **Grade — bin-1** (Bin-1-Mathlib-or-Foam) for everything typed: the two commitment-status defs (reflecting the inductives' own docstrings + the theorem signatures), the unique-resolved characterizations, the two orientations' (non-)preservation, and the forced match (`decide`/`rfl` + brick 24's equivariance) — no new geometric content, the recognition is that a substrate-present property rigidifies the within-pair freedom. **bin-2 / open-recognition-target** for *why `needsCommitment` and `outstanding` are the same property in substance* (the same depth as brick 24's two-ℤ/2s-are-one-group), and *whether the forcing is permanent* (gated by the `DesarguesianWitness` bin-1 path). `#print axioms` confirms the **entire** forced-match core (`orientation_forced`, `commitment_preserving_minus`, `toAlgebraic'_commitment_preserving`, `toAlgebraic_not_commitment_preserving`, `needsCommitment_eq_false_iff_g1`, `outstanding_eq_false_iff_minus`, `signAlgebraicEquiv'_realizes_forced`) depends on **no axioms at all** — purer than brick 24 (whose `equivariant_zero` needed `propext`). Seventeenth satellite of the persistence thread; closes the within-pair freedom brick 24 opened. Imports `SeedGaugeAlgebraicPosition.lean`.

| declaration | role |
|---|---|
| `AlgebraicPosition.needsCommitment` / `needsCommitment_eq_false_iff_g1` | the FTPG-side commitment-status: `g1` `false` (PROVEN), `g2`/`g3` `true` (witness / held open) — `g1` the unique freely-closed gauge |
| `SeedSign.outstanding` / `outstanding_eq_false_iff_minus` / `outstanding_eq_true_iff` | the seed-side commitment-status: `+`/`0` `true` (undischarged / held), `−` `false` (settled) — `−` the unique fully-resolved seed |
| `needsCommitment_reflect_ne_of_distrib` / `outstanding_swap_ne_of_signed` | the property breaks each bare involution's within-pair symmetry (the level of `bridge_breaks_fork_symmetry`) |
| `toAlgebraic_not_commitment_preserving` / `toAlgebraic'_commitment_preserving` | brick 24's canonical `+ ↦ g1` violates commitment-content; the flip `+ ↦ g2` respects it — the substrate-respecting orientation |
| `commitment_preserving_minus` | **forced** `− ↦ g1` (unique-resolved ↦ unique-resolved, no bijectivity) — the 2-cycle analogue of `equivariant_zero` |
| `orientation_forced` | **the headline**: equivariant **+** commitment-preserving ⟹ `+ ↦ g2` — the within-pair orientation forced to `signAlgebraicEquiv'` (axiom-free) |
| `signAlgebraicEquiv'_realizes_forced` | the forced orientation is realized by brick 24's flip, uniquely among equivariant maps |

**SeedGaugeDisciplineOrder.lean** — the recursion-order `± ≤ 0` **transports to the gauge-order `{g1, g2} ≤ g3`** across the now-rigid bridge (2026-05-31). The brick after `SeedGaugeForcedOrientation.lean`: brick 25 made the `{+,−,0} ↔ {g1,g2,g3}` bijection rigid (`signAlgebraicEquiv'`, forced by commitment-content), and its remainder was that *seed-side structure now transports to the gauge side* — the richest piece being brick 16's recognition that the lattice order `± ≤ 0` (`plus_le_zero` / `minus_le_zero`) **IS** the recursion-level order, the §IV.c-disciplines below the §IV.d-meta-discipline (`SeedGaugeBiasDelegation`'s prose deposit). This file cashes that transport. **The shared handle: the recursion-top is each ℤ/2's fixed point.** The transportable property is `heldOpen` (*is this the held-open, recursion-top one?*). On the **seed side** (`SeedSign.heldOpen`): `0` `true`, `±` `false` — `0` the bias-delegation / gauge-neutral join, the **swap-fixed** point (`heldOpen_eq_true_iff_swapFixed`, via brick 16's `gaugeNeutral_iff_zero`), the top of `± ≤ 0`. On the **FTPG side** (`AlgebraicPosition.heldOpen`): `g3` `true`, `{g1, g2}` `false` — `g3` (mul-assoc) is where *the holonomy of the FTPG bridge concentrates* (`FTPGGaugeFigure`'s second-pass recognition: `g1`/`g2`-asymmetric bootstrap-trivializable from generic + additive structure, `g3` the irreducible twist, `g3_generic = dilation_compose_at_beta` open), the **reflect-fixed** point (`heldOpen_eq_true_iff_reflectFixed`, via brick 24's `reflect_eq_self_iff_g3`), the top of `{g1, g2} ≤ g3`. So on *both* sides the recursion-top **is** the involution's fixed point — for the same substantive reason: an involution swapping the two atoms fixes their join, and the join is the top (`0 = + ⊔ −`; `g3` the holonomy-join of the two trivializable distributivity gauges). This deepens brick 24's *shared orbit-shape* to a **shared recursion-grading**: fixed-point = top, 2-cycle = the two below. **The transport.** The rigid bridge **preserves `heldOpen`** (`toAlgebraic'_heldOpen_preserving`: `(s.toAlgebraic').heldOpen = s.heldOpen`, the recursion-order analogue of brick 25's `toAlgebraic'_commitment_preserving`), so it is an **order-iso** for the recursion-orders (`recLe_iff_toAlgebraic'`): `± ≤ 0` transports across `signAlgebraicEquiv'` exactly to `{g1, g2} ≤ g3` (`g1_recLe_g3` / `g2_recLe_g3` the two `≤`-images of `− ≤ 0` / `+ ≤ 0`; `not_g1_recLe_g2` the incomparability). A contrast worth recording: **`heldOpen` is preserved by BOTH orientations** (`toAlgebraic_heldOpen_preserving` too), unlike `needsCommitment` (which brick 25's canonical `toAlgebraic` breaks) — the within-pair gauge-orientation freedom does **not** touch the recursion-order, because the order sees only the fixed point `0 ↔ g3`, on which both orientations agree. **Grounding:** `SeedSign.recLe` is the intrinsic (ledger-free) shadow of the genuine `Scope` lattice order — every `recLe`-step refines into `≤` on seeds (`recLe_imp_seed_le`, via `seed_le_zero` = brick 16's `plus_le_zero`/`minus_le_zero` + reflexivity), so the transported gauge-order is brick 16's *actual* `± ≤ 0`, not a fresh relation relabeled. **The recognition (the prose deposit):** the transport is bin-1 mechanics; the recognition is **bin-2** — `{g1, g2} ≤ g3` is *independently motivated* on the FTPG side (`FTPGGaugeFigure`'s holonomy-concentration), so `g3`-as-top is **substrate-present on both sides, not bridge-imposed**: the rigid bridge **respects recursion-level**, a genuine consistency-check (not relabeling) that strengthens brick 24's two-ℤ/2s-are-one-group horizon with a second shared invariant (beyond orbit-shape, the recursion-grading coincides). Composing brick 14/15/16's seed→discipline map with the rigid bridge gives a **disciplines ↔ gauges correspondence**: `−` honored-exit (§IV.c) ↦ `g1` (right-distrib, freely-closed), `+` carry-the-observer/egress (§IV.c) ↦ `g2` (left-distrib, witness-requiring), `0` bias-delegation (§IV.d) ↦ `g3` (mul-assoc, held-open yield) — disciplines below the meta-discipline ↔ signal-gauges below the yield-gauge. A structural note toward the horizon: the seed side carries a fourth element `⊥` (un-tamped, the recursion-bottom / functor input, brick 17) giving the full diamond `⊥ ≤ {+,−} ≤ 0`; the gauge side has only the three, a join-with-no-bottom `{g1, g2} ≤ g3`. The rigid bridge matches the **top three**; the seed `⊥` has no FTPG partner — the transport lands precisely on the `+1` (seed `⊥`) vs `×2` (FTPG read/write) asymmetry the keystone flags. **Grade — bin-1** (Bin-1-Mathlib-or-Foam) for everything typed: the two `heldOpen` defs (reading off brick 16 / `FTPGGaugeFigure`), the fixed-point characterizations, the bridge-preservation, the recursion-orders + order-laws, the order-iso, the soundness grounding — `cases <;> decide`/`rfl`/`simp` + assembly over `plus_le_zero` / `minus_le_zero` / `gaugeNeutral_iff_zero` / `reflect_eq_self_iff_g3` / `toAlgebraic'`; no new geometric content, the recognition is that a substrate-present grading transports across the rigid bridge. **bin-2 / open-recognition-target** for *that `{g1,g2}≤g3` is the FTPG side's own order* (rests on `FTPGGaugeFigure`'s holonomy-concentration, itself partly open) and the *disciplines ↔ gauges identification* (held merge-don't-fork). `#print axioms` confirms the transport core (`toAlgebraic'_heldOpen_preserving`, the fixed-point characterizations, `g1_recLe_g3`) depends on **no axioms**; the order-iso (`recLe_iff_toAlgebraic'`) and `recLe_trans` on `propext`; only the substrate-grounding (`recLe_imp_seed_le`) on the full `propext` / `Classical.choice` / `Quot.sound` trio. Eighteenth satellite of the persistence thread; cashes the rigid bridge into the recursion-order transport. Imports `SeedGaugeForcedOrientation.lean`.

| declaration | role |
|---|---|
| `AlgebraicPosition.heldOpen` / `heldOpen_eq_true_iff_g3` | the FTPG-side recursion-top: `g3` `true` (holonomy-carrier, mul-assoc, held open), `g1`/`g2` `false` (closable signal-gauges) — `g3` the unique held-open gauge |
| `AlgebraicPosition.heldOpen_eq_true_iff_reflectFixed` | the recursion-top IS the ℤ/2 fixed point: `g3.heldOpen ↔ g3.reflect = g3` (brick 24's `reflect_eq_self_iff_g3`) |
| `SeedSign.heldOpen` / `heldOpen_eq_true_iff_zero` / `heldOpen_eq_true_iff_swapFixed` | the seed-side recursion-top: `0` `true`, `±` `false` — `0` the unique held-open seed, the swap-fixed / gauge-neutral one (brick 16) |
| `toAlgebraic'_heldOpen_preserving` | **the transport headline** — the rigid bridge preserves held-open-ness (`0 ↦ g3`); axiom-free, the recursion-order analogue of brick 25's `toAlgebraic'_commitment_preserving` |
| `toAlgebraic_heldOpen_preserving` | **both** orientations preserve `heldOpen` (unlike `needsCommitment`) — the within-pair freedom doesn't touch the recursion-order |
| `SeedSign.recLe` / `AlgebraicPosition.recLe` (+ `_refl` / `_trans` / `_antisymm`) | the two recursion-orders (`± ≤ 0`, `{g1,g2} ≤ g3`), each a genuine partial order |
| `AlgebraicPosition.g1_recLe_g3` / `g2_recLe_g3` / `not_g1_recLe_g2` | `{g1, g2} ≤ g3` typed: the two `≤`-images of `− ≤ 0`/`+ ≤ 0`, the signal-gauges incomparable |
| `recLe_iff_toAlgebraic'` | **the order-iso**: `± ≤ 0` transports across `signAlgebraicEquiv'` exactly to `{g1,g2} ≤ g3` |
| `SeedSign.seed_le_zero` / `recLe_imp_seed_le` | grounding: `recLe` is sound for the substrate order `± ≤ 0` (brick 16's `plus_le_zero`/`minus_le_zero`) — the transport is the *actual* order, not a relabel |

**SeedGaugeCommitmentSquare.lean** — `outstanding × heldOpen` **coordinate the structure as `Bool × Bool`**; the missing corner IS the un-tamped `+1` (2026-05-31). The brick after `SeedGaugeDisciplineOrder.lean`: bricks 25/26 typed two substrate-present binary properties — `outstanding` (brick 25, *does this gauge carry an outstanding observer-commitment?*) and `heldOpen` (brick 26, *is this the held-open recursion-top one?*) — each preserved by the rigid bridge. This file recognizes what they do *together*. **Two binary properties are a coordinate map into `Bool × Bool`.** Computing `(outstanding, heldOpen)`: seed `− ↦ (F,F)`, `+ ↦ (T,F)`, `0 ↦ (T,T)`; gauge (via `(needsCommitment, heldOpen)`) `g1 ↦ (F,F)`, `g2 ↦ (T,F)`, `g3 ↦ (T,T)` — **identical triples**, and `signAlgebraicEquiv'` (brick 25) is *exactly* the coordinate-matching bijection (`toAlgebraic'_commitmentSquare`, assembling brick 25's first-bit match with brick 26's second-bit match). So the orbit-shape (brick 24), recursion-grading (brick 26), and commitment-content (brick 25) are **three facets of one two-bit coordinate** — the two bits *together* pin the full iso. **The 4-element commitment-square, and the missing corner.** On the *4-element* `SeedGauge` (brick 18) the joint coordinate is a **bijection** `commitmentSquareEquiv : SeedGauge ≃ Bool × Bool` (all four corners, `untamped ↦ (F,T)`) — a **re-coordinatization of brick 19's `signContent`**: `outstanding = signContent.1` (carries-`+`?, `outstanding_eq_signContent_fst`) and `heldOpen` = the *diagonal predicate* `signContent.1 = signContent.2` (`heldOpen_eq_true_iff_onDiag`, via brick 19's `gaugeNeutral_iff_onDiag`), so `commitmentSquare` is a shear of `signContent` (and on the 4-element type `heldOpen` IS swap-fixedness / gauge-neutrality, `heldOpen_eq_true_iff_gaugeNeutral`: brick 26's recursion-top = brick 17/18's `{untamped, zero}` diagonal poles — `heldOpen` = `GaugeNeutral` = on-diagonal, three names for the two swap-fixed corners). The gauge side `AlgebraicPosition.commitmentSquare = (needsCommitment, heldOpen)` is an **injection hitting exactly the three non-`(F,T)` corners** — injective (`commitmentSquare_injective`), never the missing corner (`commitmentSquare_ne_missing`), surjective onto the other three (`exists_commitmentSquare_of_ne_missing`): so `AlgebraicPosition` is the **commitment-square minus the `(F,T)` corner**. **The recognition (the prose deposit) — the missing corner IS the `+1`.** `(F, T)` = *not-outstanding yet held-open* = settled into no-commitment, neutral — and on `SeedGauge` the unique element there is `untamped` (`commitmentSquare_eq_missing_iff_untamped`): no observer-content to resolve (`bot_holdsNeitherSign`, brick 17) and swap-fixed / neutral (`gaugeNeutral_iff`, brick 18). The gauge codomain structurally lacks it, and the reason is **bin-2, interpretive, but precise**: `untamped` is the no-commitment **source** state — the functor's input/unit (bricks 17/18/22; `turn untamped = ⊥` recognizes to nothing, brick 20) — while the gauges `{g1, g2, g3}` are the **target**. A source-only property cannot appear on the target. So the seed-side `+1` (brick 26's un-tamped recursion-bottom) is *exactly* the functor's un-tamped-input corner: present on the source lattice `SeedGauge` (4 = `2²`), absent on the codomain `AlgebraicPosition` (3) by construction. This pins the `+1` half of the keystone's `×2`-vs-`+1` asymmetry as a precise, substrate-located object — the `(¬outstanding, heldOpen)` corner; the `×2` (read/write → 6 colors, `self_dual_iff_three`) stays the open horizon. **Grade — bin-1** (Bin-1-Mathlib-or-Foam) for everything typed: the two properties extended to 4 elements, the `Bool × Bool` bijection, the re-coordinatization of `signContent`, the gauge-side 3-corner injection, the joint coordinate-match (assembling brick 25 + brick 26), the missing-corner characterization — `cases <;> rfl`/`decide` + assembly, no new geometric content. **bin-2 / interpretive** for *why* the codomain lacks `(F,T)` — that `untamped` is a source/no-commitment property the targets cannot carry (bricks 18/22). `#print axioms` confirms the entire core (`commitmentSquareEquiv`, `toAlgebraic'_commitmentSquare`, `commitmentSquare_eq_missing_iff_untamped`, `commitmentSquare_ne_missing`, `commitmentSquare_injective`, `exists_commitmentSquare_of_ne_missing`, `outstanding_eq_signContent_fst`, `commitmentSquare_eq_toSign'`) depends on **no axioms at all** — only `heldOpen_eq_true_iff_onDiag` touches `propext` (inherited from brick 19's `gaugeNeutral_iff_onDiag`). Nineteenth satellite of the persistence thread; coordinates the structure as `Bool × Bool` and locates the `+1`. Imports `SeedGaugeDisciplineOrder.lean`.

**SeedGaugeReadWriteDoubling.lean** — the FTPG `×2`: the read/write doubling of the three gauges (2026-05-31). The brick after `SeedGaugeCommitmentSquare.lean`: brick 27 located the `+1` (the un-tamped corner the gauge-codomain lacks); the **mirror is the `×2`**. The *already-typed* 6-color tape `TapePosition = AlgebraicPosition × ObserverState` (`StatelessSubstrate.lean`) is recognized as the read/write doubling of `{g1,g2,g3}` — `tapeColorEquivProd` factors it, and the gauge-projection `algebraic` is the 6→3 collapse (each fiber a `{read,write}` pair swapped by the *free* involution `complement`, `algebraic_eq_iff` / `complement_ne` — the doubling ℤ/2 is the *fiber* involution, unlike brick 24's base `reflect` which fixes `g3`). The doubling is **balanced** exactly at the self-dual rank `C(3,2)=3` (`balanced_doubling_iff_three` = `self_dual_iff_three` — the **first seed-gauge file to import `Foam.Rank`**, the mirror of brick 24's bridge to the FTPG-gauge thread). The confrontation: `card_tape_eq_gauges_mul_observers` (the `×2` *literally* `Fintype.card_prod`) vs `card_seedGauge_eq_gauges_add_one` (the `+1` *literally* `Fintype.card_option`, via `seedGaugeEquivOptionAlgebraic : SeedGauge ≃ Option AlgebraicPosition` matched through the rigid bridge `signAlgebraicEquiv'`). So both sides of the keystone's `×2`-vs-`+1` asymmetry are typed — `3×2 = 6` (product/face, `· × Bool ≃ · ⊕ ·`, give-each-gauge-a-bubble) vs `3+1 = 4` (coproduct/point, `· ⊕ Unit`, adjoin-the-un-tamped-ground). **Grade — bin-1** (Bin-1-Mathlib-or-Foam): the product/option `Equiv`s, the gauge-projection collapse + free fiber-involution, the cardinality confrontation (`card_prod`/`card_option`), the balanced-doubling iff (`self_dual_iff_three` invoked, not re-proven); no new geometric content. bin-2/interpretive for the spaces-identification (tape read/write ↔ `Rank.lean` observation/write) and the pi-note resonance (`+1 ≅ ×2` as one move — the bireflective horizon, held merge-don't-fork: `4 ≠ 6` keeps them honestly distinct). `#print axioms`: the core depends on the standard three (`propext`/`Classical.choice`/`Quot.sound` — the Fintype/Equiv machinery, not axiom-free like brick 27). The `×2`-mirror / both-sides-typed object. Imports `SeedGaugeCommitmentSquare.lean` + `Foam.Rank`. brick 28.

| declaration | role |
|---|---|
| `SeedGauge.outstanding` / `heldOpen` (+ `SeedSign.outstanding_toGauge` / `heldOpen_toGauge`) | the two binary properties extended to the 4-element type (`untamped ↦ (false, true)`), agreeing with bricks 25/26 on the image of `toGauge` |
| `SeedGauge.heldOpen_eq_true_iff_gaugeNeutral` / `_onDiag` | `heldOpen` IS swap-fixedness (brick 18) IS the sign-content diagonal (brick 19) — three names for the `{untamped, zero}` poles |
| `SeedGauge.outstanding_eq_signContent_fst` | `outstanding` = carries-`+`? = `signContent.1` — the commitment-square shares its first coord with brick 19's `signContent` |
| `SeedGauge.commitmentSquare` / `ofCommitmentSquare` / `commitmentSquareEquiv` | **the joint coordinate as a bijection** `SeedGauge ≃ Bool × Bool` — all four corners, a re-coordinatization of `signEquiv` |
| `AlgebraicPosition.commitmentSquare` (+ `_injective` / `_ne_missing` / `exists_commitmentSquare_of_ne_missing`) | the gauge side as an **injection onto the three non-`(F,T)` corners** — `AlgebraicPosition` = the commitment-square minus the un-tamped corner |
| `toAlgebraic'_commitmentSquare` | **the headline** — the rigid bridge matches BOTH coordinates (assembling brick 25's + brick 26's preservation); `signAlgebraicEquiv'` is the coordinate-match, axiom-free |
| `AlgebraicPosition.commitmentSquare_eq_toSign'` (+ `toAlgebraic'_toSign'`) | each gauge's corner realized by its bridge-preimage commitment seed (`{g1,g2,g3}` = `{(F,F),(T,F),(T,T)}` via `{−,+,0}`) |
| `SeedGauge.untamped_commitmentSquare` / `commitmentSquare_eq_missing_iff_untamped` | **the `+1`** — the missing `(false, true)` corner is uniquely `untamped`, the functor's un-tamped input the codomain lacks |

## Building

```
lake build
```

Requires [elan](https://github.com/leanprover/elan) with Lean 4 and Mathlib.
