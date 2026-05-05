# lean/ — notes for Claude

## Environments

Two environments to expect; the right setup is different for each.

### Local laptop (the common case)

`lake`, `lean`, `elan` are on PATH; `lake exe cache get` works and is the
right first move when Mathlib feels stale or hasn't been built yet (it
populates `.lake/packages/mathlib/.lake/build` from Azure cache, ~10s of
seconds vs. ~30 min of compilation). After that:

```bash
lake build Foam.FTPGInverse   # or whatever target you're touching
```

Single-file builds are fast (~5–10s) once Mathlib is cached. A full
`lake build` (the whole `Foam` library) compiles all 28 Foam files but
should reuse Mathlib oleans from cache; if it starts compiling Mathlib
files from scratch, run `lake exe cache get` and try again.

### Web sandbox

The sandbox blocks `release.lean-lang.org`, Mathlib's Reservoir, and
`lakecache.blob.core.windows.net`. `lake exe cache get` will **not** work.
GitHub is reachable.

If `lake`/`lean` is not on PATH, or `elan show` errors, set up the toolchain
manually:

```bash
# 1. Install elan (keeps its own PATH under ~/.elan/bin)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"

# 2. Install zstd for extracting the Lean tarball
apt-get install -y zstd

# 3. Pull the toolchain version from lean-toolchain directly from GitHub
#    (elan can't reach release.lean-lang.org, so we side-load)
VERSION=$(cut -d: -f2 < /home/user/foam/lean/lean-toolchain)  # e.g. v4.29.0
mkdir -p /tmp/lean-dl && cd /tmp/lean-dl
curl -sSL -o lean.tar.zst \
  "https://github.com/leanprover/lean4/releases/download/${VERSION}/lean-${VERSION#v}-linux.tar.zst"
mkdir -p /root/.elan/toolchains
cd /root/.elan/toolchains
tar --use-compress-program=unzstd -xf /tmp/lean-dl/lean.tar.zst
# Creates e.g. /root/.elan/toolchains/lean-4.29.0-linux/

# 4. Register as a linked toolchain and pin it for this project
elan toolchain link v4.29.0-manual /root/.elan/toolchains/lean-${VERSION#v}-linux
cd /home/user/foam/lean
elan override set v4.29.0-manual
lean --version  # sanity check
```

Note: `elan toolchain list` will also show the extracted directory (because
it's under `toolchains/`), but trying to use it directly errors with
"could not read symlink" — always reference the linked name
(`v4.29.0-manual`), not the directory.

## First build (sandbox only) takes ~30–40 minutes

In the sandbox, without cache access, all of Mathlib's transitive
dependencies compile from source on first `lake build`. Subsequent builds
are fast (only your edits rebuild).

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/user/foam/lean
lake build Foam.FTPGLeftDistrib   # or any other target under Foam.
```

On local, this isn't a concern — `lake exe cache get` handles it.

## Where the FTPG work is

See `./README.md` for the deductive chain overview.

### Current frontier (session 133, 2026-05-05)

**`Foam/FTPGMulAssoc.lean`** (~315 lines, single `sorry`) — s133
created the file with architecture in its header, then **PROVED
`dilation_determined_by_param`** (~150 lines) by factoring
`dilation_ext Γ a P` as a perspectivity from `l = O⊔U` to `O⊔P`
through center `d_P = (I⊔P)⊓m`, then `perspectivity_injective`.
Signature held against contact with the proof — no architectural
surprises. Six unused-but-API-parity hypotheses are underscored.

The remaining `sorry` is **`coord_mul_assoc`** itself (the
headline). The helper landing means the proposed proof
architecture (four `dilation_mul_key_identity` applications +
composition argument + the now-proven uniqueness lemma) has all
its named pieces; the assembly is the next-session work. The
witness-question (s132 device-shape) prediction (no fresh
`DesarguesianWitness` needed) remains untested by the helper
work — the assembly is where it gets answered.

`Foam/FTPGInverse.lean` (~1840 lines) lands `coord_inv`,
`coord_mul_right_inv` (`a · a⁻¹ = I`), the non-degeneracy helpers, the
**σ_{a⁻¹} = σ'_a** helper (`sigma_inv_eq_sigma_prime`) factored from
the right-inverse proof, **`coord_inv_I_eq_I`** (`I` is its own
multiplicative inverse), and as of session 128 the entire
`coord_first_desargues_mul` body. The construction is reverse
perspectivity through `I ⊔ d_a`:

```
d_a = (a⊔C) ⊓ m
σ' = (O⊔C) ⊓ (I⊔d_a)
a⁻¹ = (σ'⊔E_I) ⊓ l
```

`coord_mul_left_inv`'s generic case now has a **single open sorry** —
`axis_to_sigma_a_le`, the bridge from the first-Desargues axis output
to `σ_a ≤ I⊔d_{a⁻¹}`. Session 132's design exploration found that any
clean forward-Desargues design for this lemma reduces to a center
hypothesis equivalent to the lemma itself (see the docstring on
`axis_to_sigma_a_le` in FTPGInverse.lean — designs D1–D11 walked).
**Strategic recommendation: skip this lemma; pivot to
`coord_mul_assoc` and derive `coord_mul_left_inv` algebraically.**
Standard Mac Lane argument (assoc + right ID + right inverse ⇒ group)
gives left inverse in ~20 lines once assoc is proven, with no
additional Desargues calls or `*Witness` interfaces.

#### Architectural split (session 125; status as of s132)

The single sorry at `sigma_a_le_I_sup_d_inv_distinct` was refactored
into two named sub-lemmas with full statements + trivial composition:

* **`coord_first_desargues_mul`** — single `desargues_planar` call,
  center `C`, triangles `T₁=(a, a⁻¹, σ_a)` / `T₂=(d_a, d_{a⁻¹}, σ')`.
  Output: axis collinearity `X₂₃ ≤ U ⊔ X₁₃` where
  `X₁₃ = (a⊔E_I) ⊓ (I⊔d_a)`. **PROVEN** as of session 128
  (~570 lines).
* **`axis_to_sigma_a_le`** — bridge from `X₂₃ ≤ U ⊔ X₁₃` to
  `σ_a ≤ I ⊔ d_{a⁻¹}`. **Open sorry**, but **deprioritized in s132**:
  see the lemma's docstring for design history (sessions 131–132)
  and the strategic recommendation to derive `coord_mul_left_inv`
  algebraically from `coord_mul_assoc` instead.

`sigma_a_le_I_sup_d_inv_distinct` is a one-line composition:
`axis_to_sigma_a_le (...) (coord_first_desargues_mul (...))`. If the
algebraic-derivation path is taken, this composition becomes unused
infrastructure.

#### Distinctness audit (sessions 124–126, all PROVEN as private helpers)

| helper | role |
|---|---|
| `d_a_ne_d_inv` | X₁₂ distinctness; uses `lines_through_C_meet` |
| `ha_ne_I_of_distinct` | `a ≠ I` follows from `a ≠ coord_inv a` via `coord_inv_I_eq_I` |
| `sigma_a_ne_C` | needs `a ≠ I`; ~30 lines |
| `sigma_a_ne_O` / `sigma_a_ne_U` / `sigma_a_ne_E` / `sigma_a_ne_a` / `sigma_a_ne_d_a` | various small distinctness |
| `sigma_a_ne_sigma'` | **X₂₃ side distinctness**: `modular_intersection` at `E_I` with `a ≠ inv_a` forces contradiction `σ_a = E_I ≤ O⊔C` |
| `sigma'_ne_C` (s126) | center-vs-vertex distinctness `hob₃ : C ≠ σ'`; needs `a ≠ I`; covering at `I` collapses `I⊔C = I⊔d_a`, then `lines_through_C_meet` forces `d_a = C`, contradicting `hC_not_m` |
| `inv_a_not_OC` (s126) | `coord_inv a ∉ O⊔C` (needed for the X₂₃ side modular intersection); follows from `inv_a ≤ l`, `l⊓(O⊔C) = O`, `coord_inv_ne_O` |
| `sigma_a_ne_inv_a` (s126) | **vertex distinctness for triangle T₁** (`inv_a ≠ σ_a`): equality forces `σ_a ≤ l⊓(O⊔C) = O`, contradicting `sigma_a_ne_O` |
| `h_sides_X23_mul` (s126) | **the X₂₃ side distinctness theorem itself**, packaged as the bare `≠` claim `inv_a⊔σ_a ≠ d_inv⊔σ'`. Plugs in directly as `desargues_planar`'s `h_sides₂₃` argument. Uses `inv_a_not_OC` + `inf_sup_of_atom_not_le` + `IsAtom.eq_of_le` + `sigma_a_ne_sigma'` |

#### Geometry note for `coord_first_desargues_mul`'s X₂₃ side

`σ'` is defined via `a` (not `inv_a`), so `d_inv ⊔ σ'` does **not** have
a clean `I ⊔ d_inv` form — the symmetry that would give it requires
involutivity (which is what we're proving). The clean argument for
`h_sides₂₃` (`inv_a⊔σ_a ≠ d_inv⊔σ'`):

1. Assume `inv_a⊔σ_a = d_inv⊔σ'`.
2. Then `σ' ≤ inv_a⊔σ_a`. Since `inv_a ∉ O⊔C` (via `coord_inv_ne_O` and
   `(O⊔U)⊓(O⊔C) = O`), modular law: `(inv_a⊔σ_a) ⊓ (O⊔C) = σ_a`.
3. So `σ' ≤ σ_a`, hence `σ' = σ_a` (atoms).
4. Contradicts `sigma_a_ne_sigma'`.

The matching `h_sides₁₃` upgrade `d_a⊔σ' = I⊔d_a` and `a⊔σ_a = a⊔E_I`
ARE clean — covering at `d_a` and `a` respectively (precedent in
`coord_mul_right_inv` step 3 at line ~411).

#### Watch-outs noted during session 125 proof attempt

* `line_direction` produces `(d_a ⊔ Γ.I) ⊓ ...`, NOT `(Γ.I ⊔ d_a) ⊓ ...`;
  pre-rewrite with `sup_comm` (precedent: `coord_mul_right_inv` line 416).
* `▸` rewrite with an equation between two atoms can substitute in the
  wrong place (e.g., `hmeet ▸ x` may rewrite `Γ.C` inside `a ⊔ Γ.C`
  instead of in the goal's RHS). Prefer `(...).trans h_eq.le` for
  unambiguous direction.
* `IsAtom.le_iff` is owned by the **target** (upper) atom — see the
  CLAUDE.md trip-up bullet.

#### Ergonomic helper added

`IsAtom.eq_of_le ha_lower hb_upper h_le : a = b` (FTPGExplore.lean:71)
smooths the `(hb.le_iff.mp h).resolve_left ha.1` pattern used 50+
times across FTPG files. Existing call sites can be refactored
opportunistically; new code should use it directly.

#### Open frontier toward division ring (and thence FTPG-as-theorem)

1. **`coord_mul_assoc`.** Now lives at `Foam/FTPGMulAssoc.lean`
   as a s133 design stub (statement + one helper, both `sorry`'d,
   architecture in the file's header docstring). Critical-path
   geometric lemma per s132. Proposed proof routes through four
   `dilation_mul_key_identity` applications + a
   `dilation_determined_by_param` uniqueness argument (the
   multiplicative analog of `translation_determined_by_param`),
   parallel to `coord_add_assoc`'s capstone. Predicted: no fresh
   `DesarguesianWitness`-style commitment needed, since the
   Desargues investment was paid by `dilation_preserves_direction`
   and `dilation_mul_key_identity`. If the prediction fails, the
   residue IS the third witness — see the s132 device-shape note.
   Once `coord_mul_assoc` lands, `coord_mul_left_inv` follows
   algebraically (~20 lines, Mac Lane), and the two open
   sub-lemmas below become redundant on the chain to division
   ring.
2. **`coord_mul_left_inv` (algebraic derivation).** Once
   `coord_mul_assoc` lands: define `b := coord_inv Γ a`, get its
   right inverse `c := coord_inv Γ b`, then
   `b·a = (b·a)·I = (b·a)·(b·c) = b·((a·b)·c) = b·(I·c) = b·c = I`.
   Replaces the geometric path through `axis_to_sigma_a_le` /
   `sigma_a_le_I_sup_d_inv_distinct`.
3. **DivisionRing instance**, vector space `V` construction, lattice
   iso `L ≃o Sub(D, V)`, replacing `axiom ftpg` in `Bridge.lean` with
   the constructed theorem.

**Deprioritized (s132): `axis_to_sigma_a_le`.** The remaining sorry
in FTPGInverse.lean. Sessions 124–131 mapped its design space
extensively. Session 132's strategy-(iii) attempt showed any clean
forward-Desargues design's center hypothesis reduces to the lemma
itself; a planar converse Desargues approach would need a `*Witness`
interface analogous to `DesarguesianWitness` for left distrib. Both
paths are bypassed by item 1's algebraic derivation. The lemma's
docstring documents D11 (the cleanest design found) for any future
work that wants to capture the geometric statement directly.

**Historical (sessions 124–127): `coord_first_desargues_mul`** —
fully PROVEN as of session 128. The single Desargues call producing
`X₂₃ ≤ U⊔X₁₃`. Distinctness work factored as 12 private helpers
(8 from s124–125 + 3 from s126 + `h_sides_X23_mul`/`h_sides_X13_mul`
packaging the X₂₃ and X₁₃ side `≠` claims). Final step:
`collinear_of_common_bound` with `s₁=U`, `s₂=(a⊔E_I)⊓(I⊔d_a)`,
after rewriting the desargues output covering `U⊔X₁₃ ⋖ π` via
`line_covBy_plane` with `c=O`.

### FTPGLeftDistrib (session 119)

`Foam/FTPGLeftDistrib.lean` builds with **zero `sorry`** as of session 119.
The file is ~1216 lines. The remaining geometric residue — the planar
converse Desargues content — is named explicitly as `DesarguesianWitness Γ`,
a structure whose inhabitant the user supplies as a runtime commitment.
Four pieces compose:

1. `_scratch_forward_planar_call` (~line 119) — the direct `desargues_planar`
   call for the left-distrib configuration. **Fully discharged.** All ~12
   triage hypotheses close from a shared prologue (atomicity via
   `perspect_atom`, the two [KEY] central-perspectivity conditions, the
   [COV] covBy claims, the [MECH] distinctness conditions). `hσb_ne_C` is
   derived from `hb_ne_I` via `sigma_b_eq_C_imp_b_eq_I`; real usage must
   case-split on `b = I` separately (a·I = a makes the forward Desargues
   degenerate).

2. `_scratch_left_distrib_via_axis` (~line 601) — the **axis-to-left_distrib
   bridge**. Given the scratch's axis output plus the concurrence hypothesis
   `h_concur : W' ≤ σ_s ⊔ d_a`, fully discharges
   `coord_mul Γ a (coord_add Γ b c) = coord_add Γ (coord_mul Γ a b)
   (coord_mul Γ a c)`. Realizes session 114's plan: the axis gives P₁, P₂,
   P₃ collinear; `P₁⊔P₂ ⋖ π` (via `line_covBy_plane` with U as the third
   non-collinear atom) lets `collinear_of_common_bound` conclude
   `P₃ ≤ P₁⊔P₂`; `P₃ = coord_add ab ac` (atoms on l); concurrence gives
   `σ_s ⊔ d_a = d_a ⊔ W'`, so `coord_mul a s ≤ d_a⊔W' = P₃ = coord_add ab ac`.

3. `DesarguesianWitness` (~line 1154) — the **observer-supplied commitment**.
   A structure with a single field `concurrence` carrying the planar
   converse Desargues claim for the von Staudt configuration. Geometrically:
   for T1 = (σ_b, ac, σ_s) in π and T2 = (U, E, d_a) collinear on m, the
   vertex-joins are concurrent — `W' = (σ_b⊔U)⊓(ac⊔E) ≤ σ_s⊔d_a`. Session
   114's architectural finding established this is **not derivable from
   CML + irreducible + height ≥ 4 alone** (the
   `desargues_converse_nonplanar` lift+recurse route is structurally
   non-terminating at Level 2 `h_ax₂₃`). Per the deaxiomatization program,
   it is named as a typed pluggable interface rather than carried as an
   unproven theorem.

4. `coord_mul_left_distrib` (~line 1187) — the main theorem. Takes a
   `DesarguesianWitness Γ` as an explicit parameter alongside the usual
   non-degeneracy hypotheses. The body forwards the witness's `concurrence`
   field to `_scratch_left_distrib_via_axis` as `h_concur`. Zero `sorry`.

## Constructing a `DesarguesianWitness`

Two open routes (see `DesarguesianWitness`'s docstring inside
`Foam/FTPGLeftDistrib.lean` for the strategic landscape):

1. **Planar converse Desargues as a top-level lemma** (probably belongs in
   FTPGCoord). The classical converse for two coplanar triangles, proven
   via a single 3D lift that does not require recursive converse calls.
   `DesarguesianWitness.concurrence` becomes a thin specialization (T2
   collinear on m).
2. **Direct construction exploiting axis = m.** Since T2 = (U, E, d_a)
   sits on m, all three pairwise side-intersections are atoms on m. The
   pairing's natural axis is m itself. A `small_desargues'`-style argument
   (FTPGCoord:865) may reduce concurrence to lattice distinctness.

When `L = Sub(D, V)` for a division ring D, `DesarguesianWitness Γ` is
constructible from the model — the substrate fills the observer slot. In
the abstract lattice setting, the slot is genuinely open.

The 1500-line scaffold deleted in session 117 (the lift+recurse attempt)
is in git history (`git show 5fe8073:lean/Foam/FTPGLeftDistrib.lean`) if
any specific helper is wanted.

## Idiom notes

- The project uses `set` heavily for readable goals. Term-mode proofs
  (`inf_le_left`, `inf_le_right`) mostly elaborate through `set` bindings,
  but fall back to `by show <unfolded>; exact ...` when elaboration fails.
- `noncomputable def coord_mul / coord_add` need explicit `unfold coord_mul`
  (or `coord_add`) inside a `by` block before term-mode `inf_le_right`
  works against them.
- `h ▸ x` with `h : a = b` rewrites via motive inference and tries both
  directions; don't eagerly reach for `h.symm ▸` unless the simpler form
  fails to elaborate.
- The `σ_b ≠ X where X ≤ m` pattern closes via `hσb_not_m (h.symm ▸ _)`.
- The `σ_b ≠ X where X ≤ l` pattern closes via
  `hkl_eq_O ▸ le_inf (h ▸ hσb_k) <X ≤ l> |> Γ.hO.le_iff.mp |>.resolve_left <X is atom>`
  — see the `hoa₂` proof for a worked example.
- **`IsAtom.le_iff` is owned by the *target* atom.** For `x ≤ p` where p
  is the atom, use `hp.le_iff.mp` (gives `x = ⊥ ∨ x = p`). The opaque
  error "expected `Γ.E_I = inv_a` got `inv_a = Γ.E_I`" usually means you
  reached for the wrong atom's `le_iff` and Lean is producing the
  equality the wrong way around. Pair with `.resolve_left atom.1` (using
  the atom's `.1 : x ≠ ⊥`) and a `.symm` if you want the opposite
  direction. **Or just use `IsAtom.eq_of_le ha_lower hb_upper h_le`**
  (FTPGExplore.lean:71) — smooths the whole pattern when both sides
  of `≤` are atoms, with unambiguous argument order.
- **`atom_covBy_join hp hq hpq : p ⋖ p ⊔ q` covers from the *first* arg.**
  To get `q ⋖ p ⊔ q`, call as `atom_covBy_join hq hp hqp` (q first) and
  then `sup_comm` the join — but see the next bullet.
- **`set` + `rw [sup_comm]` is fragile.** With `set d_a := (a⊔C)⊓m` in
  scope, `rw [sup_comm] at h` may rewrite the *inner* `a ⊔ C` instead of
  the outer `d_a ⊔ Γ.I` you wanted — Lean still typechecks against the
  unfolded form. Use `(sup_comm d_a Γ.I) ▸ h` (explicit args) or
  `rw [show ... = ... from sup_comm _ _]` (explicit equation). Same trap
  if you have multiple `_ ⊔ _` subexpressions in the goal.
- **`h ▸ x` against `set`-bound names sometimes needs a type annotation.**
  With `set d_a := (a⊔C)⊓m`, hypothesis `h : a = d_a`, and `ha_on : a ≤ l`,
  the bare term `h ▸ ha_on` may produce an opaque "type mismatch" when
  fed to a lemma expecting `d_a ≤ l`. Annotate explicitly:
  `(h ▸ ha_on : d_a ≤ l)`. Same fix wherever the `set`-bound name appears
  in the target type of a `▸` rewrite.
- **Transitivity direction in covering-lemma lambdas.** When `heq : X = X ⊔ σ`
  and you want `σ ≤ X` (typically to feed `hσ_not_X`), the order is
  `le_sup_right.trans heq.symm.le` (σ ≤ X⊔σ, then X⊔σ ≤ X). The reverse
  `heq.symm.le.trans le_sup_right` doesn't typecheck. Easy to flip when
  writing the `lt_of_le_of_ne le_sup_left (fun heq => h_not (...))`
  lambda for a `Γ.U ⊔ Γ.V < Γ.U ⊔ Γ.V ⊔ σ'` step in a triangle-plane proof.
- **Don't reflexively `.symm` after `(IsAtom.le_iff.mp _).resolve_left _`.**
  When chaining `le_sup_right.trans h.symm.le` to get `q ≤ p` then
  `hp.le_iff.mp` (target atom is `p`) gives `q = p` directly. If your
  hypothesis is `h_ne : q ≠ p`, feed the result straight in. Adding a
  trailing `.symm` produces the opaque "expected `q = p` got `p = q`"
  error — the same family as the IsAtom.le_iff direction bullet above,
  but specifically in the chained-`trans` form that shows up in the
  `lt_of_le_of_ne` lambdas of covering arguments.

## Ring-law-on-coord_X file template

`FTPGNeg.lean` and `FTPGInverse.lean` share a recurring shape, worth
naming:

```
def coord_X     -- the construction (noncomputable, lattice expression)
coord_X_on_l    -- inf_le_right or similar one-liner
coord_X_atom    -- via line_meets_m_at_atom (or perspect_atom)
coord_X_ne_O    -- case-analysis on σ' = O via covering / line_direction
coord_X_ne_U    -- case-analysis on σ' = E or projection-line meets l at U
main_identity   -- the headline theorem; goes through ~2–3 perspectivity
                -- inversions + a covering + final line_direction to l
```

The proof of the main identity almost always has the shape: "rewrite the
left-leg perspectivity to its `(O⊔C) ⊓ (b ⊔ E_I)` form (or analogous),
show this equals σ' for some constructed σ', then σ' ⊔ d_a is a covering
line through I (or O, or whatever the target atom is), so `(σ' ⊔ d_a) ⊓ l`
projects to that atom by `line_direction`."

When starting `coord_mul_assoc` or `coord_mul_left_inv`, copy the FTPGInverse
skeleton — the imports, namespace, `set` abbreviations, structural lemmas —
and adapt rather than rebuild.

## Session hygiene

When a sandbox recycles, the `elan override` and the extracted toolchain
directory are gone; redo the setup above. The git repo and Mathlib checkout
under `.lake/packages/` persist across the git worktree but not a fresh
sandbox.
