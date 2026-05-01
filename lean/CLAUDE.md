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

### Current frontier (session 120, 2026-04-30)

`Foam/FTPGInverse.lean` lands `coord_inv`, `coord_mul_right_inv`
(`a · a⁻¹ = I`), and the non-degeneracy helpers `coord_inv_ne_O`,
`coord_inv_ne_U` with **zero `sorry`**. The construction is reverse
perspectivity through `I ⊔ d_a`:

```
d_a = (a⊔C) ⊓ m
σ' = (O⊔C) ⊓ (I⊔d_a)
a⁻¹ = (σ'⊔E_I) ⊓ l
```

The non-degeneracy helpers reduce cleanly: `coord_inv = O` collapses
the σ'⊔E_I line to O⊔E_I, forcing σ' ≤ (O⊔C)⊓(O⊔E_I) = O, contradicting
`sigma'_ne_O`. Symmetric for `coord_inv = U` via U⊔E_I ≤ m and
`sigma'_ne_E`.

Open frontier toward division ring (and thence FTPG-as-theorem):

1. **`coord_mul_left_inv` (`a⁻¹ · a = I`).** The geometric content
   reduces to **σ_a = σ'_{a⁻¹}** as atoms on (O⊔C); equivalently
   `coord_inv` is involutive. The Desargues plan is laid out in
   `Foam/FTPGInverse.lean`'s top docstring: center C, triangles
   `T₁ = (a, a⁻¹, σ_a)` on `(l,l,OC)` and `T₂ = (d_a, d_{a⁻¹}, σ')` on
   `(m,m,OC)`. The first axis intersections are U and `(a⊔E_I)⊓(I⊔d_a)`;
   the third intersection `(a⁻¹⊔σ_a)⊓(d_{a⁻¹}⊔σ')` carries the open
   geometric content. Two paths from there:
   - (a) Prove `coord_mul_assoc` first; left inverse follows in a few
     lines from assoc + right inverse + `a⁻¹ · (a⁻¹)⁻¹ = I` plus a
     small algebraic juggle.
   - (b) Build `coord_first_desargues_mul` / `coord_second_desargues_mul`
     analogues of `FTPGAddComm`'s ~600/~800 line additive ones, then
     `coord_mul_left_inv` lands in ~30 lines like `coord_add_left_neg`'s
     ~250 lines (including a char-2 case-split for self-inverse a).
2. **`coord_mul_assoc`.** Likely a sibling file to FTPGInverse, ~600–1500
   lines, Desargues-style argument via dilation composition.
3. **DivisionRing instance**, vector space `V` construction, lattice iso
   `L ≃o Sub(D, V)`, replacing `axiom ftpg` in `Bridge.lean` with the
   constructed theorem.

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
  direction.
- **`atom_covBy_join hp hq hpq : p ⋖ p ⊔ q` covers from the *first* arg.**
  To get `q ⋖ p ⊔ q`, call as `atom_covBy_join hq hp hqp` (q first) and
  then `sup_comm` the join — but see the next bullet.
- **`set` + `rw [sup_comm]` is fragile.** With `set d_a := (a⊔C)⊓m` in
  scope, `rw [sup_comm] at h` may rewrite the *inner* `a ⊔ C` instead of
  the outer `d_a ⊔ Γ.I` you wanted — Lean still typechecks against the
  unfolded form. Use `(sup_comm d_a Γ.I) ▸ h` (explicit args) or
  `rw [show ... = ... from sup_comm _ _]` (explicit equation). Same trap
  if you have multiple `_ ⊔ _` subexpressions in the goal.

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
