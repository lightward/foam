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

### Current frontier (session 142, 2026-05-11)

**`Foam/FTPGMulAssoc.lean`: `dilation_compose_at_beta` Step 5+ — s139
(β) prediction FALSIFIED.** s142 carried the (β) re-bridging route
through Steps 1–4 and inspected the closing equality at Step 5+. The
s133/s134/s139 prediction — "(β) re-bridging lands without surfacing
a third `*Witness` interface" — does not hold.

Reason: taking ⊔E of both sides of `σ_y(σ_x(β(a))) = σ_(x·y)(β(a))`
reduces to `(a·x)·y ⊔ E = a·(x·y) ⊔ E`, hence by atom-cover to
`(a·x)·y = a·(x·y)` — `coord_mul_assoc` applied to atoms.
`dilation_compose_at_beta` *contains* its causal antecedent through
the s134 thin assembly, making the architecture **circular through
Lean's dependency graph**:

```
coord_mul_assoc
  ←  dilation_compose_at_witness (×4)
  ←  dilation_compose_at_beta
  ⟹  coord_mul_assoc-at-atoms
```

Step 5+ cannot close on its own infrastructure. Three exits, none
walked (detailed in the section docstring above `dilation_compose_at_beta`
in `Foam/FTPGMulAssoc.lean`):

* **(A) Architecture inversion (bin-1)** — prove `coord_mul_assoc`
  directly via a fresh Desargues call on coord_mul's definition.
* **(B) Named Witness (bin-2)** — surface `MulComposeWitness Γ` as
  typed observer commitment. See "Meta-frontier: bin-2 Witnesses as
  exhaustion findings" below before defaulting to this.
* **(C) Fresh Desargues at this level (bin-1)** — triangle setup
  proving the β-image atom equality directly via a single Desargues
  call. The (α) shifted-key-identity route may be cleanest.

s142 also looked back at `FTPGLeftDistrib.lean`'s `DesarguesianWitness`
under the same framing and found the same shape (one-route exhaustion
mis-characterized as irreducibility). See revised docstring in
`FTPGLeftDistrib.lean` and the "Meta-frontier" section below.

Chain status (post-s142):

```
coord_mul_assoc            (s134 thin assembly; circular below)
  ↓
dilation_compose_at_witness  ← case-split on P ≤ q vs ¬, both reducing to ↓
  ↓
dilation_compose_at_beta   ← contains coord_mul_assoc-at-atoms (s142)
                              Steps 1-4 PROVEN; Step 5+ open via A/B/C
  ↓ (reducible via)
recovery_via_E             (PROVEN, s135–s137)
dilation_mul_key_identity  (PROVEN, FTPGMulKeyIdentity.lean)
dilation_witness_preservation (PROVEN, s134)
```

Earlier-session pieces still in place:

* **`coord_mul_assoc` PROVEN as a thin algebraic assembly** (~30
  lines, 0 sorries in body, s134), using
  `dilation_compose_at_witness` three times +
  `dilation_determined_by_param`.
* **`dilation_witness_preservation` PROVEN** (~70 lines, s134): if
  `P` is a valid witness (atom in π, off l, off m, off O⊔C, ≠ I) and
  `x` a non-degenerate dilation parameter, then `σ_x(P)` is also a
  valid witness. **Note: this preservation lemma does NOT carry
  `¬ σ_x(P) ≤ q`, and s139 found that an unconditional extension
  isn't available** — σ_x doesn't preserve off-q (one critical
  `x*(P)` for which `σ_x(P) ≤ q`). The bridge architecture (see the
  `dilation_compose_at_beta` section docstring in `FTPGMulAssoc.lean`)
  sidesteps this entirely via σ_y's preservation of lines through E.
* **`recovery_via_E` PROVEN** (~400 lines total across s135-s137):
  for a witness P off q, σ_c(P) is recoverable from σ_c(beta_cast Γ P)
  via the line through E and the original ray O⊔P. The β-cast bridge
  (q = U⊔C, projected through E) carries the off-l witness arithmetic
  through to where `dilation_mul_key_identity` (PROVEN) applies on
  on-q points. **Subtleties** that landed in s137 and are reusable:
  * P' witness conditions cluster around the keystone P' ≠ U,
    derivable via U ≤ P⊔E ⇒ E ≤ U through (P⊔U)⊓m = U.
  * σP ≠ σP' (the `dilation_preserves_direction` h_images_ne
    precondition) is NOT derivable from generic dilation injectivity
    — adapt the `FTPGMulKeyIdentity:hσ_ne_DE` pattern: σP = σP' ⇒
    σP ≤ (O⊔P)⊓(O⊔P') = O via `modular_intersection`, then σP ⊄ l
    contradiction. The σP ⊄ l proof itself uses `line_direction`
    twice; `d_P ⊄ l` (a sub-step) needs the chain `d_P = U ⇒ I⊔U
    = I⊔P ⇒ P ≤ l ✗`.
  * `hE_not_OP` and `hO_not_PE` should be at outer scope (not
    nested inside `hPE_covBy_π`) — s137 lifted them; subsequent
    work that touches recovery_via_E should keep them there.
* **`dilation_compose_at_witness` (sorry'd)**: `σ_(x·y)(P) = σ_y(σ_x(P))`
  for general witness `P`. s134's center-O Desargues setup was invalid
  (T1 collinear, s135 finding); s139 architecture replaces it: case-split
  on `P ≤ q` vs ¬, both branches reducing to `dilation_compose_at_beta`.
  Docstring in `FTPGMulAssoc.lean` documents the reduction; theorem
  body unchanged from s137 (single top-level sorry).
* **`dilation_compose_at_beta` (1 sorry: Step 5+, prediction FALSIFIED s142)**:
  `σ_y(σ_x(β(a))) = σ_(x·y)(β(a))` — σ-composition restricted to
  β-images. Status as of s142:
  - Steps 1-4 PROVEN (s140 + s141 + s142): two
    `dilation_mul_key_identity` applications, seven sub-witness
    conditions on `Q := σ_x(β(a))` (including `¬ Q ≤ q` via
    s141's `hQ_not_q`), `recovery_via_E` applies cleanly at
    `h_recovery`.
  - Step 5+ FALSIFIED: the s133/s135/s139 prediction "route (β)
    closes without a `*Witness` interface" does not hold. From
    `h_inner_unfold`, `Q ≤ a·x ⊔ E`, so `b := (Q⊔E)⊓l = a·x` is
    FORCED. The closing equality reduces under ⊔E to
    `(a·x)·y = a·(x·y)` — `coord_mul_assoc` applied to atoms. The
    s134 architecture is circular through this content. Three exits
    A/B/C — see Current frontier above and the section docstring
    above the theorem in `FTPGMulAssoc.lean`.

The s133 helper `dilation_determined_by_param` (PROVEN, ~150 lines)
is the lift-from-witness-agreement used by the capstone.

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

1. **`coord_mul_assoc`.** PROVEN as an assembly in
   `Foam/FTPGMulAssoc.lean` (s134). The substantive sorry on the chain
   to division ring is **`dilation_compose_at_beta`** (named sub-lemma
   from s139): `σ_y(σ_x(β(a))) = σ_(x·y)(β(a))` — σ-composition
   on β-images. With `recovery_via_E` (PROVEN, s137) and
   `dilation_mul_key_identity` (PROVEN) in place, the (β) re-bridging
   route is now fully landed through Step 4. **Steps 1-4 PROVEN
   (s140-s141): two key-identity unfoldings, all 7 Step 3 witness
   sub-conditions on `Q := σ_x(β(a))` discharged, `recovery_via_E`
   application lands at `h_recovery`.** Step 5+ open: closing modular
   juggling, substantive content `b·y = a·(x·y)`. `dilation_compose_
   at_witness` reduces to `dilation_compose_at_beta` via case-split on
   `P ≤ q`. The s132 device-shape question is sharply localized at
   Step 5+.
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

## Meta-frontier: bin-2 Witnesses as exhaustion findings

The project has accumulated typed-observer commitments at points where
the deaxiomatization program named geometric residue as explicit
pluggable interfaces rather than carry as unproven theorems:

* **`DesarguesianWitness Γ`** (`FTPGLeftDistrib.lean`) — the concurrence
  claim for the planar converse-Desargues content of the von Staudt
  configuration. Discharged by `coord_mul_left_distrib` callers.
* **(prospective) `MulComposeWitness Γ`** — would discharge
  `dilation_compose_at_beta`'s Step 5+ if exit (B) is taken on the
  multiplicative branch.

**s142 finding: both commitments are exhaustion-based, not
irreducibility-proven.**

* `DesarguesianWitness`: s114 found `desargues_converse_nonplanar`
  lift+recurse non-terminates at Level 2 `h_ax₂₃`. The s114 → s119
  record stated "not derivable from CML + irreducible + height ≥ 4
  alone"; s142 lookback identified this as an inferential overreach
  from a one-route failure result.
* `MulComposeWitness` (if surfaced): would emerge from s142's
  falsification of the s139 (β) prediction. The falsification shows
  one route can't close; it does not show the content is irreducible.

**Predicted shape:** both slots admit bin-1 bundlings — *typed
constructions of the recursive content as named lattice objects*, on
the `HalfType` template (`lean/Foam/HalfType.lean`: "the diamond iso
IS the half-type theorem" became the constructed `HalfType`, with the
iso as one of its fields). Whether the bundlings exist for these
specific situations is open; the prediction is consistent with the
geometric structure (left-distrib's concurrence is distributivity
content, Desargues-derivable in principle; mul-assoc is
Desargues-derivable in any coordinatized projective space of height
≥ 4).

**Mechanism note (s142):** the predicted structural shape of bin-1
paths is *dimensional lift via the height-≥-4 R witness*. R is
already threaded through the lemma signatures (it's how
`desargues_planar` works internally — uses R to lift planar
configurations into 3-space, applies nonplanar Desargues, projects
back). For situations where the planar argument loops on itself
(the s142 finding for `dilation_compose_at_beta`), the predicted
construction route is: use R to lift the loop-content into 3-space
where it has structural room to close, then project back. The
HalfType template (`lean/Foam/HalfType.lean`) is the bundling shape:
construct a typed object whose existence (via R) carries the
projected lower-dim content as a field. "Residents on the higher
substrate do the work the lower substrate can't" is the structural
slogan.

**Operational consequence:** bin-2 commitments in this project are
*landings*, not destinations. Each Witness is a potential bin-1
bundling waiting to be found. The default disposition when surfacing
a new Witness should be "this names the residue; the bin-1 path is
open" — not "this content is irreducible." The framing shift between
these two dispositions is the s142 working-derivation; see
`history/142_*.md`.

### s144 refinement: bin-1 grade diagnostic + recognition-only working mode

Session 144 (see `lean/Foam/FTPGLeftDistribViaR.lean` docstring and
`derivations/lfp.md`) refined the predicted-bin-1-path framing:

**Bin-1 has a grade diagnostic.** Within bin-1, targets sort by
recognition-readiness:

* **Bin-1-Mathlib-or-Foam (substrate-direct).** The structural fact is
  already a theorem at the substrate layer — either in Mathlib *or* in
  Foam's own previously-recognized primitives (the closed-circuit
  channel: Foam's primitives count regardless of Mathlib membership,
  and each landed bin-1 conversion extends the substrate). The bin-1
  path is packaging — constructor is `{ field := SubstrateLemma }`.
  Work-shape: recognition + assembly. Example: `HalfType`.
* **Open-recognition-target.** Substrate-derivable in principle but
  the path is not yet reduced to substrate-direct primitives. Needs
  more recognition walks before the substrate-direct shape becomes
  visible. Example: `DesarguesianWitness Γ`'s bin-1 path (s144 walked
  two vertex-lift architectures, both seen-not-to-close; the bin-1
  path is reachable in principle but the architecture is still
  maturing — see `FTPGLeftDistribViaR.lean` docstring for the two
  pre-walked architectures and why both fail).

**Recognition-only is the project's working mode.** Construction-grade
work (designing substeps and grinding through them) is not a working
mode this project takes. Re-entrant recognition walks over time may
produce something that *looks like* the product of construction, but
the project never *directly approaches* via construction-design.
Open-recognition-targets resolve by one of:

* Re-entrant recognition eventually reveals they were
  Bin-1-Mathlib-or-Foam all along (substrate has more than was noticed)
* They stay bin-2 until recognition reveals the substrate-direct shape
* The architecture changes such that they're bypassed entirely

The discipline preserves the recognition operator's monotonicity,
hence the K-T convergence of the bin-discipline's lfp iteration. See
`derivations/lfp.md` for the methodology-level synthesis.

**Diagnostic-not-mode.** The grade distinction sorts *targets* by
readiness, NOT *working modes*. One working mode (recognition);
diagnostic distinguishes ready vs. maturing.

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
