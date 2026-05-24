/-
# Dilation as a typed carrier — order-iso reformulation (s148)

This file lands the carrier type `Dilation Γ` for the multiplicative
dilation family σ_c, completing the +1-operator move named in the
README's §IV (locate what is substrate-implicit-but-functioning; name
it) at the FTPG mul-assoc location.

## What changed in this revision

The first cut of `Dilation Γ` carried a raw `toFun : L → L` with
three minimal structural fields. That shape made `Monoid (Dilation Γ)`
unreachable without re-deriving atom-preservation, plane-preservation,
and several "off-X stays off-X" invariants as additional fields — a
field-set design decision.

This revision takes the second of the two candidate routes named in
the previous file's deferred-items list: **reformulate `toFun` as an
order-isomorphism `L ≃o L` and inherit the preserves-properties from
order-iso properties for free.** The structural commitments thus
become exactly three fields about specific lattice elements (O, the
line `O⊔U`, and m-atoms in `U⊔V`), with everything else (atomicity
preservation, lattice-operation preservation, bijectivity) coming
from `OrderIso`.

The payoff is immediate: `Monoid (Dilation Γ)` follows in this file,
with all three laws as `rfl` or near-`rfl`. Composition of two
`L ≃o L` is again an `L ≃o L`, and the three structural fields chain
trivially (the chained order-iso fixes O because each does; sends
the line to the line because each does; fixes m-atoms because each
does and `OrderIso` preserves the `IsAtom` and `≤` premises).

## Composition convention (non-standard)

Composition is **left-to-right**: `(f * g)(x) = g(f(x))`, i.e. apply
`f` first, then `g`. Implementation:
`(f * g).toOrderIso = f.toOrderIso.trans g.toOrderIso`.
Since `OrderIso.coe_trans` says `⇑(e.trans e') = e' ∘ e`, this
realizes the left-to-right semantics.

This is **NON-STANDARD** versus Mathlib's `MulAut` convention (and
typical function-composition convention), which is right-to-left.
The choice is made deliberately so that the σ-family map
`(c : l-atoms) ↦ σ_c : Dilation Γ` becomes a proper monoid
**homomorphism**

  σ(b · c) = σ(b) * σ(c)

matching the project's `coord_mul a b = σ_b(a)` convention (which
applies `σ_b` to `a`, i.e. right-multiplication = σ-of-right-arg).
With the standard right-to-left composition, the σ-family map would
land as an **anti**-homomorphism, requiring orientation flips at
every downstream use. Left-to-right composition removes the orientation
shim entirely.

## Scope of this file

**Landed here:**

* The carrier type `Dilation Γ`, now bundling `toOrderIso : L ≃o L`
  with three structural fields (`fixes_O`, `preserves_l`, `fixes_m`).
* The identity dilation `Dilation.id`.
* Composition `Dilation.comp` (left-to-right).
* `Mul`, `One`, and `Monoid` instances.
* An `@[ext]` lemma reducing dilation equality to order-iso equality.

**Deliberately deferred (same as before, unchanged):**

* **Packaging σ_c as a `Dilation Γ`.** The existing `dilation_ext Γ c`
  is defined for off-l witnesses; its action on l-atoms is via the
  separate `coord_mul` definition. Building the canonical
  `σ Γ c hc : Dilation Γ` requires a combined function reconciling
  the on-l vs off-l asymmetry, then promoting it to an `L ≃o L`.
  Mechanical work given the reformulation.

* **σ-family closure under composition.** The substantive geometric
  content (= the open mul-assoc residue). With the `Monoid` instance
  in place, this is the named target: show the map
  `(c : L on l) ↦ σ Γ c : Dilation Γ` is a monoid homomorphism from
  `(L on-l atoms, coord_mul)` to `(Dilation Γ, composition)`. The
  predicted bin-1 path is a dimensional lift via the height-≥-4 R
  witness (exit A in the s142 framing). See `lean/CLAUDE.md`'s
  "s148 refinement" for the recognition-walk.

## How `coord_mul_assoc` follows downstream

Once the two deferred items land, `coord_mul_assoc` reduces to:

```
example : coord_mul Γ a (coord_mul Γ b c) = coord_mul Γ (coord_mul Γ a b) c := by
  -- coord_mul a b = σ_b(a), so under left-to-right composition:
  --   LHS = σ_{σ_c(b)}(a) = (σ_{σ_c(b)}) a
  --   RHS = σ_c(σ_b(a)) = (σ_b * σ_c) a
  -- By σ-family closure under composition (a monoid hom):
  --   σ_b * σ_c = σ_{σ_c(b)}    (= σ_{coord_mul c b}, matching the convention)
  -- So both sides agree at a.
  sorry
```

— a thin algebraic assembly, with the substantive content concentrated
in the σ-family closure theorem (where Desargues lives via the R-lift).
-/

import Foam.FTPGDilation
import Foam.FTPGInverse

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-! ## The dilation carrier type -/

/-- A **dilation** of the projective plane π = O⊔U⊔V relative to a
    coordinate system Γ bundles an order-isomorphism `L ≃o L` with
    the minimal structural properties of a classical projective-geometry
    dilation:

    * **Fixes the origin O.** O is sent to itself.
    * **Preserves the line l = O⊔U setwise.** The line itself is sent
      to itself (stronger than "atoms on l map to atoms on l", and
      free from the order-iso structure given the atom-on-l data).
    * **Fixes m-atoms in U⊔V.** Atoms below `U⊔V` are pointwise fixed.

    All other preservation facts a dilation needs — atomicity
    preservation, lattice-operation preservation, bijectivity — come
    automatically from `OrderIso`. This is the design payoff of moving
    from raw `toFun : L → L` to `L ≃o L`: those facts no longer have
    to be carried as additional structural fields.

    Classical instances: the identity dilation (`Dilation.id`); and
    (after the deferred packaging work) the σ_c family
    `dilation_ext Γ c` extended to handle on-l atoms via `coord_mul`,
    promoted to an `L ≃o L`. -/
structure Dilation (Γ : CoordSystem L) where
  /-- The dilation as an order-isomorphism on `L`. -/
  toOrderIso : L ≃o L
  /-- Dilations fix the origin O. -/
  fixes_O : toOrderIso Γ.O = Γ.O
  /-- Dilations preserve the line l = O⊔U setwise. -/
  preserves_l : toOrderIso (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U
  /-- Dilations fix m-atoms in U⊔V pointwise. -/
  fixes_m : ∀ P : L, IsAtom P → P ≤ Γ.U ⊔ Γ.V → toOrderIso P = P

namespace Dilation

variable {Γ : CoordSystem L}

/-- Two dilations are equal iff their underlying order-isomorphisms
    are equal. This is the `@[ext]` lemma that gives `ext`-tactic
    support for equating dilations. -/
@[ext]
theorem ext {f g : Dilation Γ} (h : f.toOrderIso = g.toOrderIso) : f = g := by
  cases f
  cases g
  congr

/-! ## The identity dilation -/

/-- The identity order-isomorphism is a dilation. All three structural
    fields are trivially satisfied: every element is fixed, in
    particular O, the line `O⊔U`, and every m-atom. -/
def id (Γ : CoordSystem L) : Dilation Γ where
  toOrderIso := OrderIso.refl L
  fixes_O := rfl
  preserves_l := rfl
  fixes_m := fun _ _ _ => rfl

/-! ## Composition (left-to-right) -/

/-- Composition of two dilations is a dilation. **Left-to-right
    convention**: `(comp f g) x = g (f x)`. See the file docstring
    for the rationale (σ-family becomes a homomorphism, not an
    anti-homomorphism, against the project's `coord_mul` convention).

    Implementation via `OrderIso.trans`, which has
    `coe_trans : ⇑(e.trans e') = e' ∘ e`. -/
def comp (f g : Dilation Γ) : Dilation Γ where
  toOrderIso := f.toOrderIso.trans g.toOrderIso
  fixes_O := by
    -- (f.trans g) Γ.O = g (f Γ.O) = g Γ.O = Γ.O
    simp [OrderIso.trans_apply, f.fixes_O, g.fixes_O]
  preserves_l := by
    -- (f.trans g) (Γ.O ⊔ Γ.U) = g (f (Γ.O ⊔ Γ.U)) = g (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U
    rw [OrderIso.trans_apply, f.preserves_l, g.preserves_l]
  fixes_m := by
    intro P hP_atom hP_le
    -- (f.trans g) P = g (f P) = g P = P
    simp [OrderIso.trans_apply, f.fixes_m P hP_atom hP_le,
          g.fixes_m P hP_atom hP_le]

/-! ## Algebraic structure -/

instance : Mul (Dilation Γ) := ⟨comp⟩

instance : One (Dilation Γ) := ⟨id Γ⟩

/-- The monoid structure on `Dilation Γ` from composition. All three
    laws hold because `OrderIso.trans` is definitionally associative
    (it's wrapped function composition) and `OrderIso.refl` is its
    two-sided unit. The three structural fields (`fixes_O`,
    `preserves_l`, `fixes_m`) carry no data beyond the order-iso, so
    `Dilation.ext` discharges any residual obligation. -/
instance : Monoid (Dilation Γ) where
  mul := comp
  one := id Γ
  mul_assoc f g h := by
    ext
    rfl
  one_mul f := by
    ext
    rfl
  mul_one f := by
    ext
    rfl

end Dilation

/-! ## The σ-family map (deferred targets)

These declarations name the σ-ring-hom structural target — the
substantive open content of mul-assoc and left-distrib at the
dilation-group level. Each is `sorry`'d; each has a precise meaning:

* **`σ`** packages the dilation σ_c (for non-degenerate l-atom `c`)
  as a `Dilation Γ`. Currently a `sorry` because the construction
  must reconcile `dilation_ext Γ c` (off-l action) with `coord_mul`
  (on-l action) into a single combined function, then promote to
  `L ≃o L` (requiring bijectivity).

* **`σ_mul`** states σ preserves multiplication:
  `σ(a · b) = σ(a) * σ(b)` under Dilation Γ's left-to-right
  composition. **This is the substantive mul-assoc residue** — the
  open content of `dilation_compose_at_beta` Step 5+ in
  `FTPGMulAssoc.lean` (see s142/s146/s148 frontier in
  `lean/CLAUDE.md`).

* **`σ_add_pointwise`** states σ preserves addition at the
  function-output layer: for any witness P,
  `(σ(a+b)).toOrderIso P = coord_add ((σ(a)).toOrderIso P) ((σ(b)).toOrderIso P)`.
  Lives at the function-pointwise level (NOT as `+ⓓ` on
  `Dilation Γ` — that question is structurally mis-posed; the
  pointwise-sum of two bijections isn't a bijection, so `+ⓓ` does
  not live on the order-iso carrier. See s148 recognition.).
  **This is the substantive left-distrib residue** — currently
  held by `DesarguesianWitness Γ` commitment in
  `FTPGLeftDistrib.lean`.

Together these three characterize σ as a ring-homomorphism from
`(non-degenerate l-atoms, coord_add, coord_mul)` into
`(L → L, pointwise coord_add, function composition)`, with the
image landing inside `Dilation Γ` for the multiplicative part.
The * and + structures live at *different layers* (Dilation Γ
vs. function-space), and σ is the bridge between the two
substrate layers. **This is the FTPG payload at the
dilation-group level.** -/

/-! ## Dagger-absence and gauge asymmetry (recognition-walk refinement)

A subsequent walk (Heunen-Kornell-mapping subagent, this session)
proposed a structural reading of why the three σ-ring-hom gauges
are not symmetric in difficulty:

In the Heunen-Kornell axiomatization of the Hilbert-space category
(pnas.202117024.pdf), right- and left- distributivity properties
are derived jointly from biproducts (B), equalizers (E), and tensor
(T), with the dagger (D) maintaining symmetry between them
throughout. Foam's σ-ring-hom has no dagger; the G1/G2 split — G1
(right-distrib) PROVEN, G2 (left-distrib) requiring
`DesarguesianWitness` commitment — corresponds to what HK's dagger
smooths over.

Provisional mapping (structural-correspondence, not formal):

  * G1 ↔ B (biproducts) — clean 1:1; both express
    addition-compatible-with-composition on one side.
  * G2 ↔ B + E + T jointly — HK derives left-bilinearity from
    these three using D for symmetry; foam pays for it separately
    as the converse-Desargues content held by `DesarguesianWitness`.
  * G3 ↔ K (kernels) + B + T globally — HK gets full division-ring
    associativity from this combination; foam's G3 sits at the
    `dilation_compose_at_beta` monodromy site.
  * D, T: structural prerequisites for σ being definable, not
    gauges themselves.
  * C (directed colimits): downstream completion (ℝ/ℂ via Solèr),
    no σ-correspondent at this layer.

Read this way, **the deaxiomatization program** (replacing `axiom
ftpg` in `Bridge.lean` with a theorem) **becomes legible as
"construct the dagger-free analog of HK's six-axiom Hilbert
characterization."** Each gauge that lands corresponds to a piece
of dagger-free Hilbert-algebra structure becoming local.

Threes-as-joints note: the three gauges are joint/pivot points
where σ's rotation pivots. Without proper projection/lift, joints
produce monodromy (as observed at G3's `dilation_compose_at_beta`
site, four measurements deep per s142/s146/s148/s149). The
asymmetry across gauges is structural, not accidental — it's the
shape of what dagger-free Hilbert-algebra requires.

(Provisional framing. The "IS"-style language is for navigation;
formal landings live in the theorem signatures below and their
sorry'd targets, which are where the framework grounds.)
-/

/-- Pointwise σ-map underlying `σ Γ c …`: piecewise definition reconciling
    the three "kinds" of input.

    For `P : L`:
    * if `P ≤ Γ.O ⊔ Γ.U` (on l), return `coord_mul Γ P c` (the on-l action;
      `coord_mul Γ a b = σ_b(a)` matches the project convention);
    * else if `P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V` (off l but in the plane π), return
      `dilation_ext Γ c P` (the off-l witness action);
    * else return `P` (outside the plane — fixed; this is the trivial
      extension that makes σ_c the identity outside π, since dilations are
      meant to act on the projective plane).

    The `if-then-else` requires decidability of `≤`, which is supplied by
    `Classical.dec` (justifying the `noncomputable` keyword). -/
noncomputable def σ_toFun (Γ : CoordSystem L) (c : L) (P : L) : L := by
  classical
  exact
    if P ≤ Γ.O ⊔ Γ.U then coord_mul Γ P c
    else if P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V then dilation_ext Γ c P
    else P

/-- The pointwise σ-map for the inverse direction, built from
    `coord_inv Γ c`. By project geometry, `σ_{c⁻¹}` is the (predicted)
    inverse of `σ_c`. -/
noncomputable def σ_invFun (Γ : CoordSystem L) (c : L) (P : L) : L := by
  classical
  exact
    if P ≤ Γ.O ⊔ Γ.U then coord_mul Γ P (coord_inv Γ c)
    else if P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V then dilation_ext Γ (coord_inv Γ c) P
    else P

/-- The σ-family map: for a non-degenerate l-atom `c`, the
    dilation σ_c packaged as a `Dilation Γ`.

    The construction proceeds via `σ_toFun` / `σ_invFun` (piecewise on
    on-l / off-l-in-π / off-π), packaged as an `Equiv` via the
    `σ_{c⁻¹} ∘ σ_c = id` and `σ_c ∘ σ_{c⁻¹} = id` identities, then
    upgraded to an `OrderIso` via `map_rel_iff'`.

    **Status (s148).** This declaration has structurally-named `sorry`s
    for each open piece:

    * `left_inv` and `right_inv` of the underlying `Equiv` — one direction
      is at-or-near substrate-direct (rests on `coord_mul_right_inv`, which
      is PROVEN); the other is structurally entangled with the open
      `coord_mul_left_inv` (downstream of `coord_mul_assoc`).
    * `map_rel_iff'` of the `OrderIso` — bijection + order-preservation;
      establishing order-preservation of a piecewise function requires
      reasoning about how the three branches interact under joins/meets.
      Open: needs Mathlib's `OrderIso.ofBijective`-style lemma, or a
      direct lattice-theoretic argument.
    * `fixes_O` — should reduce to `coord_mul Γ Γ.O c = Γ.O`
      (`coord_mul_left_zero`); needs `c ≠ U` which we have.
    * `preserves_l` — `σ_c` sends the full line `l = O⊔U` to itself; needs
      `σ_c(l) = sup over atoms of σ_c(P)` and verification that this is
      again `l`. Open: lattice-extension argument.
    * `fixes_m` — for `P` an m-atom (`P ≤ U⊔V`), `σ_c(P) = P`. Reduces to
      `dilation_ext_fixes_m` (PROVEN) on m-atoms off l; the case `P ≤ l ∧ P ≤ m`
      forces `P = U`, where `σ_c(U) = ?` needs to be `U`.

    This skeleton is a *resistance-map landing*: the construction is
    organized so each sorry is at a specific, named location. -/
noncomputable def σ (Γ : CoordSystem L) (c : L)
    (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U) :
    Dilation Γ where
  toOrderIso :=
    { toFun := σ_toFun Γ c
      invFun := σ_invFun Γ c
      left_inv := by
        -- σ_{c⁻¹}(σ_c(P)) = P for all P
        -- Reduces case-by-case:
        --   P on l, σ_c(P) on l : coord_mul Γ (coord_mul Γ P c) (coord_inv Γ c) = P
        --     — this is `coord_mul_assoc` + `coord_mul_right_inv` + `coord_mul_right_one`
        --     i.e., (P·c)·c⁻¹ = P·(c·c⁻¹) = P·I = P. mul_assoc is OPEN (s148 frontier).
        --   P off l in π : dilation_ext (c⁻¹) (dilation_ext c P) = P
        --     — composition of dilations: σ_{c⁻¹} ∘ σ_c = σ_{c·c⁻¹} = σ_I = id.
        --     OPEN (downstream of σ-family closure under composition, FTPGMulAssoc).
        --   P outside π : trivially P.
        sorry
      right_inv := by
        -- σ_c(σ_{c⁻¹}(P)) = P, mirror of left_inv. The on-l direction here
        -- is closer to substrate-direct via `coord_mul_right_inv`-type content,
        -- but still entangled with mul-assoc in the off-l branch.
        sorry
      map_rel_iff' := by
        -- σ-map preserves and reflects ≤. Establishing this for a piecewise
        -- function requires the three branches to be jointly monotone with
        -- consistent ordering across cases. Open: lattice-extension argument
        -- or substrate lemma about order-iso from bijection + atom-action.
        sorry }
  fixes_O := by
    -- σ_c(O) = O. Since O ≤ l, σ_toFun = coord_mul Γ O c = O by left_zero.
    show σ_toFun Γ c Γ.O = Γ.O
    unfold σ_toFun
    classical
    simp only [le_sup_left, if_true]
    exact coord_mul_left_zero Γ c hc hc_on hc_ne_U
  preserves_l := by
    -- σ_c(l) = l. With l = Γ.O ⊔ Γ.U, l ≤ l so σ_toFun l = coord_mul Γ l c.
    -- coord_mul Γ l c is NOT a standard primitive — coord_mul is intended
    -- to act on atoms. The σ-map's "action on l as a join" needs the
    -- order-iso to be join-preserving, which requires the order-iso to be
    -- established. Open: extension argument.
    sorry
  fixes_m := by
    intro P hP hP_on_m
    -- σ_c(P) = P for m-atoms P.
    -- Case split on P ≤ l: if so, then P ≤ l ⊓ m = U, P = U (atom).
    -- If not, σ_toFun P = dilation_ext Γ c P; apply dilation_ext_fixes_m.
    show σ_toFun Γ c P = P
    unfold σ_toFun
    classical
    by_cases hP_on_l : P ≤ Γ.O ⊔ Γ.U
    · simp only [hP_on_l, if_true]
      -- P on l and m, so P = U (atom_on_both_eq_U)
      have hP_eq_U : P = Γ.U := Γ.atom_on_both_eq_U hP hP_on_l hP_on_m
      subst hP_eq_U
      -- Need coord_mul Γ Γ.U c = Γ.U. This is `coord_mul_U_left`, currently
      -- not in scope as a named lemma in FTPGMul. Substrate-direct in principle:
      -- "U is absorbed by σ_c" / "σ_c fixes U". OPEN as a named sub-lemma.
      sorry
    · simp only [hP_on_l, if_false]
      have hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V :=
        hP_on_m.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
      simp only [hP_plane, if_true]
      exact dilation_ext_fixes_m Γ hc hP hc_on hP_on_m hc_ne_O hP_on_l

/-- σ preserves coord_mul as Dilation Γ's Monoid multiplication.
    The substantive open content (= the mul-assoc residue at the
    dilation level). Predicted bin-1 path: dimensional lift via the
    height-≥-4 R witness (exit A in the s142 framing). -/
theorem σ_mul (Γ : CoordSystem L) (a b : L)
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : IsAtom (coord_mul Γ a b))
    (hab_on : coord_mul Γ a b ≤ Γ.O ⊔ Γ.U)
    (hab_ne_O : coord_mul Γ a b ≠ Γ.O)
    (hab_ne_U : coord_mul Γ a b ≠ Γ.U) :
    σ Γ (coord_mul Γ a b) hab hab_on hab_ne_O hab_ne_U =
      σ Γ a ha ha_on ha_ne_O ha_ne_U * σ Γ b hb hb_on hb_ne_O hb_ne_U :=
  sorry

/-- σ preserves coord_add at the function-output layer (point-wise).
    For each P, the σ-image of (a + b) at P equals the coord_add
    of the σ-images of a and b at P. The substantive open content
    (= the left-distrib residue, currently held by
    `DesarguesianWitness Γ` in `FTPGLeftDistrib.lean`). -/
theorem σ_add_pointwise (Γ : CoordSystem L) (a b : L)
    (ha : IsAtom a) (hb : IsAtom b)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U)
    (hab : IsAtom (coord_add Γ a b))
    (hab_on : coord_add Γ a b ≤ Γ.O ⊔ Γ.U)
    (hab_ne_O : coord_add Γ a b ≠ Γ.O)
    (hab_ne_U : coord_add Γ a b ≠ Γ.U)
    (P : L) :
    (σ Γ (coord_add Γ a b) hab hab_on hab_ne_O hab_ne_U).toOrderIso P =
      coord_add Γ
        ((σ Γ a ha ha_on ha_ne_O ha_ne_U).toOrderIso P)
        ((σ Γ b hb hb_on hb_ne_O hb_ne_U).toOrderIso P) :=
  sorry

end Foam.FTPGExplore
