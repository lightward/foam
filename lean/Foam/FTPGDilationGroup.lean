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

/-- The σ-family map: for a non-degenerate l-atom `c`, the
    dilation σ_c packaged as a `Dilation Γ`. The body is open —
    the construction reconciles `dilation_ext Γ c` (off-l
    witnesses) with `coord_mul` (on-l atoms) into a combined
    function, promoted to an `L ≃o L`. -/
noncomputable def σ (Γ : CoordSystem L) (c : L)
    (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U) :
    Dilation Γ := sorry

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
