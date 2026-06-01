/-
# SeedGaugeBireflectiveOpDuality — the op-duality probe; the dagger is the tamp

Brick 37 (`SeedGaugeBireflectiveDagger.lean`) closed the resistance-triple at three
(`BireflectiveResistanceTriple`, proven) and typed the dagger's **object-level** shadow: the zero
object is op-self-dual (`pointedObjects_isZero_op`, via Mathlib's `IsZero.op`), present on the `+1`
(`Under ⊤`), absent on the `×2` (`Over Bool`). The remainder it produced (§III: a typed
non-recognition produces its own remainder):

> a dagger is a **self-op-duality** `C ≅ Cᵒᵖ` (identity-on-objects), and the `+1`/`×2` are **op-dual
> constructions** — monad ↔ comonad, EM ↔ co-EM, `Under` ↔ `Over` all swap under `op`. So the dagger
> is precisely the structure that would make the op-dual `+1`/`×2` coincide (the §VI bireflective
> fixed point), and §VII names "the dagger as observer-side commitment" = the reader's gauge-fixing =
> the **tamp** (the single-external-commitment functor the whole seed-gauge chain built). Probe whether
> `(Under ⊤)ᵒᵖ ≌ Over ⊤` conducts (install) and read whether the dagger-as-self-op-duality is the tamp.

This file is that probe — the **install** branch.

## What conducts — the op-duality of the constructions (bin-1)

Mathlib carries the op-duality as a *named* equivalence, `Over.opEquivOpUnder X : Over (op X) ≌
(Under X)ᵒᵖ` (with `unitIso = counitIso = Iso.refl _`, as strict as an equivalence gets). So
`under_opDual_over X : (Under X)ᵒᵖ ≌ Over (op X)` — the `+1`-construction (pointed objects / coslice,
`Under`) and the `×2`-construction (colorings / slice, `Over`) **are op-dual as construction-shapes**,
at the **same** base point `X`, mediated by `op`. b37's remainder ("the `+1`/`×2` are op-dual
constructions") is now a Lean theorem, not prose. The two operations the whole bireflective thread has
been comparing are genuinely related — by `op`.

And b37's `IsZero.op` **rides across** the op-duality: `over_op_top_hasZeroObject` transports the `+1`'s
op-self-dual zero object (`pointedObjects_isZero_op`) through `under_opDual_over` into `Over (op ⊤)`. So
the op-dual of the `+1`'s pointed-objects IS an `Over`-construction *carrying a zero object* — the
dagger-shadow surviving the duality.

## Where it lands — `Cᵒᵖ`, not `C`. The dagger is the within-category closure.

The op-duality lands `Over (op X)` in `Cᵒᵖ`, not `C`. To bring it home into `C` you need an equivalence
`C ≌ Cᵒᵖ` — a **dagger** (a self-op-duality). `dagger_closes_opDuality (e : Cᵒᵖ ≌ C) (hX :
e.functor.obj (op X) = X) : (Under X)ᵒᵖ ≌ Over X` types exactly this: given a dagger `e` (the
equivalence `Cᵒᵖ ≌ C`) that fixes the base object (`hX`, the identity-on-objects part of a dagger), the
op-dual construction comes home into `C` at the same base point. The dagger is the precise structure
that closes the category-crossing.

**The tamp is the hypothesis `e`.** The closing equivalence is *conditional on an externally-supplied
self-op-duality* — foam provides no canonical `e : Cᵒᵖ ≌ C` (b37: Mathlib carries no abstract dagger;
foam is no-dagger, §VIII). That required external input IS the single-external-commitment = the **tamp**.
So the bireflective-resistance thread's genuine joint (the dagger) IS the keystone the seed-gauge chain
built (the single-external-commitment functor, `SeedGaugeFunctor.lean`'s `commitmentFunctor`): §VII's
"the dagger as observer-side commitment" now has substrate under it — the dagger is literally the
hypothesis the closing theorem cannot discharge internally. **Dagger = tamp**, the two threads unified.

## The two-root resistance — even a dagger is not enough

Even *with* a dagger, `dagger_closes_opDuality` lands `(Under ⊤)ᵒᵖ ≌ Over ⊤` — at the **same** base
point `⊤`. The foam's `×2` lives at `Bool ≠ ⊤`. So the refuted coincidence `Under ⊤ ≃ Over Bool` (b36)
needs **two** things, and the op-duality (bin-1) supplies *neither*:

1. **the dagger** — to cross `Cᵒᵖ → C` — observer-supplied, the tamp, **absent** in foam;
2. **the base-point match `⊤ ≃ Bool`** — substrate-**false**: `base_points_differ` proves `Over (op ⊤)`
   has a zero object (the `+1`'s self-dual point, `1`) while `Over Bool` has none (the `×2`'s
   irreducible doubling, `2`) — b36's separator, the self-dual point `1` vs the doubling `2`.

One root is observer-supplied (the dagger = the tamp); one is substrate-intrinsic (the `1`-vs-`2`
asymmetry, b36). The op-duality relates the *shapes* `Under`/`Over` at a *fixed* base point across
`C`/`Cᵒᵖ`; it is genuine (bin-1), and it is exactly *not* the coincidence.

## Bin-grading

**bin-1** (Bin-1-Mathlib-or-Foam) for every theorem: `under_opDual_over` is `(Over.opEquivOpUnder _).symm`;
`over_op_top_hasZeroObject` transports b37's `pointedObjects_isZero_op` via b36's `isZeroFunctorObj`;
`dagger_closes_opDuality` composes `under_opDual_over` with Mathlib's `Over.postEquiv` (slice-transport
along an equivalence); `base_points_differ` pairs the transport with b36's `boolColorings_not_hasZeroObject`.
No new geometric content. **bin-2** (interpretive) for the readings: that the op-duality IS the
construction-shape relation the bireflective thread compares; that the dagger IS the missing
within-category closure; that the dagger-as-the-conditional's-hypothesis IS the tamp (dagger =
single-external-commitment, unifying §VI's genuine joint with the keystone the chain built); and that
the resistance has two roots (observer-supplied dagger + substrate-false base-point match).

## NOT the coincidence-trap

Per the brick's warning: typing `(Under X)ᵒᵖ ≌ Over (op X)` is the op-duality of the *construction-shapes*
(true), **NOT** the refuted `Under ⊤ ≃ Over Bool` (b36 — different base points, same category). The
dagger-conditional lands `(Under X)ᵒᵖ ≌ Over X` (same base point `X`), which at `⊤` is `(Under ⊤)ᵒᵖ ≌
Over ⊤` — still *not* `Under ⊤ ≃ Over Bool` (`base_points_differ` proves the `Over ⊤`-side and the
`Over Bool`-side are distinguished by the zero object). The coincidence stays refuted; the
dagger-that-would-install-it — composed with the substrate-false base-point match `⊤ ≃ Bool` — is the
named horizon. This file manufactures no coincidence; it types the op-duality (which holds), the dagger
as the missing piece (a conditional), and why the dagger alone is still not enough.

(Re-grep — stamps decay: on 2026-06-01 `lake build Foam.SeedGaugeBireflectiveOpDuality` is clean, zero
sorry; the file imports `Foam.SeedGaugeBireflectiveDagger` (b37, chaining b36/35/34) and reuses
Mathlib's `Over.opEquivOpUnder` / `Over.postEquiv` from `Comma.Over.Basic` already in scope via b36.)
-/

import Foam.SeedGaugeBireflectiveDagger

namespace Foam

open CategoryTheory CategoryTheory.Limits Opposite

/-! ## 1. The op-duality of the constructions — `(Under X)ᵒᵖ ≌ Over (op X)`

The `+1`-construction (`Under`, pointed objects / coslice) and the `×2`-construction (`Over`,
colorings / slice) are op-dual as construction-shapes, at the *same* base point, mediated by `op`.
This is b37's remainder ("the `+1`/`×2` are op-dual constructions") as a Lean theorem — a named
Mathlib equivalence, `Over.opEquivOpUnder`. -/

/-- **The op-duality of the `+1`/`×2` constructions.** `(Under X)ᵒᵖ ≌ Over (op X)`: pointed-objects
    (the `+1`'s EM-category shape) and colorings (the `×2`'s co-EM-category shape) are op-dual at the
    *same* base point `X`. Mathlib's `Over.opEquivOpUnder`, symmetrized. The construction-shape
    relation the whole bireflective thread has been comparing — genuine (bin-1), mediated by `op`. -/
def under_opDual_over {C : Type*} [Category C] (X : C) : (Under X)ᵒᵖ ≌ Over (op X) :=
  (Over.opEquivOpUnder X).symm

/-- The op-duality at foam's `+1` base point `⊤` — `(PointedObjects)ᵒᵖ ≌ Over (op ⊤)`. `PointedObjects`
    (b36) is the `+1`'s EM-category; its opposite is op-dual to the `×2`-shape `Over` at `op ⊤`. -/
def plusMinus_opDual : (PointedObjects)ᵒᵖ ≌ Over (op (PUnit : Type)) :=
  under_opDual_over _

/-! ## 2. The dagger-shadow rides across — `Over (op ⊤)` HAS a zero object

b37's `IsZero.op` (the dagger's object-level shadow: the zero object is op-self-dual) transports across
the op-duality. The op-dual of the `+1`'s pointed-objects is an `Over`-construction *carrying* a zero
object — the self-dual point surviving the duality, now on the `Over` side (in `Cᵒᵖ`). -/

/-- **`Over (op ⊤)` has a zero object**, transported from the `+1`'s op-self-dual point across the
    op-duality. b37's `pointedObjects_isZero_op` (a zero object in `(Under ⊤)ᵒᵖ`) carried through
    `under_opDual_over ⊤`'s functor by b36's `isZeroFunctorObj`. The dagger-shadow on the `Over`
    side. -/
theorem over_op_top_hasZeroObject : HasZeroObject (Over (op (PUnit : Type))) :=
  (isZeroFunctorObj (under_opDual_over (PUnit : Type)) pointedObjects_isZero_op).hasZeroObject

/-! ## 3. The dagger is the within-category closure — `dagger_closes_opDuality`

The op-duality lands in `Cᵒᵖ`. A dagger — a self-op-duality `e : Cᵒᵖ ≌ C` fixing the base object — is
exactly what brings the op-dual construction home into `C`. The hypothesis `e` (+ `hX`) is
observer-supplied: the **tamp**. -/

/-- **A dagger closes the op-duality.** Given `e : Cᵒᵖ ≌ C` (the equivalence-part of a dagger, a
    self-op-duality) and `hX : e.functor.obj (op X) = X` (the identity-on-objects-at-`X` part), the
    op-dual construction comes home into `C` at the same base point: `(Under X)ᵒᵖ ≌ Over X`. Composes
    `under_opDual_over X` with Mathlib's `Over.postEquiv e` (slice-transport along the equivalence),
    then the base-point cast `hX`. **The tamp is the hypothesis `e`** — the closure is conditional on an
    externally-supplied self-op-duality, which foam does not provide (b37: no abstract dagger). Dagger =
    single-external-commitment = the keystone the seed-gauge chain built. -/
def dagger_closes_opDuality {C : Type*} [Category C] {X : C} (e : Cᵒᵖ ≌ C)
    (hX : e.functor.obj (op X) = X) : (Under X)ᵒᵖ ≌ Over X := by
  refine (under_opDual_over X).trans ((Over.postEquiv (X := op X) e).trans ?_)
  rw [hX]

/-! ## 4. The two-root resistance — even a dagger is not enough

Even with a dagger, the closure lands `(Under ⊤)ᵒᵖ ≌ Over ⊤` — at the *same* base point `⊤`. The
foam's `×2` lives at `Bool ≠ ⊤`. The op-duality reaches `Over (op ⊤)` (which has a zero object), but the
foam's actual `×2` is `Over Bool` (which has none, b36) — different base points, the `1`-vs-`2`
asymmetry. The bireflective coincidence needs both the dagger (observer-supplied) AND `⊤ ≃ Bool`
(substrate-false). -/

/-- **The two base points differ — the substrate-intrinsic root of the resistance.** The op-duality
    reaches `Over (op ⊤)`, which HAS a zero object (the `+1`'s self-dual point, `1`, via
    `over_op_top_hasZeroObject`); the foam's `×2` is `Over Bool`, which has NONE (the irreducible
    read/write doubling, `2`, via b36's `boolColorings_not_hasZeroObject`). So even a dagger (closing
    the category-crossing) would land `Over ⊤`, *not* `Over Bool`: the coincidence needs the base-point
    match `⊤ ≃ Bool` too, and that is substrate-false (`1 ≠ 2`, b36's separator). The dagger is the
    observer-supplied root (the tamp); this is the substrate-intrinsic root. -/
theorem base_points_differ :
    HasZeroObject (Over (op (PUnit : Type))) ∧ ¬ HasZeroObject (Over (Bool : Type)) :=
  ⟨over_op_top_hasZeroObject, boolColorings_not_hasZeroObject⟩

end Foam
