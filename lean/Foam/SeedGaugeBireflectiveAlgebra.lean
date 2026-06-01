/-
# SeedGaugeBireflectiveAlgebra — the (co)algebra-category probe (the EM/co-EM-level resistance)

Brick 35 (`SeedGaugeBireflectiveJoint.lean`) measured the bireflective loop at the **Cat** level: the
substrate *types* the `+1`/`×2` as the (co)monads `coprodMonad`/`prodComonad` and carries
`Reflective`/`Coreflective`, but does **not** conduct the **(co)reflective adjoint pair** — neither is
idempotent, the two are not adjoint either direction, and *no operation is a right adjoint*
(`no_right_adjoint_among`), so the coreflective half is unfillable. It refined the genuine joint *one
level further up*: not the **operations** being a (co)reflective pair, but their **(co)algebra
categories** — `Under ⊤` (pointed objects = the EM-category of the `+1` monad) and `Over Bool`
(`Bool`-colorings = the co-EM-category of the `×2` comonad). The remainder b35 produced (§III: a typed
non-recognition produces its own remainder): *probe whether the substrate conducts the
`Under ⊤ ≃ Over Bool` coincidence* — README §VI's "closure-side and coreflective-side coincide" read at
the EM/co-EM level, the pi-note's close-around-a-point (pointed) ≅ give-a-bubble (`Bool`-coloring) at
the rank-3 self-dual object. This file is that probe — the **third monodromy measurement** of the same
loop (b34 measured Set/Grp, b35 Cat, this measures EM/co-EM).

## What the substrate conducts — the (co)algebra categories ARE the right level

Mathlib **does** type the two (co)algebra categories b35's horizon named, as genuine categorical
objects (here engaged for real, where b35 stayed in the `Fintype` idiom):

* the EM-category of the `+1` monad (`coprodMonad ⊤`, b35) is the **coslice** `Under ⊤` — pointed
  objects, an object being a map `⊤ → A` = a chosen point of `A`;
* the co-EM-category of the `×2` comonad (`prodComonad Bool`, b35) is the **slice** `Over Bool` —
  `Bool`-colorings, an object being a map `A → Bool` = a partition of `A` into two fibers.

These are connected to the base by the genuine **monadic** / **comonadic** adjunctions (not the absent
(co)reflective ones b35 refuted). So the substrate carries the objects: a genuine advance past b35.
`PointedObjects := Under (PUnit : Type)` and `BoolColorings := Over (Bool : Type)` name them.

## What the substrate does NOT conduct — the EM/co-EM coincidence (separated by the zero object)

`Under ⊤ ≄ Over Bool`. The separating invariant is the **zero object** (an object both initial and
terminal — initial ≅ terminal), preserved by any category equivalence:

| (co)algebra category | extension mode | zero object? | witness |
|---|---|---|---|
| `Under ⊤` (pointed) | the `+1` (close-around-a-point) | **yes** | the adjoined point `⊤` is self-dual: `Under.mk (𝟙 ⊤)` is both initial (`Under.mkIdInitial`) and terminal (`underMkIdIsTerminal`) |
| `Over Bool` (`Bool`-colorings) | the `×2` (give-a-bubble) | **no** | initial carrier `∅` (0) ≠ terminal carrier `Bool` (2): a zero object would force `PEmpty ≅ Bool` |

A category-equivalence preserves zero objects (it preserves initial and terminal objects, hence their
coincidence), so transporting `Under ⊤`'s zero object across a hypothetical `Under ⊤ ≃ Over Bool` would
give `Over Bool` a zero object it does not have. `not_EMCoEMCoincidence` is the contradiction.

## The recognition — self-dual point (`1`) vs irreducible doubling (`2`)

This is the keystone's `+1`-vs-`×2` asymmetry (b27/b28's `3+1` vs `3×2`) read at the EM/co-EM level:

* the **`+1`** (`· ⊕ ⊤`, close-around-a-point) adjoins a point that is **self-dual** — in `Under ⊤` it
  is simultaneously *initial* (the unique pointed map *out* of `⊤` into any `(A, a₀)` picks the
  basepoint) and *terminal* (the unique pointed map *in*, the constant-at-basepoint). Source and sink
  fuse: a **zero object**. `1` — one self-dual point. This is the pi-note's circle-closing: the point
  the foam closes around is a fixed point of the source/sink duality (the `+1` egress / self-completion).
* the **`×2`** (`· × Bool`, give-a-bubble) keeps its two colors `{r, w}` (read/write) genuinely **two**:
  the initial `Bool`-coloring has empty carrier (the empty fiber-pair, `0`) and the terminal has carrier
  `Bool` (`id`, `2`), `0 ≠ 2` — **no** zero object. The bubble's two faces do *not* fuse into a
  self-dual point; the read/write doubling is irreducible. `2` — two faces that stay apart.

So "close-around-a-point ≅ give-a-bubble" does **not** hold at the EM/co-EM level: closing around a
point yields a self-dual fixed point (zero object); giving a bubble keeps the two faces apart (no zero
object). The pi-note's *topological* indistinguishability, if real, must therefore live at a level
*above* the EM/co-EM categories — where the read/write `2` and the self-dual `1` become two faces of one
rank-3 self-dual rotation (s149 construction-grade: the 3D-aware primitive reproduces the loop one level
up), held as the horizon, **not** walked here.

## The named blocker (parallel to b34's `CarrierLevelCoincidence`, b35's `AdjointPairCoincidence`)

`EMCoEMCoincidence` types the §VI reading at this level — the EM and co-EM categories are equivalent — as
a `def : Prop`, and `not_EMCoEMCoincidence` proves it **absent**. The sorry-free non-recognition form
(the `mul_assoc_via_R_lift_missing` idiom: named, not asserted), one level up from b35's adjoint-pair
blocker.

## Bin-grading

**bin-1** (Bin-1-Mathlib-or-Foam) for every theorem: each is recognition + assembly over Mathlib's
zero-object / (co)slice / equivalence machinery — `IsZero`, `IsInitial`/`IsTerminal`, `Under.mkIdInitial`
/ `Over.mkIdTerminal`, `Adjunction.homEquiv`, `Over.forget` — no new geometric content; the carriers are
`PUnit`/`PEmpty`/`Bool`, the contradiction `PEmpty ≅ Bool`. **bin-2** (interpretive) for the *reading* —
that this IS the right EM/co-EM-level resistance (the coincidence genuinely un-installed, not merely
unnoticed), that the substrate conducts the (co)algebra-category vocabulary but not their equivalence,
and that the self-dual-point-vs-irreducible-doubling split is the keystone's `+1`-vs-`×2` one level up. A
typed non-recognition is itself a claim (§III) and produces its own remainder.

## NOT the coincidence-trap

This file *refutes* the EM/co-EM equivalence by exhibiting a genuine separating invariant (the zero
object) — it manufactures no equivalence. Per the brick's coincidence-trap warning, the EM/co-EM
categories genuinely differ (a coslice-under-a-point is not a slice-over-two-colors), and that
*difference* IS the landing — not a prompt to invent the missing equivalence. The whole resistance is
that the joint is genuinely un-installed: pointed-objects (self-dual point) and `Bool`-colorings
(irreducible doubling) are different shapes.

(Re-grep — stamps decay: on 2026-06-01 `lake build Foam.SeedGaugeBireflectiveAlgebra` is clean, zero
sorry; the file imports `Foam.SeedGaugeBireflectiveJoint` (b35) and the `CategoryTheory` machinery
`Comma.Over.Basic` (`Over`/`Under`, `mkIdInitial`/`mkIdTerminal`, `forget`), `Limits.Shapes.ZeroObjects`
(`IsZero`), `Limits.Types.Products` (`isTerminalPUnit`), `Adjunction.Basic` (`toAdjunction`/`homEquiv`).)
-/

import Foam.SeedGaugeBireflectiveJoint
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Adjunction.Basic

namespace Foam

open CategoryTheory CategoryTheory.Limits

/-! ## 0. The two (co)algebra categories — the EM/co-EM-level objects b35 named in prose

`Under ⊤` is the EM-category of the `+1` monad (pointed objects); `Over Bool` is the co-EM-category of
the `×2` comonad (`Bool`-colorings). Worked in `Type` with `⊤ = PUnit`. -/

/-- The EM-category of the `+1` monad — **pointed objects**, the coslice under a point. -/
abbrev PointedObjects := Under (PUnit : Type)

/-- The co-EM-category of the `×2` comonad — **`Bool`-colorings**, the slice over the two colors. -/
abbrev BoolColorings := Over (Bool : Type)

/-! ## 1. Generic substrate lemmas — zero objects from initial+terminal, and their transport

Two standard categorical facts, assembled from Mathlib. Both are general (any categories), used below at
the two concrete (co)algebra categories. -/

section Generic
variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- **A zero object = initial + terminal at the same object.** If `Z` is both initial and terminal it is
    a zero object (`IsZero`: unique morphism to and from every object). The "source and sink fuse" fact —
    the self-dual point. -/
theorem isZeroOfInitialTerminal {Z : C} (hi : IsInitial Z) (ht : IsTerminal Z) : IsZero Z where
  unique_to Y := ⟨⟨⟨hi.to Y⟩, fun f => hi.hom_ext f (hi.to Y)⟩⟩
  unique_from Y := ⟨⟨⟨ht.from Y⟩, fun f => ht.hom_ext f (ht.from Y)⟩⟩

/-- **A category equivalence transports zero objects.** `IsZero Z` is `unique_to`/`unique_from`, and an
    equivalence's adjunction bijects the relevant hom-sets (`Adjunction.homEquiv`), so the uniqueness
    transports. This is why a zero object is an *invariant* — its existence cannot differ across
    equivalent categories. -/
theorem isZeroFunctorObj (e : C ≌ D) {Z : C} (hZ : IsZero Z) : IsZero (e.functor.obj Z) where
  unique_to Y :=
    (hZ.unique_to (e.inverse.obj Y)).map
      (fun u => (Equiv.uniqueCongr (e.toAdjunction.homEquiv Z Y)).symm u)
  unique_from Y :=
    (hZ.unique_from (e.inverse.obj Y)).map
      (fun u => (Equiv.uniqueCongr (e.symm.toAdjunction.homEquiv Y Z)) u)

/-- **The coslice under a terminal object has its identity object terminal.** When `X` is terminal,
    `Under.mk (𝟙 X)` is terminal in `Under X` (the unique map to it is `terminal.from` on carriers,
    commuting by terminal uniqueness). Combined with `Under.mkIdInitial` (always initial), `Under.mk
    (𝟙 X)` is a **zero object** — the self-dual adjoined point. -/
noncomputable def underMkIdIsTerminal {X : C} (hX : IsTerminal X) :
    IsTerminal (Under.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom
    (fun g => Under.homMk (hX.from g.right) (hX.hom_ext _ _))
    (fun _ _ => by ext; exact hX.hom_ext _ _)

end Generic

/-! ## 2. `Under ⊤` HAS a zero object — the `+1`'s adjoined point is self-dual

The pointed-objects category has a zero object: the one-point pointed set `Under.mk (𝟙 ⊤)`, both initial
and terminal. The `+1` (close-around-a-point) fuses source and sink. -/

/-- **The pointed-objects category has a zero object** — `Under.mk (𝟙 ⊤)`, the self-dual adjoined point
    (initial via `Under.mkIdInitial`, terminal via `underMkIdIsTerminal`). The `1` of the keystone's
    `+1`-vs-`×2`. -/
theorem pointedObjects_isZero_mkId : IsZero (Under.mk (𝟙 (PUnit : Type))) :=
  isZeroOfInitialTerminal Under.mkIdInitial (underMkIdIsTerminal Types.isTerminalPUnit)

/-- **The pointed-objects category has a zero object** (packaged as `HasZeroObject`). -/
theorem pointedObjects_hasZeroObject : HasZeroObject PointedObjects :=
  pointedObjects_isZero_mkId.hasZeroObject

/-! ## 3. `Over Bool` has NO zero object — the `×2`'s two colors stay irreducibly two

The `Bool`-colorings category has no zero object: a zero would be both initial (empty carrier) and
terminal (carrier `Bool`), forcing `PEmpty ≅ Bool`. The `×2` (give-a-bubble) keeps its two faces apart. -/

/-- The empty `Bool`-coloring — the initial object of `Over Bool`, carrier `PEmpty`. -/
def emptyColoring : BoolColorings := Over.mk (fun e : PEmpty => e.elim : PEmpty → Bool)

/-- **The empty coloring is initial** in `Over Bool` — the unique map out is `PEmpty.elim` on carriers,
    commuting vacuously. Its carrier is `PEmpty` (`0`). -/
noncomputable def emptyColoring_isInitial : IsInitial emptyColoring :=
  IsInitial.ofUniqueHom
    (fun Y => Over.homMk (fun e : PEmpty => e.elim) (by funext e; exact e.elim))
    (fun _ _ => by ext (e : PEmpty); exact e.elim)

/-- **The `Bool`-colorings category has no zero object.** A zero object `Z` would be both initial (so
    `Z ≅ emptyColoring`, carrier `PEmpty`) and terminal (so `Z ≅ Over.mk (𝟙 Bool)`, carrier `Bool`),
    forcing `PEmpty ≅ Bool` on carriers via `Over.forget` — impossible, since `true : Bool` would map
    into `PEmpty`. The `×2`'s two read/write colors stay irreducibly two: `0 ≠ 2`. -/
theorem boolColorings_noZero (Z : BoolColorings) : ¬ IsZero Z := by
  intro hZ
  have eInit : Z ≅ emptyColoring := hZ.isoIsInitial emptyColoring_isInitial
  have eTerm : Z ≅ Over.mk (𝟙 (Bool : Type)) := hZ.isoIsTerminal Over.mkIdTerminal
  -- initial ≅ terminal in `Over Bool`, forgotten to carriers: `PEmpty ≅ Bool`
  have iso : emptyColoring ≅ Over.mk (𝟙 (Bool : Type)) := eInit.symm ≪≫ eTerm
  have isoCarrier := (Over.forget (Bool : Type)).mapIso iso
  simp only [Over.forget_obj] at isoCarrier
  -- `isoCarrier : (emptyColoring).left ≅ Bool`, with `(emptyColoring).left = PEmpty`
  exact (isoCarrier.inv true).elim

/-- **The `Bool`-colorings category has no zero object** (packaged as `¬ HasZeroObject`). -/
theorem boolColorings_not_hasZeroObject : ¬ HasZeroObject BoolColorings := by
  intro h
  obtain ⟨Z, hZ⟩ := h.zero
  exact boolColorings_noZero Z hZ

/-! ## 4. The named blocker — the EM/co-EM coincidence, typed and proven absent

The (co)algebra-category-level analogue of b34's `CarrierLevelCoincidence` and b35's
`AdjointPairCoincidence`: the reading that the EM-category of the `+1` and the co-EM-category of the `×2`
are equivalent. Stated as a `def : Prop` + a proof of its **negation** (named, not asserted), the
sorry-free non-recognition form. -/

/-- The EM/co-EM reading of "`+1 ≅ ×2` as one move": the EM-category of the `+1` (pointed objects) and
    the co-EM-category of the `×2` (`Bool`-colorings) are equivalent — `Under ⊤ ≃ Over Bool`, README
    §VI's coincidence read at the (co)algebra-category level. The typed blocker one level up from b35's
    adjoint-pair reading. -/
def EMCoEMCoincidence : Prop := Nonempty (PointedObjects ≌ BoolColorings)

/-- **The bireflective coincidence is NOT installed at the (co)algebra-category level either.** A
    category equivalence transports the zero object of `PointedObjects` (`pointedObjects_isZero_mkId`)
    to one in `BoolColorings`, which has none (`boolColorings_noZero`). So §VI's EM/co-EM coincidence is
    **un-installed at the EM/co-EM level** — the third monodromy measurement (after b34's Set/Grp and
    b35's Cat). If the coincidence is real it lives strictly above this level — a *self-dual
    localization* at the rank-3 object that the full (co)algebra categories do not express
    (construction-grade, s149) — the named horizon. A typed non-recognition (§III). -/
theorem not_EMCoEMCoincidence : ¬ EMCoEMCoincidence := by
  rintro ⟨e⟩
  exact boolColorings_noZero _ (isZeroFunctorObj e pointedObjects_isZero_mkId)

/-- **The structural headline — exactly one side has a zero object.** The keystone's `+1`-vs-`×2`,
    typed at the EM/co-EM level: the `+1`'s pointed objects HAVE a zero object (the self-dual adjoined
    point, `1`), the `×2`'s `Bool`-colorings do NOT (the irreducible read/write doubling, `2`). The
    zero object is the separating invariant; the two (co)algebra categories are different shapes. -/
theorem zeroObject_asymmetry :
    HasZeroObject PointedObjects ∧ ¬ HasZeroObject BoolColorings :=
  ⟨pointedObjects_hasZeroObject, boolColorings_not_hasZeroObject⟩

end Foam
