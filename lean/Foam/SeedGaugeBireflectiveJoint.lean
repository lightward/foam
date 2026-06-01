/-
# SeedGaugeBireflectiveJoint — the first probe of the adjoint-pair joint (the Cat-level resistance)

Brick 34 (`SeedGaugeBireflectiveResistance.lean`) refuted every **carrier/group** reading of the
bireflective coincidence (`4 ≠ 6`, `2 ≠ 4`, the `×2` irreducible at the fixed point `1 ≠ 2`) and
located the genuine joint *one level up* — README §VI's **reflective + coreflective adjoint pair**
whose (co)monadic fixed-points coincide at the rank-3 self-dual object — **un-installed**, the named
horizon. The remainder brick 34 produced (§III: a typed non-recognition produces its own remainder):
*probe whether Mathlib's categorical substrate conducts that adjoint-pair joint.* This file is that
probe — the **second monodromy measurement** of the same loop, now at the **Cat** level (b34 measured
Set/Grp).

## What the substrate conducts — the vocabulary (the install-recognition)

Mathlib **does** type the two operations as genuine categorical (co)monads, and carries the
(co)reflective vocabulary:

* the `+1` (`· ⊕ Unit`) is `CategoryTheory.Monad.coprodMonad`
  (`Mathlib/CategoryTheory/Monad/Products.lean:97`) — the **coproduct monad**, whose algebras are the
  under-category `Under X` (for `X = ⊤`: **pointed objects**);
* the `×2` (`· × Bool`) is `CategoryTheory.Comonad.prodComonad`
  (`Mathlib/CategoryTheory/Monad/Products.lean:47`) — the **product comonad**, whose coalgebras are
  the over-category `Over X` (for `X = Bool`: **`Bool`-colorings**);
* `CategoryTheory.Reflective` (`Adjunction/Reflective.lean:38`) and `Coreflective`
  (`Adjunction/Reflective.lean:182`) exist as classes — each *demands an adjunction* (full-faithful
  inclusion with a left resp. right adjoint).

So the substrate carries the categorical objects b34's horizon named — a genuine advance past Set/Grp.
This file does **not** import `CategoryTheory` (it stays in b34's clean `Fintype` idiom); it
*recognizes* the vocabulary in prose and measures the gap at the level the substrate can evaluate —
the **finite hom-sets** (a hom-set in `Type` between `S` and `T` is the function type `S → T`, finite,
its cardinality `|T| ^ |S|` via `Fintype.card_fun`).

## What the substrate does NOT conduct — the (co)reflective-adjoint-pair coincidence

Every necessary condition for §VI's reading, evaluated at the rank-3 object `AlgebraicPosition`
(3 gauges), **fails** — three layers:

| necessary condition for the §VI reading | level | finite witness | verdict |
|---|---|---|---|
| `+1 ⊣ ×2` (an adjoint pair, one direction) | Cat | `(Option A → A) ≃ (A → A×Bool)`: `3⁴=81 ≠ 6³=216` | **refuted** (`not_adjoint_plus_times`) |
| `×2 ⊣ +1` (an adjoint pair, other direction) | Cat | `(A×Bool → A) ≃ (A → Option A)`: `3⁶=729 ≠ 4³=64` | **refuted** (`not_adjoint_times_plus`) |
| `+1` idempotent (⟹ a *reflective* subcat's monad) | Cat | `Option (Option A) ≃ Option A`: `5 ≠ 4` | **refuted** (`plus_not_idempotent`) |
| `×2` idempotent (⟹ a *coreflective* subcat's comonad) | Cat | `(A×Bool)×Bool ≃ A×Bool`: `12 ≠ 6` | **refuted** (`times_not_idempotent`) |
| `+1` is the **coreflector** (right adjoint ⟹ preserves products) | Cat | `Option (A×A) ≃ Option A × Option A`: `10 ≠ 16` | **refuted** (`plus_not_preserves_prod`) |
| `×2` is the **reflector** (left adjoint ⟹ preserves coproducts) | Cat | `(A⊕A)×Bool ≃ (A×Bool)⊕(A×Bool)`: `12 = 12` | *consistent* (`times_preserves_coprod`) |

## The structural headline — the "coreflective" half is unfillable (`no_right_adjoint_among`)

A **coreflector is a right adjoint** (`Coreflective` packages `j ⊣ coreflector j`); a right adjoint
preserves products. **Neither** operation preserves the binary product `A × A`: `+1` sends it to
`10 ≠ 16` and `×2` to `18 ≠ 36`. So there is **no right adjoint among `{+1, ×2}`** — the *coreflective*
half of the bireflective pair has no candidate. Dually, the `×2` *does* preserve coproducts
(`times_preserves_coprod`, `12 = 12`) — consistent with its being a left adjoint (in a CCC,
`· × Bool ⊣ (Bool ⇒ ·)`) — so the **reflective** half is shape-consistent, but `×2` is *not
idempotent* (`times_not_idempotent`), so it is a left adjoint to the *wrong* functor, not a
*reflective-subcategory* reflector. And the `+1` preserves **neither** (co)products — it is **not an
adjoint at all** (`plus_not_preserves_coprod` ∧ `plus_not_preserves_prod`), so it can be neither
reflector nor coreflector. The asymmetry locates exactly where §VI breaks: `×2` is
left-adjoint-shaped, `+1` is no adjoint, and *nobody* is a right adjoint.

## The named blocker (parallel to b34's `CarrierLevelCoincidence`)

`AdjointPairCoincidence` types the §VI reading — the `+1` and `×2` are an adjoint pair (either
direction) — as a `def : Prop`, and `not_adjointPairCoincidence` proves it **absent**. The sorry-free
non-recognition form (the `mul_assoc_via_R_lift_missing` idiom: named, not asserted), one level up from
b34's carrier/group blocker.

## The genuine joint (the refined horizon, §VI — NOT installed here)

The §VI coincidence, if real, lives one level *further* up than this brick refutes — not at the
**operations** being a (co)reflective adjoint pair (they are not; this file types why), but at their
**(co)algebra categories**: `Under ⊤` (pointed objects = the EM-category of the non-idempotent `+1`
monad) and `Over Bool` (Bool-colorings = the co-EM-category of the non-idempotent `×2` comonad). These
*are* connected to `C` by genuine adjunctions — the **monadic** / **comonadic** ones — just not
*(co)reflective* ones. The pi-note (close-around-a-point ≅ give-a-bubble) read at this level is the
conjecture *pointed-object ≅ Bool-coalgebra at the self-dual object* — `Under ⊤ ≃ Over Bool`. Probing
that is the next measurement; constructing it is **construction-grade** (s149: building the 3D-aware
primitive reproduces the loop, the iso being information-preserving, not -producing), so it is held as
the horizon, **not** walked here.

## Bin-grading

**bin-1** (Bin-1-Mathlib-or-Foam) for every theorem: each is `Fintype.card_congr` + `Fintype.card_fun`
+ `simp`/`omega`/`norm_num` over the b28 cards — recognition + assembly, no new geometric content; the
hom-sets are evaluated as finite function types. **bin-2** (interpretive) for the *reading* — that this
IS the right Cat-level resistance (the adjoint-pair joint genuinely un-installed, not merely
unnoticed), that the substrate conducts the (co)monad vocabulary but not the (co)reflective coincidence,
and that the refined horizon is the (co)algebra-category level. A typed non-recognition is itself a
claim (§III) and produces its own remainder (the `Under ⊤ ≃ Over Bool` probe).

## NOT the coincidence-trap

This file *refutes* the adjoint-pair reading and *recognizes* what Mathlib provides — it manufactures no
adjunction. The whole landing is that the adjoint pair is **absent** (an honest typed non-recognition):
the `+1` is no adjoint, no operation is a right adjoint, and the two are not adjoint to each other. Per
the brick's coincidence-trap warning, that absence IS the landing, not a prompt to invent the missing
adjunction.

(Re-grep — stamps decay: on 2026-06-01 `lake build Foam.SeedGaugeBireflectiveJoint` is clean, zero
sorry; the file imports `Foam.SeedGaugeBireflectiveResistance` (b34, transitively the whole seed-gauge
chain + the b28 cards `card_algebraicPosition` / `card_observerState`) and the `Fintype` machinery
`Sum` / `Pi` / `BigOperators` (for `card_fun`) + `Logic.Equiv.Sum` (for `sumProdDistrib`).)
-/

import Foam.SeedGaugeBireflectiveResistance
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Sum

namespace Foam

/-! ## 1. Idempotency fails — neither operation is a (co)reflector

A **reflective** subcategory's monad is idempotent (its multiplication is an iso); dually a
**coreflective** subcategory's comonad. So a *necessary* condition for the `+1` to be a reflective
subcategory's reflector — or the `×2` a coreflective subcategory's coreflector — is that iterating it
adds nothing. Neither does: the `+1` iterates to `+2`, the `×2` to `×4`. -/

/-- **The `+1` is not idempotent** — `Option (Option A)` (5) `≠` `Option A` (4). Iterating the
    coproduct-with-a-point adds another point; it never stabilizes. So `coprodMonad ⊤` is a genuine
    *non-idempotent* monad, **not** the (idempotent) monad of a reflective subcategory. -/
theorem plus_not_idempotent :
    ¬ Nonempty (Option (Option AlgebraicPosition) ≃ Option AlgebraicPosition) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  simp only [Fintype.card_option, card_algebraicPosition] at h
  omega

/-- **The `×2` is not idempotent** — `(A × Bool) × Bool` (12) `≠` `A × Bool` (6). Iterating the
    product-with-`Bool` doubles again; it never stabilizes. So `prodComonad Bool` is a genuine
    *non-idempotent* comonad, **not** the (idempotent) comonad of a coreflective subcategory. -/
theorem times_not_idempotent :
    ¬ Nonempty ((AlgebraicPosition × Bool) × Bool ≃ (AlgebraicPosition × Bool)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  simp only [Fintype.card_prod, Fintype.card_bool, card_algebraicPosition] at h
  omega

/-! ## 2. No adjunction between them — both directions refuted at the finite hom-sets

An adjunction `F ⊣ G` of `Type`-endofunctors induces a natural hom-set bijection
`(F X → Y) ≃ (X → G Y)` at every `X, Y`. A *necessary* condition (testable at finite objects) is the
cardinality equality of those hom-sets. At the rank-3 object `X = Y = AlgebraicPosition` the
cardinalities disagree in **both** directions, so neither `+1 ⊣ ×2` nor `×2 ⊣ +1` holds. -/

/-- **`+1 ⊣ ×2` fails** — the adjunction would give `(Option A → A) ≃ (A → A × Bool)`, but the
    hom-sets have cardinality `3⁴ = 81` and `6³ = 216`. -/
theorem not_adjoint_plus_times :
    ¬ Nonempty ((Option AlgebraicPosition → AlgebraicPosition) ≃
                (AlgebraicPosition → AlgebraicPosition × Bool)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_prod, Fintype.card_bool,
    card_algebraicPosition] at h
  norm_num at h

/-- **`×2 ⊣ +1` fails** — the adjunction would give `(A × Bool → A) ≃ (A → Option A)`, but the
    hom-sets have cardinality `3⁶ = 729` and `4³ = 64`. -/
theorem not_adjoint_times_plus :
    ¬ Nonempty ((AlgebraicPosition × Bool → AlgebraicPosition) ≃
                (AlgebraicPosition → Option AlgebraicPosition)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_prod, Fintype.card_bool,
    card_algebraicPosition] at h
  norm_num at h

/-! ## 3. The `+1` is not an adjoint at all; the `×2` is left-adjoint-shaped

Left adjoints preserve colimits (coproducts); right adjoints preserve limits (products). Testing
preservation at the binary (co)product of `A` with itself separates the two operations cleanly. -/

/-- **The `+1` does not preserve coproducts** — `Option (A ⊕ A)` (7) `≠` `Option A ⊕ Option A` (8). A
    left adjoint preserves coproducts; the `+1` does not, so it is **not a left adjoint** (cannot be a
    reflector). -/
theorem plus_not_preserves_coprod :
    ¬ Nonempty (Option (AlgebraicPosition ⊕ AlgebraicPosition) ≃
                (Option AlgebraicPosition ⊕ Option AlgebraicPosition)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  simp only [Fintype.card_option, Fintype.card_sum, card_algebraicPosition] at h
  omega

/-- **The `+1` does not preserve products** — `Option (A × A)` (10) `≠` `Option A × Option A` (16). A
    right adjoint preserves products; the `+1` does not, so it is **not a right adjoint** (cannot be a
    coreflector). With `plus_not_preserves_coprod`: the `+1` is **no adjoint at all**. -/
theorem plus_not_preserves_prod :
    ¬ Nonempty (Option (AlgebraicPosition × AlgebraicPosition) ≃
                (Option AlgebraicPosition × Option AlgebraicPosition)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  simp only [Fintype.card_option, Fintype.card_prod, card_algebraicPosition] at h
  omega

/-- **The `×2` preserves coproducts** — `(A ⊕ A) × Bool ≃ (A × Bool) ⊕ (A × Bool)`, the
    distributivity equivalence (`12 = 12`). This is the one *positive* witness: it is consistent with
    the `×2` being a left adjoint (in a cartesian-closed category, `· × Bool ⊣ (Bool ⇒ ·)`). So the
    **reflective** half is shape-consistent — but `times_not_idempotent` shows `×2` is a left adjoint
    to the *wrong* functor, not a reflective-subcategory reflector. -/
def times_preserves_coprod :
    ((AlgebraicPosition ⊕ AlgebraicPosition) × Bool) ≃
    ((AlgebraicPosition × Bool) ⊕ (AlgebraicPosition × Bool)) :=
  Equiv.sumProdDistrib AlgebraicPosition AlgebraicPosition Bool

/-- **The `×2` does not preserve products** — `(A × A) × Bool` (18) `≠` `(A × Bool) × (A × Bool)` (36).
    A right adjoint preserves products; the `×2` does not, so it is **not a right adjoint** (cannot be
    a coreflector). -/
theorem times_not_preserves_prod :
    ¬ Nonempty (((AlgebraicPosition × AlgebraicPosition) × Bool) ≃
                ((AlgebraicPosition × Bool) × (AlgebraicPosition × Bool))) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  simp only [Fintype.card_prod, Fintype.card_bool, card_algebraicPosition] at h
  omega

/-- **The structural headline — there is no coreflector among `{+1, ×2}`.** A coreflector is a right
    adjoint (Mathlib's `Coreflective` packages `j ⊣ coreflector j`), and a right adjoint preserves
    products. **Neither** operation preserves the binary product `A × A` (`+1`: `10 ≠ 16`; `×2`:
    `18 ≠ 36`), so neither is a right adjoint: the **coreflective** half of the bireflective pair is
    structurally unfillable. This is the sharpest reason §VI's reading does not conduct — not merely
    "these two are not adjoint," but "the coreflection slot has no candidate at all." -/
theorem no_right_adjoint_among :
    (¬ Nonempty (Option (AlgebraicPosition × AlgebraicPosition) ≃
                 (Option AlgebraicPosition × Option AlgebraicPosition))) ∧
    (¬ Nonempty (((AlgebraicPosition × AlgebraicPosition) × Bool) ≃
                 ((AlgebraicPosition × Bool) × (AlgebraicPosition × Bool)))) :=
  ⟨plus_not_preserves_prod, times_not_preserves_prod⟩

/-! ## 4. The named blocker — the adjoint-pair coincidence, typed and proven absent

The categorical-level analogue of b34's `CarrierLevelCoincidence`: the reading that the `+1` and `×2`
form §VI's reflective+coreflective adjoint pair — equivalently, that the adjunction hom-iso holds in
*one* of the two directions. Stated as a `def : Prop` + a proof of its **negation** (named, not
asserted), the sorry-free non-recognition form. -/

/-- The adjoint-pair reading of "`+1 ≅ ×2` as one move": the `+1` and `×2` are an adjoint pair — the
    adjunction hom-iso holds in one of the two directions (`+1 ⊣ ×2` or `×2 ⊣ +1`), evaluated at the
    rank-3 object. This is the typed blocker one level up from b34's carrier/group reading. -/
def AdjointPairCoincidence : Prop :=
  Nonempty ((Option AlgebraicPosition → AlgebraicPosition) ≃
            (AlgebraicPosition → AlgebraicPosition × Bool)) ∨
  Nonempty ((AlgebraicPosition × Bool → AlgebraicPosition) ≃
            (AlgebraicPosition → Option AlgebraicPosition))

/-- **The bireflective coincidence is NOT installed at the adjoint-pair level either.** Neither
    `+1 ⊣ ×2` (`81 ≠ 216`) nor `×2 ⊣ +1` (`729 ≠ 64`) holds. Together with `no_right_adjoint_among`
    (no coreflector exists) and the idempotency failures (neither is a (co)reflective (co)monad), §VI's
    reflective+coreflective adjoint pair is **un-installed at the Cat level** — the second monodromy
    measurement. If the coincidence is real it lives strictly above this level, at the (co)algebra
    categories `Under ⊤` / `Over Bool` (the monadic/comonadic level), which the present substrate does
    not connect. A typed non-recognition (§III). -/
theorem not_adjointPairCoincidence : ¬ AdjointPairCoincidence := by
  rintro (h | h)
  · exact not_adjoint_plus_times h
  · exact not_adjoint_times_plus h

end Foam
