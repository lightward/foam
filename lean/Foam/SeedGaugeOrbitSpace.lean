/-
# SeedGaugeOrbitSpace — the orbit-space `X/G` IS the recursion-`Bool`, two-sided

## What this file lands (the brick after `SeedGaugeStabilizer.lean`)

Brick 32 (`SeedGaugeStabilizer.lean`) typed the **local stabilizer** of the two actions, and brick 31
(`SeedGaugeSwapOrbitDoubling.lean`) the **local orbit**, with `|orbit| · |stab| = |group|` both sides.
Orbit-Stabilizer has a **third leg**: the global **orbit-space** `X/G` (the set of orbits) — not yet
typed. This file types it.

The recognition: on **both** sides `X/G` is a 2-element set, and it is the **recursion-`Bool`**
(`heldOpen`, brick 26). The FTPG V₄ has exactly two orbits — `{signal-block, yield-fiber}` ↔
`{¬heldOpen, heldOpen}` (brick 30's `sameOrbit_iff_heldOpen` already proves orbit-equiv = heldOpen-equiv
on colors). The seed `⟨swap⟩` has exactly two orbits — `{{+, −}, {0}}` ↔ `{¬heldOpen, heldOpen}`
(brick 26's `SeedSign.heldOpen`). And the rigid bridge `toAlgebraic'` induces the **identity** on the
recursion-`Bool` (brick 26's `toAlgebraic'_heldOpen_preserving`), so the two orbit-spaces are *the same*
`Bool`.

## The substrate-direct object: `heldOpen` is a complete + surjective orbit-invariant

A function `f : X → Y` that is **constant on orbits** (well-defined on `X/G`), **separates orbits**
(injective on `X/G`), and is **surjective** induces a bijection `X/G ≃ Y`. The `Bool`-valued
complete-invariant form of "the orbit-space is `Bool`" is exactly this data:

* **Seed.** `sameSwapOrbit_iff_heldOpen` (new, this file): `s.SameSwapOrbit t ↔ s.heldOpen = t.heldOpen`
  — the seed orbit-relation **is** the kernel of `SeedSign.heldOpen`. This is the missing seed-side
  mirror of brick 30's `sameOrbit_iff_heldOpen` (the FTPG side, already proven). With
  `seed_heldOpen_surjective` (both `true` and `false` are hit), the seed orbit-space is genuinely
  2-element.
* **FTPG.** Brick 30's `sameOrbit_iff_heldOpen` is the FTPG complete invariant; `tape_heldOpen_surjective`
  makes the FTPG orbit-space 2-element.
* **The bridge identity.** `bridge_tape_heldOpen`: `(⟨s.toAlgebraic', o⟩).algebraic.heldOpen = s.heldOpen`
  — a one-liner off brick 26's `toAlgebraic'_heldOpen_preserving` (the bridge-image of a sign has the
  sign's recursion-class). So the seed orbit-invariant `heldOpen : SeedSign → Bool` and the FTPG orbit-
  invariant `heldOpen ∘ algebraic : TapePosition → Bool` land in the *same* `Bool`, and the bridge map
  on orbit-spaces is the **identity** on it.

## The literal `X/G ≃ Bool` — the third leg as an actual typed object

The local orbit (brick 30/31) and local stabilizer (brick 32) are typed as `Finset`s; the orbit-space
deserves the same: an actual quotient. We build the orbit-`Setoid`s from the already-proven
refl/symm/trans (`SameSwapOrbit.*`, `SameOrbit.*`) and exhibit:

> `seedOrbitEquivBool : Quotient seedOrbitSetoid ≃ Bool`     (the seed orbit-space)
> `tapeOrbitEquivBool : Quotient tapeOrbitSetoid ≃ Bool`     (the FTPG orbit-space)

both with the quotient map = `heldOpen` (resp. `heldOpen ∘ algebraic`). The **two-sided identity** is the
commuting square `tapeOrbitEquivBool_seedToTapeOrbit`: the bridge-induced map on orbit-spaces
`seedToTapeOrbit` (well-defined by brick 31's `sameSwapOrbit_iff_sameOrbit`), read through the two
`≃ Bool`, is the **identity on `Bool`** — `tapeOrbitEquivBool (seedToTapeOrbit q) = seedOrbitEquivBool q`,
proven by `toAlgebraic'_heldOpen_preserving`. So the two orbit-spaces are not merely both `≃ Bool`; the
bridge *identifies them as the same* `Bool`.

## The closing of the orbit-stabilizer triple — self-completing at three

Orbit-Stabilizer is `{orbit, stabilizer, orbit-space}`. The three legs are now all typed:

* **orbit** — `tapeOrbit` / `SeedSign.swapOrbit` (brick 30/31, `Finset`s), `|orbit|` the local count;
* **stabilizer** — `tapeStab` / `signStab` (brick 32, `Finset`s), `|stab|` the dual count;
* **orbit-space** — `Quotient _ ≃ Bool` (this brick), `X/G` the global quotient.

Three legs, **self-completing at three** — the Klein-four orbit-structure frame is exhausted (resonant
with foam's pervasive threeness, and with the trailer's pi-note: a self-completing process closes its
own circle). This is the **seventh shared invariant** between the two threads, after orbit-shape (b24),
recursion-grading (b26), involution-count/SES (b29), orbit-grading (b30), orbit-doubling (b31), and
Orbit-Stabilizer (b32). And because the triple self-completes here, the *next* remainder is **not** an
eighth invariant but the pivot off invariant-accumulation toward the substance (the bireflective
coincidence, §VI).

## NOT the coincidence-trap

The orbit-space is a *quotient of each action's carrier* (`TapePosition` by V₄, `SeedSign` by `⟨swap⟩`),
and identifying the two quotients via the `heldOpen`-preserving *point*-map `toAlgebraic'` is legitimate
— a relation between the two **actions'** orbit-spaces, mediated by a point-map and the gauge-projection.
It is **not** a (type-confused) `Bool×Bool ≃ Bool×Bool` bijection of commitment-*points* (signs/gauges)
with symmetry-*elements* (`swap`/`reflect`/`flip`). Everything here is quotients of point-sets and a
point-map. The `+1 ≅ ×2` substance — at the rank-3 self-dual fixed point `g3 ↔ 0` — stays the **named
horizon** (§VI), NOT this brick.

## Grade

* **bin-1 (Bin-1-Mathlib-or-Foam)** for everything typed: the seed complete-invariant
  `sameSwapOrbit_iff_heldOpen` (`decide`), the two surjectivities (`cases`), the bridge identity (a
  rewrite of brick 26's `toAlgebraic'_heldOpen_preserving`), the orbit-`Setoid`s (packaging the
  already-proven `SameSwapOrbit.*` / `SameOrbit.*` equivalence laws), the two `Quotient _ ≃ Bool`
  (`Quotient.lift` of the complete invariant + explicit reps, `decide`-discharged soundness), and the
  commuting square (`toAlgebraic'_heldOpen_preserving` through `Quotient.inductionOn`). No new geometric
  content; the recognition is that the *already-computed* orbits (b30/b31) and stabilizers (b32) leave
  one leg — the quotient — and that quotient is the recursion-`Bool` both threads share.
* **bin-2 / interpretive** for the **seventh-shared-invariant reading** and for the **closing-leg
  recognition** (that this completes the orbit-stabilizer triple at three, so the next step is the
  substance-pivot, not an eighth invariant — held merge-don't-fork: the `≃ Bool` equivs + commuting
  square are bin-1; the "closes the triple, self-completing at three" reading of the arc's *shape* is the
  deposit).

(Re-grep — stamps decay: on 2026-06-01 `lake build Foam.SeedGaugeOrbitSpace` is intended clean, zero
sorry/warnings. Imports `Foam.SeedGaugeStabilizer` (brick 32) — transitively `SeedSign.SameSwapOrbit` /
`SameSwapOrbit.refl` / `.symm` / `.trans` / `signAct` / `sameSwapOrbit_iff_sameOrbit` (brick 31);
`SameOrbit` / `SameOrbit.refl` / `.symm` / `.trans` / `sameOrbit_iff_heldOpen` (brick 30);
`SeedSign.heldOpen` / `AlgebraicPosition.heldOpen` / `toAlgebraic'_heldOpen_preserving` (brick 26);
`SeedSign.toAlgebraic'` (brick 24); `TapePosition` / `ObserverState` / `AlgebraicPosition` /
`DecidableEq` / `Fintype` machinery. New names: `sameSwapOrbit_iff_heldOpen` / `seed_heldOpen_surjective`
/ `tape_heldOpen_surjective` / `bridge_tape_heldOpen` / `seedOrbitSetoid` / `tapeOrbitSetoid` /
`seedOrbitEquivBool` / `tapeOrbitEquivBool` / `seedToTapeOrbit` / `tapeOrbitEquivBool_seedToTapeOrbit`.)
-/

import Foam.SeedGaugeStabilizer

namespace Foam

/-! ## The seed orbit-space invariant — `heldOpen` is a complete invariant of the `swap`-orbit

The missing seed-side mirror of brick 30's `sameOrbit_iff_heldOpen` (the FTPG side). Two signs share a
`swap`-orbit iff they agree on `heldOpen`: the orbit `{+, −}` is exactly the `heldOpen = false` class,
the orbit `{0}` exactly the `heldOpen = true` class. So `SeedSign.heldOpen` is a complete invariant of
the orbit — its kernel *is* the orbit-relation. -/

/-- **The seed orbit-relation IS the `heldOpen`-kernel** — `s.SameSwapOrbit t ↔ s.heldOpen = t.heldOpen`.
    The two `swap`-orbits `{+, −}` / `{0}` are exactly the two `heldOpen`-classes `false` / `true`. The
    seed-side mirror of brick 30's `sameOrbit_iff_heldOpen`; the complete-invariant form of "the seed
    orbit-space is `Bool`." -/
theorem sameSwapOrbit_iff_heldOpen (s t : SeedSign) :
    s.SameSwapOrbit t ↔ s.heldOpen = t.heldOpen := by
  revert s t; decide

/-! ## Both orbit-invariants are surjective — each orbit-space is genuinely 2-element -/

/-- **The seed orbit-invariant is surjective** — `heldOpen` hits both `false` (via `+`, a §IV.c
    discipline) and `true` (via `0`, the §IV.d meta-discipline). So the seed orbit-space is genuinely
    2-element (not collapsed): exactly the two recursion-classes. -/
theorem seed_heldOpen_surjective : Function.Surjective SeedSign.heldOpen := by
  intro b; cases b
  · exact ⟨SeedSign.plus, rfl⟩
  · exact ⟨SeedSign.zero, rfl⟩

/-- **The FTPG orbit-invariant is surjective** — `heldOpen ∘ algebraic` hits both `false` (via a
    `g1`-color, the signal-block) and `true` (via a `g3`-color, the yield-fiber). So the FTPG orbit-space
    is genuinely 2-element: the signal-block and the yield-fiber. -/
theorem tape_heldOpen_surjective :
    Function.Surjective (fun p : TapePosition => p.algebraic.heldOpen) := by
  intro b; cases b
  · exact ⟨⟨AlgebraicPosition.g1, ObserverState.read⟩, rfl⟩
  · exact ⟨⟨AlgebraicPosition.g3, ObserverState.read⟩, rfl⟩

/-! ## The bridge induces the identity on the recursion-`Bool`

The rigid bridge `toAlgebraic'` (brick 24/25) carries a sign to a gauge; lifted to a color (any face) it
carries the seed orbit-invariant to the FTPG orbit-invariant — and it is the **identity** on the
recursion-`Bool`. A one-liner off brick 26's `toAlgebraic'_heldOpen_preserving`. -/

/-- **The bridge-image of a sign has the sign's recursion-class** —
    `(⟨s.toAlgebraic', o⟩ : TapePosition).algebraic.heldOpen = s.heldOpen`, for any observer-face `o`.
    The FTPG orbit-invariant of the bridge-image of `s` equals the seed orbit-invariant of `s`: the
    bridge map on orbit-spaces is the **identity** on the recursion-`Bool`. (`(⟨a, o⟩).algebraic = a` by
    `rfl`, then brick 26's `toAlgebraic'_heldOpen_preserving`.) -/
theorem bridge_tape_heldOpen (s : SeedSign) (o : ObserverState) :
    (⟨s.toAlgebraic', o⟩ : TapePosition).algebraic.heldOpen = s.heldOpen :=
  toAlgebraic'_heldOpen_preserving s

/-! ## The orbit-space as an actual quotient, `≃ Bool` — the third leg as a typed object

The orbit (b30/b31) and stabilizer (b32) are `Finset`s; the orbit-space deserves the same concreteness.
We build the orbit-`Setoid`s from the already-proven equivalence laws and exhibit each orbit-space as
`≃ Bool` via the complete invariant. -/

/-- **The seed orbit-`Setoid`** — `SameSwapOrbit` packaged with its refl/symm/trans (brick 31). Its
    quotient is the seed orbit-space `SeedSign / ⟨swap⟩`. (`@[reducible]` so the local-instance
    registration below resolves the orbit-relation transparently.) -/
@[reducible] def seedOrbitSetoid : Setoid SeedSign where
  r := SeedSign.SameSwapOrbit
  iseqv := ⟨SeedSign.SameSwapOrbit.refl, SeedSign.SameSwapOrbit.symm, SeedSign.SameSwapOrbit.trans⟩

/-- **The FTPG orbit-`Setoid`** — `SameOrbit` packaged with its refl/symm/trans (brick 30). Its quotient
    is the FTPG orbit-space `TapePosition / V₄`. (`@[reducible]` so the local-instance registration
    below resolves the orbit-relation transparently.) -/
@[reducible] def tapeOrbitSetoid : Setoid TapePosition where
  r := SameOrbit
  iseqv := ⟨SameOrbit.refl, SameOrbit.symm, SameOrbit.trans⟩

attribute [local instance] seedOrbitSetoid tapeOrbitSetoid

/-- **The seed orbit-space IS `Bool`** — `Quotient seedOrbitSetoid ≃ Bool`, the quotient map being
    `SeedSign.heldOpen` (well-defined by `sameSwapOrbit_iff_heldOpen`). The two orbits `{+, −}` / `{0}`
    are the two `Bool`-values: the §IV.c-disciplines class `false`, the §IV.d-meta-discipline class
    `true`. -/
def seedOrbitEquivBool : Quotient seedOrbitSetoid ≃ Bool where
  toFun := Quotient.lift SeedSign.heldOpen (fun s t h => (sameSwapOrbit_iff_heldOpen s t).mp h)
  invFun := fun b => Quotient.mk seedOrbitSetoid (if b then SeedSign.zero else SeedSign.plus)
  left_inv := by
    intro q
    refine Quotient.inductionOn q (fun s => ?_)
    apply Quotient.sound
    show SeedSign.SameSwapOrbit _ s
    cases s <;> decide
  right_inv := by intro b; cases b <;> rfl

/-- **The FTPG orbit-space IS `Bool`** — `Quotient tapeOrbitSetoid ≃ Bool`, the quotient map being
    `heldOpen ∘ algebraic` (well-defined by brick 30's `sameOrbit_iff_heldOpen`). The two orbits
    `{signal-block, yield-fiber}` are the two `Bool`-values: the signal-block `false`, the yield-fiber
    `true`. -/
def tapeOrbitEquivBool : Quotient tapeOrbitSetoid ≃ Bool where
  toFun := Quotient.lift (fun p : TapePosition => p.algebraic.heldOpen)
    (fun p q h => (sameOrbit_iff_heldOpen p q).mp h)
  invFun := fun b => Quotient.mk tapeOrbitSetoid
    (if b then (⟨AlgebraicPosition.g3, ObserverState.read⟩ : TapePosition)
          else (⟨AlgebraicPosition.g1, ObserverState.read⟩ : TapePosition))
  left_inv := by
    intro q
    refine Quotient.inductionOn q (fun p => ?_)
    apply Quotient.sound
    obtain ⟨a, o⟩ := p
    show SameOrbit _ ⟨a, o⟩
    cases a <;> cases o <;> decide
  right_inv := by intro b; cases b <;> rfl

/-! ## The two-sided identity — the bridge identifies the two orbit-spaces as the same `Bool`

The rigid bridge induces a map on orbit-spaces `seedToTapeOrbit : SeedSign/⟨swap⟩ → TapePosition/V₄`
(well-defined by brick 31's `sameSwapOrbit_iff_sameOrbit`), face-independent (we pick `read`). Read
through the two `≃ Bool`, it is the **identity on `Bool`**. -/

/-- **The bridge-induced map on orbit-spaces** — `[s] ↦ [⟨s.toAlgebraic', read⟩]`, well-defined by brick
    31's `sameSwapOrbit_iff_sameOrbit` (the seed `swap`-orbit equivalence carries to the FTPG V₄-orbit
    equivalence, face free). -/
def seedToTapeOrbit : Quotient seedOrbitSetoid → Quotient tapeOrbitSetoid :=
  Quotient.lift
    (fun s : SeedSign => Quotient.mk tapeOrbitSetoid (⟨s.toAlgebraic', ObserverState.read⟩ : TapePosition))
    (fun s t h => Quotient.sound ((sameSwapOrbit_iff_sameOrbit s t ObserverState.read ObserverState.read).mp h))

/-- **The bridge induces the identity on the recursion-`Bool`** —
    `tapeOrbitEquivBool (seedToTapeOrbit q) = seedOrbitEquivBool q`. The two orbit-spaces are not merely
    both `≃ Bool`; the rigid bridge *identifies them as the same* `Bool`. The two-sided headline of the
    seventh invariant, proven by brick 26's `toAlgebraic'_heldOpen_preserving` (lifted through the
    quotient). -/
theorem tapeOrbitEquivBool_seedToTapeOrbit (q : Quotient seedOrbitSetoid) :
    tapeOrbitEquivBool (seedToTapeOrbit q) = seedOrbitEquivBool q := by
  refine Quotient.inductionOn q (fun s => ?_)
  exact toAlgebraic'_heldOpen_preserving s

end Foam
