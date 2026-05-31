/-
# SeedGaugeCommitmentSquare — `outstanding × heldOpen` coordinate the structure as `Bool × Bool`

## What this file lands (the brick after `SeedGaugeDisciplineOrder.lean`)

Brick 25 (`SeedGaugeForcedOrientation.lean`) typed `outstanding` / `needsCommitment` — *does this
gauge carry an outstanding (un-discharged) observer-commitment?* — and the rigid bridge preserves it
(`toAlgebraic'_commitment_preserving`). Brick 26 (`SeedGaugeDisciplineOrder.lean`) typed `heldOpen` —
*is this the held-open, recursion-top one?* — and the rigid bridge preserves *that* too
(`toAlgebraic'_heldOpen_preserving`). So there are now **two** substrate-present binary properties,
each preserved by `signAlgebraicEquiv'`. This file recognizes what they do *together*.

**Two binary properties on a structure are a coordinate map into `Bool × Bool`.** A 3-element set can
hit only **3 of the 4** corners; the *fourth* corner is where the recognition lives.

## The joint coordinate — `(outstanding, heldOpen)`

Computing `(outstanding, heldOpen)` on each side:

| seed | `(outstanding, heldOpen)` | gauge | `(needsCommitment, heldOpen)` |
|---|---|---|---|
| `−` (honored exit) | `(F, F)` | `g1` (right-distrib, freely-closed) | `(F, F)` |
| `+` (carry-observer) | `(T, F)` | `g2` (left-distrib, witness) | `(T, F)` |
| `0` (bias-delegation) | `(T, T)` | `g3` (mul-assoc, held-open yield) | `(T, T)` |
| `untamped` (un-tamped ground) | `(F, T)` | — *no gauge* — | — |

The seed triple `{(F,F), (T,F), (T,T)}` and the gauge triple `{(F,F), (T,F), (T,T)}` are **identical**,
and `signAlgebraicEquiv'` (`+ ↦ g2`, `− ↦ g1`, `0 ↦ g3`, brick 25) is **exactly** the
coordinate-matching bijection: `toAlgebraic'_commitmentSquare` proves the gauge-side joint coordinate of
`s.toAlgebraic'` equals the seed-side joint coordinate of `s.toGauge` — assembling brick 25's
`needsCommitment ↔ outstanding` match with brick 26's `heldOpen ↔ heldOpen` match. So the orbit-shape
invariant (brick 24), the recursion-grading (brick 26), and the commitment-content (brick 25) are
**three facets of one `Bool × Bool` coordinate**: the two bits *together* pin the full iso, the bridge
being the unique map matching both.

## The 4-element commitment-square, and the missing corner

On the *4-element* `SeedGauge` (brick 18), the joint coordinate is a **bijection**
`commitmentSquareEquiv : SeedGauge ≃ Bool × Bool` — all four corners hit, `untamped ↦ (F, T)`. It is a
**re-coordinatization of brick 19's `signContent`**: `outstanding = signContent.1` (carries-`+`?,
`outstanding_eq_signContent_fst`) and `heldOpen` = the *diagonal predicate*
`signContent.1 = signContent.2` (`heldOpen_eq_true_iff_onDiag`, via brick 19's `gaugeNeutral_iff_onDiag`)
— so `commitmentSquare = (a, a == b) ∘ signContent`, a shear of the sign-content coordinate. (And
`heldOpen` on the 4-element type is exactly swap-fixedness / gauge-neutrality,
`heldOpen_eq_true_iff_gaugeNeutral`: the recursion-top `heldOpen` of brick 26 *is* the `{untamped, zero}`
diagonal poles of bricks 17/18 — `heldOpen` = `GaugeNeutral` = on-diagonal, three names for the two
swap-fixed corners.)

The gauge side `AlgebraicPosition.commitmentSquare = (needsCommitment, heldOpen)` is an **injection
hitting exactly the three non-`(F,T)` corners**: injective (`commitmentSquare_injective`), never the
missing corner (`commitmentSquare_ne_missing`), and surjective onto the other three
(`exists_commitmentSquare_of_ne_missing`). So **`AlgebraicPosition` is the commitment-square minus the
`(F, T)` corner.**

## The recognition (the prose deposit) — the missing corner IS the `+1`

`(F, T)` = *not-outstanding yet held-open* = **settled into no-commitment, neutral** — and on `SeedGauge`
the unique element there is `untamped` (`commitmentSquare_eq_missing_iff_untamped`): no observer-content
to resolve (`bot_holdsNeitherSign` ⇒ ¬outstanding, brick 17) and swap-fixed / neutral (`gaugeNeutral_iff`
⇒ held-open, brick 18). The gauge codomain *structurally lacks* this corner, and the reason is **bin-2,
interpretive, but precise**: `untamped` is the no-commitment **source** state — the functor's
input/unit (bricks 17/18/22; `turn untamped = ⊥` recognizes to nothing, brick 20) — while the gauges
`{g1, g2, g3}` are the **target**, what the tamp commits *to*. A source-only property (being the
un-tamped ground) cannot appear on the target. So **the seed-side `+1` (the un-tamped `⊥`, brick 26's
recursion-bottom) is *exactly* the functor's un-tamped-input corner**: present on the source lattice
`SeedGauge` (4 = `2²`), absent on the codomain `AlgebraicPosition` (3) by construction.

This pins the `+1` half of the keystone's `×2`-vs-`+1` asymmetry as a precise, substrate-located object:
not a vague "extra element," but the `(¬outstanding, heldOpen)` corner of the commitment-square — the
one corner that is a property of *being un-committed*, hence of the source alone. The `×2` (FTPG
read/write → 6 colors, `self_dual_iff_three`) remains the open horizon; the `+1` is now located.

## Grade

* **bin-1 (Bin-1-Mathlib-or-Foam)** for everything typed: the two binary properties extended to the
  4-element type (`untamped ↦ (false, true)`), their `Bool × Bool` bijection (`cases <;> rfl`), the
  re-coordinatization of `signContent` (assembling brick 19's `gaugeNeutral_iff_onDiag`), the gauge-side
  3-corner injection (`decide` + assembly), the joint coordinate-match (assembling brick 25's
  `toAlgebraic'_commitment_preserving` + brick 26's `toAlgebraic'_heldOpen_preserving`), and the
  missing-corner-is-`untamped` characterization (`decide`). No new geometric content; the recognition is
  that two substrate-present binary properties are a coordinate map, and the bridge is the
  coordinate-match.

* **bin-2 / interpretive** for *why* the gauge codomain lacks `(F, T)` — that `untamped` is a
  source/no-commitment property the targets cannot carry, tying the `+1` to the functor's source/target
  asymmetry (bricks 18/22). Held merge-don't-fork: the bijection + corner-identification is bin-1; the
  source-not-target reading is the interpretive deposit.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeCommitmentSquare` is clean, zero
sorry/warnings. Imports `Foam.SeedGaugeDisciplineOrder` (brick 26, the chain head) — transitively gives
`SeedSign.outstanding` / `AlgebraicPosition.needsCommitment` (brick 25), `SeedSign.heldOpen` /
`AlgebraicPosition.heldOpen` (brick 26), `SeedSign.toAlgebraic'` / `AlgebraicPosition.toSign'` /
`signAlgebraicEquiv'` (brick 24), `toAlgebraic'_commitment_preserving` (25) /
`toAlgebraic'_heldOpen_preserving` (26), `SeedGauge` / `SeedSign.toGauge` / `gaugeNeutral_iff` (brick 18),
`SeedGauge.signContent` / `gaugeNeutral_iff_onDiag` (brick 19). New names:
`SeedGauge.outstanding` / `heldOpen` (+ `_untamped` simp + `SeedSign.outstanding_toGauge` /
`heldOpen_toGauge`); `SeedGauge.heldOpen_eq_true_iff_gaugeNeutral` / `_onDiag` /
`outstanding_eq_signContent_fst`; `SeedGauge.commitmentSquare` / `ofCommitmentSquare` /
`commitmentSquareEquiv`; `AlgebraicPosition.commitmentSquare` (+ `_injective` / `_ne_missing` /
`exists_commitmentSquare_of_ne_missing` / `toAlgebraic'_toSign'` / `commitmentSquare_eq_toSign'`);
`toAlgebraic'_commitmentSquare`; `SeedGauge.untamped_commitmentSquare` /
`commitmentSquare_eq_missing_iff_untamped`.)
-/

import Foam.SeedGaugeDisciplineOrder

namespace Foam

/-! ## The two binary properties, extended to the 4-element `SeedGauge`

Bricks 25/26 defined `outstanding` and `heldOpen` on the 3-element `SeedSign` and `AlgebraicPosition`.
Here they extend to the 4-element `SeedGauge` (brick 18) — the un-tamped basepoint `untamped` settling
the values brick 26 flagged: it carries no observer-content (`bot_holdsNeitherSign`, brick 17) so it is
**not** outstanding, and it is swap-fixed (`gaugeNeutral_iff`, brick 18) so it **is** held-open. -/

/-- **Does this gauge carry an outstanding observer-commitment?** — brick 25's `SeedSign.outstanding`
    extended to the un-tamped ground: `untamped ↦ false` (carries neither sign, `bot_holdsNeitherSign`,
    so nothing is outstanding). `+`/`0` `true`, `−` `false`. -/
def SeedGauge.outstanding : SeedGauge → Bool
  | .untamped => false
  | .plus => true
  | .minus => false
  | .zero => true

/-- **Is this the held-open, recursion-top gauge?** — brick 26's `SeedSign.heldOpen` extended to the
    un-tamped ground: `untamped ↦ true` (swap-fixed / gauge-neutral, `gaugeNeutral_iff`, so held-open).
    `0` `true`, `±` `false`. The two `true` values `{untamped, zero}` are exactly brick 17/18's two
    `{⊥, 0}` swap-fixed poles. -/
def SeedGauge.heldOpen : SeedGauge → Bool
  | .untamped => true
  | .plus => false
  | .minus => false
  | .zero => true

@[simp] theorem SeedGauge.outstanding_untamped : SeedGauge.untamped.outstanding = false := rfl
@[simp] theorem SeedGauge.heldOpen_untamped : SeedGauge.untamped.heldOpen = true := rfl

/-- The 4-element `outstanding` extends brick 25's 3-element one: it agrees with `SeedSign.outstanding`
    on the image of `toGauge`. -/
theorem SeedSign.outstanding_toGauge (s : SeedSign) : s.toGauge.outstanding = s.outstanding := by
  cases s <;> rfl

/-- The 4-element `heldOpen` extends brick 26's 3-element one: it agrees with `SeedSign.heldOpen` on the
    image of `toGauge`. -/
theorem SeedSign.heldOpen_toGauge (s : SeedSign) : s.toGauge.heldOpen = s.heldOpen := by
  cases s <;> rfl

/-! ## `heldOpen` = gauge-neutral = on-diagonal — the recognition tying brick 26 to bricks 18/19

The recursion-top property `heldOpen` (brick 26), extended to the 4-element type, *is* swap-fixedness
(brick 18's `GaugeNeutral`), *is* the diagonal of sign-content (brick 19's `gaugeNeutral_iff_onDiag`):
three names for the two `{untamped, zero}` poles. -/

/-- **`heldOpen` IS swap-fixedness** — `g.heldOpen = true ↔ g.GaugeNeutral`. Brick 26's recursion-top is
    brick 18's gauge-neutral; on the 4-element type both pick out `{untamped, zero}`. -/
theorem SeedGauge.heldOpen_eq_true_iff_gaugeNeutral (g : SeedGauge) :
    g.heldOpen = true ↔ g.GaugeNeutral := by
  rw [SeedGauge.gaugeNeutral_iff]
  cases g <;> decide

/-- **`heldOpen` IS the sign-content diagonal** — `g.heldOpen = true ↔ (g.signContent).1 =
    (g.signContent).2`. Composing `heldOpen_eq_true_iff_gaugeNeutral` with brick 19's
    `gaugeNeutral_iff_onDiag`: the held-open gauges are exactly those whose sign-content is on the
    diagonal of `Bool × Bool` (carries both signs or neither). -/
theorem SeedGauge.heldOpen_eq_true_iff_onDiag (g : SeedGauge) :
    g.heldOpen = true ↔ (g.signContent).1 = (g.signContent).2 :=
  (SeedGauge.heldOpen_eq_true_iff_gaugeNeutral g).trans (SeedGauge.gaugeNeutral_iff_onDiag g)

/-- **`outstanding` IS the first sign-content coordinate** — `g.outstanding = (g.signContent).1`
    (carries-`+`?). So `(outstanding, heldOpen)` shares its first coordinate with `signContent` and
    replaces the second (carries-`−`?) with the diagonal predicate — a *shear* of the sign-content
    coordinate, `commitmentSquare = (a, a == b) ∘ signContent`. -/
theorem SeedGauge.outstanding_eq_signContent_fst (g : SeedGauge) :
    g.outstanding = (g.signContent).1 := by
  cases g <;> rfl

/-! ## The commitment-square — the joint coordinate `(outstanding, heldOpen) : SeedGauge ≃ Bool × Bool` -/

/-- **The commitment-square coordinate** — the joint of the two substrate-present binary properties,
    `g ↦ (g.outstanding, g.heldOpen)`. On the 4-element `SeedGauge` it hits all four corners of
    `Bool × Bool`; this is the `SeedGauge`-side coordinate. -/
def SeedGauge.commitmentSquare (g : SeedGauge) : Bool × Bool := (g.outstanding, g.heldOpen)

/-- The inverse of `commitmentSquare`: reading a `(outstanding?, heldOpen?)` pair back as a gauge.
    `(F, T) ↦ untamped` (the un-tamped corner), `(T, F) ↦ +`, `(F, F) ↦ −`, `(T, T) ↦ 0`. -/
def SeedGauge.ofCommitmentSquare : Bool × Bool → SeedGauge
  | (false, true) => .untamped
  | (true, false) => .plus
  | (false, false) => .minus
  | (true, true) => .zero

theorem SeedGauge.ofCommitmentSquare_commitmentSquare (g : SeedGauge) :
    SeedGauge.ofCommitmentSquare g.commitmentSquare = g := by
  cases g <;> rfl

theorem SeedGauge.commitmentSquare_ofCommitmentSquare (x : Bool × Bool) :
    (SeedGauge.ofCommitmentSquare x).commitmentSquare = x := by
  rcases x with ⟨_ | _, _ | _⟩ <;> rfl

/-- **The commitment-square is a bijection `SeedGauge ≃ Bool × Bool`.** The two substrate-present binary
    properties `(outstanding, heldOpen)` jointly *coordinate* the 4-element commitment-lattice — all four
    corners hit. A re-coordinatization of brick 19's `signEquiv` (sharing the first coordinate,
    `outstanding_eq_signContent_fst`, and replacing the second with the diagonal predicate,
    `heldOpen_eq_true_iff_onDiag`). -/
def SeedGauge.commitmentSquareEquiv : SeedGauge ≃ Bool × Bool where
  toFun := SeedGauge.commitmentSquare
  invFun := SeedGauge.ofCommitmentSquare
  left_inv := SeedGauge.ofCommitmentSquare_commitmentSquare
  right_inv := SeedGauge.commitmentSquare_ofCommitmentSquare

/-! ## The gauge side hits exactly three corners — the missing `(false, true)` -/

/-- **The gauge-side commitment-square coordinate** — `a ↦ (a.needsCommitment, a.heldOpen)`. The
    FTPG-thread joint of the *same* two properties (brick 25's `needsCommitment` is brick 25's
    *outstanding-commitment* read on the gauge side). An **injection** into `Bool × Bool` hitting only
    the three non-`(F, T)` corners. -/
def AlgebraicPosition.commitmentSquare (a : AlgebraicPosition) : Bool × Bool :=
  (a.needsCommitment, a.heldOpen)

/-- **The gauge-side coordinate is injective** — the three gauges `{g1, g2, g3}` map to three distinct
    corners. So `AlgebraicPosition` embeds into the commitment-square. -/
theorem AlgebraicPosition.commitmentSquare_injective :
    Function.Injective AlgebraicPosition.commitmentSquare := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **The gauge side never hits the `(false, true)` corner** — `a.commitmentSquare ≠ (false, true)`. The
    missing corner is *not-outstanding yet held-open*; no gauge carries it (`g1` is `(F, F)`, `g2` is
    `(T, F)`, `g3` is `(T, T)`). This is the corner the gauge codomain structurally lacks. -/
theorem AlgebraicPosition.commitmentSquare_ne_missing (a : AlgebraicPosition) :
    a.commitmentSquare ≠ (false, true) := by
  cases a <;> decide

/-- **The gauge side surjects onto the other three corners** — every `x ≠ (false, true)` is some gauge's
    coordinate. With injectivity and `commitmentSquare_ne_missing`, this is the precise sense in which
    *`AlgebraicPosition` is the commitment-square minus the `(F, T)` corner*: a bijection onto
    `Bool × Bool ∖ {(false, true)}`. -/
theorem AlgebraicPosition.exists_commitmentSquare_of_ne_missing (x : Bool × Bool)
    (hx : x ≠ (false, true)) : ∃ a : AlgebraicPosition, a.commitmentSquare = x := by
  rcases x with ⟨_ | _, _ | _⟩
  · exact ⟨.g1, rfl⟩
  · exact absurd rfl hx
  · exact ⟨.g2, rfl⟩
  · exact ⟨.g3, rfl⟩

/-! ## The rigid bridge IS the coordinate-match — preserving BOTH coordinates

The headline: `signAlgebraicEquiv'` (brick 25's forced orientation) is *exactly* the map matching the
joint coordinate. The gauge-side coordinate of `s.toAlgebraic'` equals the seed-side coordinate of
`s.toGauge` — assembling brick 25's first-coordinate match with brick 26's second-coordinate match. The
two single-bit invariants together pin the full iso. -/

/-- **The rigid bridge matches both coordinates** — `(s.toAlgebraic').commitmentSquare =
    (s.toGauge).commitmentSquare`. The first coordinate is brick 25's `toAlgebraic'_commitment_preserving`
    (`needsCommitment ↔ outstanding`), the second is brick 26's `toAlgebraic'_heldOpen_preserving`
    (`heldOpen ↔ heldOpen`). So `signAlgebraicEquiv'` is the unique coordinate-matching bijection: the
    orbit-shape (brick 24), recursion-grading (brick 26), and commitment-content (brick 25) are three
    facets of one `Bool × Bool` coordinate, and the two bits together force the full iso. -/
theorem toAlgebraic'_commitmentSquare (s : SeedSign) :
    (s.toAlgebraic').commitmentSquare = (s.toGauge).commitmentSquare := by
  have h1 : (s.toAlgebraic').needsCommitment = s.toGauge.outstanding := by
    rw [toAlgebraic'_commitment_preserving, SeedSign.outstanding_toGauge]
  have h2 : (s.toAlgebraic').heldOpen = s.toGauge.heldOpen := by
    rw [toAlgebraic'_heldOpen_preserving, SeedSign.heldOpen_toGauge]
  show ((s.toAlgebraic').needsCommitment, (s.toAlgebraic').heldOpen)
     = ((s.toGauge).outstanding, (s.toGauge).heldOpen)
  rw [h1, h2]

/-- `signAlgebraicEquiv'` round-trips on the gauge side (`a.toSign'.toAlgebraic' = a`) — the right
    inverse of brick 24's flipped orientation, as a standalone lemma. -/
theorem AlgebraicPosition.toAlgebraic'_toSign' (a : AlgebraicPosition) :
    a.toSign'.toAlgebraic' = a := by
  cases a <;> rfl

/-- **Each gauge's coordinate is realized by its bridge-preimage commitment** —
    `a.commitmentSquare = (a.toSign'.toGauge).commitmentSquare`. Reading `toAlgebraic'_commitmentSquare`
    through the bridge bijection: the three gauges `{g1, g2, g3}` are the three corners `{(F,F), (T,F),
    (T,T)}` realized by the three commitment seeds `{−, +, 0}` (= `toSign'` of the gauges), the
    un-tamped `(F, T)` corner having no gauge preimage. -/
theorem AlgebraicPosition.commitmentSquare_eq_toSign' (a : AlgebraicPosition) :
    a.commitmentSquare = (a.toSign'.toGauge).commitmentSquare := by
  have h := toAlgebraic'_commitmentSquare a.toSign'
  rw [AlgebraicPosition.toAlgebraic'_toSign'] at h
  exact h

/-! ## The missing corner IS `untamped` — the `+1`, the functor's un-tamped input

`(false, true)` = *not-outstanding yet held-open* = settled into no-commitment, neutral. On `SeedGauge`
the unique element there is `untamped` — and the gauge codomain lacks it because `untamped` is the
no-commitment *source* (the functor's input/unit), not a *target* the tamp commits to. -/

/-- `untamped`'s commitment-square coordinate is the missing corner `(false, true)`. -/
@[simp] theorem SeedGauge.untamped_commitmentSquare :
    SeedGauge.untamped.commitmentSquare = (false, true) := rfl

/-- **The missing corner is exactly `untamped`** — `g.commitmentSquare = (false, true) ↔ g = untamped`.
    The `(¬outstanding, heldOpen)` corner — *settled into no-commitment, neutral* — is the un-tamped
    ground alone: no observer-content to resolve (`bot_holdsNeitherSign`, brick 17) and swap-fixed /
    neutral (`gaugeNeutral_iff`, brick 18). Together with `AlgebraicPosition.commitmentSquare_ne_missing`,
    this is the `+1`: the one commitment-square corner present on the source lattice `SeedGauge` (4 = `2²`)
    and absent on the codomain `AlgebraicPosition` (3) — the functor's un-tamped-input corner, a
    property of *being un-committed* and hence of the source alone. -/
theorem SeedGauge.commitmentSquare_eq_missing_iff_untamped (g : SeedGauge) :
    g.commitmentSquare = (false, true) ↔ g = SeedGauge.untamped := by
  cases g <;> decide

end Foam
