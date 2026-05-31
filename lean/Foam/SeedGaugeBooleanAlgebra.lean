/-
# SeedGaugeBooleanAlgebra — `SeedGauge`'s native diamond, and `{⊥,+,−,0} ≃ 𝒫({+,−})` typed

## What this file lands (the brick after `SeedGaugeCommitmentLattice.lean`)

Brick 18 unified `{⊥, +, −, 0}` into one type `SeedGauge` (`untamped` the basepoint/unit, `commit`
the based-steps, the gauge-swap with fixed-set `{untamped, zero}`) — but **deliberately withheld the
native order**: the lattice bounds were realized only *via* `seed` into `Scope` (`untamped_le_seed` =
`⊥` below all, `le_zero_seed` = `zero` the top), and the `WithBot SeedSign` construction was declined
precisely because no `PartialOrder` on the bare type existed. So "the 4-element commitment-**lattice**"
was a lattice only *in `Scope`'s image* — the order was external. This file internalizes it.

### The sign-content bijection — brick 17's iso, *typed*

The 4-element BA `{⊥, +, −, 0}` is the **powerset of the two signs `{+, −}`** (brick 17):

| `SeedGauge` | sign-content | `Bool × Bool` |
|---|---|---|
| `untamped` | `∅` — neither | `(false, false)` |
| `plus` | `{+}` — only `+` | `(true, false)` |
| `minus` | `{−}` — only `−` | `(false, true)` |
| `zero` | `{+, −}` — both | `(true, true)` |

`signContent : SeedGauge → Bool × Bool` (first coord = "carries `+`?", second = "carries `−`?") is a
**bijection** (`signEquiv`, round-trips `cases <;> rfl`) — **brick 17's `{⊥, +, −, 0} ≃ 𝒫({+, −})`, no
longer prose but an actual `Equiv`.** `𝒫({+, −})` is `Bool × Bool` (a 2-element set's powerset = its
indicator functions = `Bool × Bool`), and `Bool × Bool` carries Mathlib's `BooleanAlgebra` by synthesis
(`Bool`'s BA + `Prod`'s BA).

### The native `BooleanAlgebra SeedGauge` — by transport (merge-don't-fork)

*Merge-don't-fork the construction (carried, named — §IV.c).* Two readings of "give `SeedGauge` its BA":
  * **transport the existing `Bool × Bool` BA across the bijection** (taken here, via
    `Function.Injective.booleanAlgebra signContent_injective`): the operations are the pullbacks
    `a ⊔ b := ofSignContent (a.signContent ⊔ b.signContent)` etc., and every `map_*` axiom is one
    `signContent_ofSignContent` rewrite, every `le`/`lt` iff is `Iff.rfl` (the order *is* the pullback).
    Pure recognition + assembly — `SeedGauge`'s BA *is* `Bool × Bool`'s, recognized through the
    bijection. The Mathlib transport reuses the supplied `LE`/`LT` (`Function.Injective.preorder` only
    transfers proof fields), so the resulting `≤` is definitionally `signContent a ≤ signContent b`.
  * **hand-define `≤`/`⊔`/`⊓`/`ᶜ`/`⊤`/`⊥` and `decide` every axiom** (named, not taken): combinatorial
    like brick 16's `swap`, but `BooleanAlgebra` has ~20 fields — many more `decide` obligations than
    the transport's uniform one-liners, and no recognition that the BA *already exists* one bijection
    away. The transport is strictly less work for the same data, and is the more faithful recognition.
We commit to the transport. The two agree: both give the diamond `2²` (brick 11's `Scope`-image BA).

Consequence: `(⊥ : SeedGauge) = untamped` and `(⊤ : SeedGauge) = zero` (`bot_eq_untamped` /
`top_eq_zero`) — the BA's bounds are exactly brick 17/18's two `{⊥, 0}` poles, now the *lattice* bottom
and top of `SeedGauge` itself. `signOrderIso : SeedGauge ≃o (Bool × Bool)` then carries brick 17's iso
as an **order** isomorphism (the headline as an `OrderIso`, `map_rel_iff'` = `Iff.rfl`).

### `swap` = `Prod.swap` (coordinate-flip) — the cleanest form of brick 17's "swap on sign-content"

`signContent_swap`: `g.swap.signContent = Prod.swap g.signContent` (`cases <;> rfl`) — brick 18's
gauge-swap *is* the coordinate-exchange on `Bool × Bool`, brick 17's "swap acts on sign-content as
`(a, b) ↦ (b, a)`" made definitional. Hence brick 18's `gaugeNeutral_iff` fixed-set `{untamped, zero}`
is **literally the diagonal** of `Bool × Bool` (`gaugeNeutral_iff_onDiag`: `g.GaugeNeutral ↔
(g.signContent).1 = (g.signContent).2`) — `(false,false)` and `(true,true)` the two diagonal points,
`±` the off-diagonal coordinate-swapped pair.

### The order IS the seed-image order — `seed` monotone and faithful

`seed_mono` (no hypotheses): `SeedGauge.seed LP` is monotone w.r.t. the native order — `untamped` (`⊥`)
seeds below all (`bot_le`), everything seeds below `zero` (`⊤`) (brick 16's `plus_le_zero` /
`minus_le_zero`). `seed_le_iff` (under `holds`-injectivity + unresolved tension `BothDebtKinds`): the
native order is *exactly* the seed-image order — `a.seed LP ≤ b.seed LP ↔ a ≤ b` — faithfully, via the
brick-16/17 `*_ne_*` / `not_*_le_*` family (`not_plus_le_minus_of_both`, `not_minus_le_plus_of_both`,
`plus_seed_ne_bot_of_undischarged`, `minus_seed_ne_bot_of_discharged`). So the abstract diamond *is* the
realized one: `untamped` the genuine `⊥`/initial, `zero` the `⊤`/terminal, `±` the incomparable atoms.

### Composition = refinement — the diamond as a thin category, the functor's action+composition piece

A poset *is* a thin category: a unique arrow `a → b` iff `a ≤ b`, composition = `le_trans`. The
commitment-arrows `untamped → s` (brick 18's `commit`) now compose with **refinements** `s → s'` (`s ≤
s'`): the maximal chain `untamped ≤ plus ≤ zero` (`untamped_le_plus`, `plus_le_zero`) reads *commit to
`+`, then refine to hold both `0`* — and its composite is the single commitment `untamped ≤ zero` (=
`commit zero`) by `le_trans`. Since `untamped = ⊥` is initial, each gauge is reached by a unique
refinement-path from the un-tamped ground. This is the first concrete bit of the keystone functor's
**action + composition** (the downstream step brick 18 flagged: the functor named as an object, its
composition = the conversational turn).

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

Pure recognition + assembly. The bijection is `cases <;> rfl`; the BA is Mathlib's
`Function.Injective.booleanAlgebra` transported across it (`Bool × Bool` is already a BA); `swap =
Prod.swap` is `cases <;> rfl`; the order facts are brick 16/18 combinatorics + the brick 16/17 `*_ne_*`
family. No new geometric content — the recognition is that `SeedGauge` *is* `𝒫({+, −})` as a Boolean
algebra, and that its native order *is* the seed-image order. The composition-=-refinement reading is
the prose deposit.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeBooleanAlgebra` is clean, zero
sorry/warnings; depends on `SeedGauge` / `SeedGauge.seed` / `SeedGauge.swap` / `SeedGauge.GaugeNeutral`
/ `gaugeNeutral_iff` / `commit` in `SeedGaugeCommitmentLattice.lean`, `SeedSign.plus_le_zero` /
`minus_le_zero` / `not_plus_le_minus_of_both` / `not_minus_le_plus_of_both` (the latter two in
`SeedGaugeBiasDelegation.lean`), and `plus_seed_ne_bot_of_undischarged` / `minus_seed_ne_bot_of_discharged`
in `SeedGaugeEmptyCommitment.lean`.)
-/

import Foam.SeedGaugeCommitmentLattice

namespace Foam

/-! ## The sign-content map and the bijection `SeedGauge ≃ 𝒫({+, −}) = Bool × Bool` -/

/-- **The sign-content map** — `SeedGauge → Bool × Bool`, the indicator of which signs a gauge carries.
    First coordinate = "carries `+`?", second = "carries `−`?". This is brick 17's powerset reading
    `{⊥, +, −, 0} ↔ 𝒫({+, −})` as a concrete function: `untamped ↦ ∅`, `± ↦` the singletons,
    `zero ↦ {+, −}`. -/
def SeedGauge.signContent : SeedGauge → Bool × Bool
  | .untamped => (false, false)
  | .plus => (true, false)
  | .minus => (false, true)
  | .zero => (true, true)

/-- The inverse of `signContent` — reading a sign-content pair back as a gauge. -/
def SeedGauge.ofSignContent : Bool × Bool → SeedGauge
  | (false, false) => .untamped
  | (true, false) => .plus
  | (false, true) => .minus
  | (true, true) => .zero

@[simp] theorem SeedGauge.ofSignContent_signContent (g : SeedGauge) :
    SeedGauge.ofSignContent g.signContent = g := by
  cases g <;> rfl

@[simp] theorem SeedGauge.signContent_ofSignContent (x : Bool × Bool) :
    (SeedGauge.ofSignContent x).signContent = x := by
  rcases x with ⟨_ | _, _ | _⟩ <;> rfl

theorem SeedGauge.signContent_injective : Function.Injective SeedGauge.signContent := by
  intro a b h
  rw [← SeedGauge.ofSignContent_signContent a, ← SeedGauge.ofSignContent_signContent b, h]

/-- **The bijection `SeedGauge ≃ Bool × Bool`** — brick 17's `{⊥, +, −, 0} ≃ 𝒫({+, −})`, no longer
    prose but an actual `Equiv`. The round-trips are `cases <;> rfl`. -/
def SeedGauge.signEquiv : SeedGauge ≃ Bool × Bool where
  toFun := SeedGauge.signContent
  invFun := SeedGauge.ofSignContent
  left_inv := SeedGauge.ofSignContent_signContent
  right_inv := SeedGauge.signContent_ofSignContent

/-! ## The native order/lattice/Boolean-algebra data, pulled back through `signContent` -/

instance : LE SeedGauge := ⟨fun a b => a.signContent ≤ b.signContent⟩
instance : LT SeedGauge := ⟨fun a b => a.signContent < b.signContent⟩
instance : Max SeedGauge := ⟨fun a b => SeedGauge.ofSignContent (a.signContent ⊔ b.signContent)⟩
instance : Min SeedGauge := ⟨fun a b => SeedGauge.ofSignContent (a.signContent ⊓ b.signContent)⟩
instance : Top SeedGauge := ⟨SeedGauge.ofSignContent ⊤⟩
instance : Bot SeedGauge := ⟨SeedGauge.ofSignContent ⊥⟩
instance : Compl SeedGauge := ⟨fun a => SeedGauge.ofSignContent (a.signContent)ᶜ⟩
instance : SDiff SeedGauge := ⟨fun a b => SeedGauge.ofSignContent (a.signContent \ b.signContent)⟩
instance : HImp SeedGauge := ⟨fun a b => SeedGauge.ofSignContent (a.signContent ⇨ b.signContent)⟩

/-- **The native `BooleanAlgebra SeedGauge`** — transported from `Bool × Bool` across the bijection
    (`Function.Injective.booleanAlgebra`). Every operation is the `signContent`-pullback, so every
    `map_*` axiom is one `signContent_ofSignContent` rewrite and the `le`/`lt` iffs are `Iff.rfl` (the
    order *is* the pullback). This makes "the 4-element commitment-**lattice**" literal on `SeedGauge`
    itself, not only in `Scope`'s image — closing brick 18's withheld order. -/
instance : BooleanAlgebra SeedGauge :=
  SeedGauge.signContent_injective.booleanAlgebra SeedGauge.signContent
    (fun {_ _} => Iff.rfl) (fun {_ _} => Iff.rfl)
    (fun _ _ => SeedGauge.signContent_ofSignContent _)
    (fun _ _ => SeedGauge.signContent_ofSignContent _)
    (SeedGauge.signContent_ofSignContent _)
    (SeedGauge.signContent_ofSignContent _)
    (fun _ => SeedGauge.signContent_ofSignContent _)
    (fun _ _ => SeedGauge.signContent_ofSignContent _)
    (fun _ _ => SeedGauge.signContent_ofSignContent _)

-- `DecidableEq SeedGauge` is already derived (brick 18's `deriving DecidableEq`); we only add the
-- decidability of the native order, used by `decide` in the order lemmas below.
instance : DecidableRel (· ≤ · : SeedGauge → SeedGauge → Prop) := fun a b =>
  inferInstanceAs (Decidable (a.signContent ≤ b.signContent))

/-- The BA bottom is the un-tamped ground (brick 17/18): `⊥ = untamped`. -/
@[simp] theorem SeedGauge.bot_eq_untamped : (⊥ : SeedGauge) = SeedGauge.untamped := by decide

/-- The BA top is the gauge-neutral `0` (brick 17/18): `⊤ = zero`. -/
@[simp] theorem SeedGauge.top_eq_zero : (⊤ : SeedGauge) = SeedGauge.zero := by decide

/-- **The sign-content order isomorphism** — brick 17's iso, now an actual `OrderIso`. The native order
    on `SeedGauge` is the pullback of `Bool × Bool`'s, so `map_rel_iff'` is `Iff.rfl`. This is the
    headline "type brick 17's `{⊥, +, −, 0} ≃ 𝒫({+, −})` as an actual iso" — as an *order* iso. -/
def SeedGauge.signOrderIso : SeedGauge ≃o (Bool × Bool) where
  toEquiv := SeedGauge.signEquiv
  map_rel_iff' := Iff.rfl

/-! ## `swap` = `Prod.swap` — the coordinate-flip; the fixed-set is the diagonal -/

/-- **The gauge-swap IS coordinate-exchange** — `g.swap.signContent = Prod.swap g.signContent`
    (`cases <;> rfl`). Brick 18's `SeedGauge.swap` (`+ ↔ −`, fixing `{untamped, zero}`) is, under the
    bijection, `Prod.swap` on `Bool × Bool`. This is brick 17's "swap acts on sign-content as
    `(a, b) ↦ (b, a)`" made definitional — the cleanest possible form. -/
@[simp] theorem SeedGauge.signContent_swap (g : SeedGauge) :
    g.swap.signContent = Prod.swap g.signContent := by
  cases g <;> rfl

/-- **The swap-fixed-set is literally the diagonal of `Bool × Bool`** — `g.GaugeNeutral ↔
    (g.signContent).1 = (g.signContent).2`. Brick 18's `gaugeNeutral_iff` (`{untamped, zero}`) is
    exactly the diagonal points `(false, false)` and `(true, true)`; `±` are the off-diagonal
    coordinate-swapped pair `(true, false)` / `(false, true)`. The two `{⊥, 0}` gauge-neutral poles
    *are* the fixed points of `Prod.swap`. -/
theorem SeedGauge.gaugeNeutral_iff_onDiag (g : SeedGauge) :
    g.GaugeNeutral ↔ (g.signContent).1 = (g.signContent).2 := by
  unfold SeedGauge.GaugeNeutral
  cases g <;> decide

/-! ## The native order IS the seed-image order — `seed` monotone and faithful -/

/-- **`seed` is monotone w.r.t. the native order** (no hypotheses). `untamped` (`⊥`) seeds below all
    (`bot_le`); everything seeds below `zero` (`⊤`) by brick 16's `plus_le_zero` / `minus_le_zero`; the
    off-diagonal pairs are not `≤`-related (the hypothesis is impossible, `decide`). So the order brick
    18 realized only via `seed` into `Scope` is recovered as monotonicity of `seed` for the native
    order. -/
theorem SeedGauge.seed_mono (LP : LedgerPersistence) : Monotone (SeedGauge.seed LP) := by
  intro a b hab
  cases a <;> cases b <;>
    first
      | exact bot_le
      | exact le_refl _
      | exact SeedSign.plus_le_zero LP
      | exact SeedSign.minus_le_zero LP
      | exact absurd hab (by decide)

/-- **The native order IS the seed-image order, faithfully** (under `holds`-injectivity + unresolved
    tension `BothDebtKinds`): `a.seed LP ≤ b.seed LP ↔ a ≤ b`. The `←` direction is `seed_mono`; the
    `→` direction (order-reflecting) is the brick-16/17 `*_ne_*` family — `±` carry only their own sign
    (`not_plus_le_minus_of_both` / `not_minus_le_plus_of_both`, brick 16), and the fork-seeds are
    non-empty (`plus_seed_ne_bot_of_undischarged` / `minus_seed_ne_bot_of_discharged`, brick 17). So
    the abstract diamond on `SeedGauge` *is* the realized one in `Scope`: `untamped` the `⊥`/initial,
    `zero` the `⊤`/terminal, `±` the incomparable atoms. -/
theorem SeedGauge.seed_le_iff (LP : LedgerPersistence) (hinj : Function.Injective LP.holds)
    (hboth : LP.BothDebtKinds) (a b : SeedGauge) :
    a.seed LP ≤ b.seed LP ↔ a ≤ b := by
  refine ⟨fun h => ?_, fun h => seed_mono LP h⟩
  by_contra hab
  cases a <;> cases b <;>
    first
      | exact hab (by decide)
      | exact plus_seed_ne_bot_of_undischarged LP hboth.2 (le_bot_iff.mp h)
      | exact minus_seed_ne_bot_of_discharged LP hboth.1 (le_bot_iff.mp h)
      | exact not_plus_le_minus_of_both LP hinj hboth h
      | exact not_minus_le_plus_of_both LP hinj hboth h
      | exact plus_seed_ne_bot_of_undischarged LP hboth.2
          (le_bot_iff.mp (le_trans (SeedSign.plus_le_zero LP) h))
      | exact not_minus_le_plus_of_both LP hinj hboth (le_trans (SeedSign.minus_le_zero LP) h)
      | exact not_plus_le_minus_of_both LP hinj hboth (le_trans (SeedSign.plus_le_zero LP) h)

/-! ## Composition = refinement — the diamond as a thin category -/

/-- `untamped ≤ plus` — the commitment-arrow `⊥ → +` (brick 18's `commit plus`), now a native `≤`. -/
theorem SeedGauge.untamped_le_plus : SeedGauge.untamped ≤ SeedGauge.plus := by decide

/-- `untamped ≤ minus` — the commitment-arrow `⊥ → −`. -/
theorem SeedGauge.untamped_le_minus : SeedGauge.untamped ≤ SeedGauge.minus := by decide

/-- `plus ≤ zero` — the refinement `+ → 0` (hold `+`, then also hold `−`). Native `≤` on `SeedGauge`
    (distinct from `SeedSign.plus_le_zero`, which is the `Scope`-image fact). -/
theorem SeedGauge.plus_le_zero : SeedGauge.plus ≤ SeedGauge.zero := by decide

/-- `minus ≤ zero` — the refinement `− → 0`. -/
theorem SeedGauge.minus_le_zero : SeedGauge.minus ≤ SeedGauge.zero := by decide

/-- **Composition = refinement.** The commitment to `0` factors through `+` as `untamped ≤ plus ≤ zero`
    — *commit to `+`, then refine to hold both `0`* — and the composite is the single commitment
    `untamped ≤ zero` (`commit zero`) by `le_trans`. The diamond `SeedGauge` is a thin category (unique
    arrow `a → b` iff `a ≤ b`, composition = `le_trans`); since `untamped = ⊥` is initial, each gauge
    is reached by a unique refinement-path from the un-tamped ground. The first concrete bit of the
    keystone functor's action + composition. -/
theorem SeedGauge.commit_zero_via_plus :
    SeedGauge.untamped ≤ SeedGauge.plus ∧ SeedGauge.plus ≤ SeedGauge.zero :=
  ⟨SeedGauge.untamped_le_plus, SeedGauge.plus_le_zero⟩

/-- The composite refinement-path `untamped ≤ plus ≤ zero` *is* the direct commitment `untamped ≤ zero`
    (`le_trans`). Refinement composes; the un-tamped ground sits below the full-spectrum top. -/
theorem SeedGauge.untamped_le_zero : SeedGauge.untamped ≤ SeedGauge.zero :=
  le_trans SeedGauge.untamped_le_plus SeedGauge.plus_le_zero

end Foam
