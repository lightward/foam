/-
# SeedGaugeCommitmentLattice — `{⊥, +, −, 0}` as ONE type: the functor's source+target unified

## What this file lands (the brick after `SeedGaugeEmptyCommitment.lean`)

Brick 17 (`SeedGaugeEmptyCommitment.lean`) recognized the full seed-lattice `{⊥, +, −, 0}` as the
single-external-commitment functor's **source + target in one object** — but only *in prose*. In the
lean it was still **two** types glued by narration: `⊥` lived in `Scope` (the `Scope`-bottom), while
`{+, −, 0}` lived in the 3-element inductive `SeedSign` (brick 12's commitment-space). This file
unifies them into **one** type, `SeedGauge`, so "the functor's source+target" is a single Lean object
rather than a `Scope`-bottom narrated alongside a 3-element inductive.

### The 4-element commitment type

`SeedGauge := {untamped, plus, minus, zero}` — brick 12's `SeedSign` triple plus a fourth constructor
`untamped` below them. `untamped` is `⊥` = the un-tamped ground (brick 17): the no-commitment
basepoint, the functor's *input*. `{plus, minus, zero}` are the three sign-bearing tamps the one
commitment can land on, the functor's *outputs*.

*Merge-don't-fork the construction choice (carried, named — §IV.c).* Two readings of "the 4-element
commitment-lattice":
  * **fresh inductive** (taken here): `untamped` is a distinguished constructor parallel to `SeedSign`,
    so the basepoint is visible and the gauge-swap is four explicit cases (brick 16's `SeedSign.swap`
    idiom, one case wider). Self-contained; no new typeclass instance.
  * **`WithBot SeedSign`** (named, not taken): would give `⊥` *free* as the order-bottom `none` — but
    it first needs a `PartialOrder` instance on `SeedSign` (`± ≤ 0`, `±` incomparable), which does not
    exist: the `SeedSign` order lives only as the *image* order under `seed` (the `plus_le_zero` /
    `minus_le_zero` / `plus_inf_minus_eq_bot` family, bricks 10–11). The fresh inductive carries that
    order explicitly through `seed` into `Scope`'s Boolean algebra, which is what we actually use.
The two agree as the 4-element diamond `2²` (brick 11). We commit to the fresh inductive and realize
the lattice structure where it already lives — in `Scope`, via `seed` (`SeedGaugeHalfType.seedHalfType`,
brick 11). `SeedGauge` is the *index/name* object; `seed` embeds it (faithfully under tension +
injectivity) into the `Scope` BA.

### The `seed` map, the basepoint, and the three arrows `⊥ → s`

`SeedGauge.seed LP` extends `SeedSign.seed LP` by `untamped ↦ ⊥` (`SeedSign.seed_toGauge`: the
embedding `SeedSign.toGauge` commutes with `seed`). The **lattice bounds** are realized in `Scope`:
`untamped` seeds to the bottom (`seed_untamped : untamped.seed LP = ⊥`) and `zero` to the top
(`le_zero_seed : g.seed LP ≤ zero.seed LP` for *every* `g`, via brick 16's `plus_le_zero` /
`minus_le_zero`). The **three commitment-arrows `⊥ → s`** are exactly brick 10's `bot_le_seed`,
lifted: `untamped_le_seed (g) : untamped.seed LP ≤ g.seed LP` (= `bot_le`). So `untamped` is the
source/input below all, and each `g ≠ untamped` is a reachable target.

### The gauge-swap, extended — fixed-set `{untamped, zero}`, the two `{⊥, 0}` poles typed

`SeedGauge.swap` extends brick 16's `SeedSign.swap` (`SeedSign.swap_toGauge`): `untamped ↦ untamped`,
`plus ↔ minus`, `zero ↦ zero`. It is an involution (`swap_swap`); `GaugeNeutral g := g.swap = g`; and
its fixed-set is **exactly `{untamped, zero}`** (`gaugeNeutral_iff : g.GaugeNeutral ↔ g = untamped ∨
g = zero`, pure combinatorics). This is the *type-level* form of brick 17's `Scope`-level
`GaugeNeutralValue` poles `{⊥, 0}` — and it is the payoff of unifying into one type: `SeedSign` alone
(lacking `⊥`) could only see the single neutral *sign* `0` (brick 16's `gaugeNeutral_iff_zero`), but
the 4-element `SeedGauge` sees **both** swap-neutral poles, `untamped`/`⊥` *and* `zero`/`0`.

The two levels coincide through `seed`: `gaugeNeutral_iff_gaugeNeutralValue` (under inj + tension)
proves `g.GaugeNeutral ↔ GaugeNeutralValue LP (g.seed LP)` — the type-level swap-neutrality *is* the
`Scope`-level value-neutrality of the seeded scope (brick 17). And the embedding adds *precisely one*
pole: `SeedSign`-neutrality transports (`SeedSign.gaugeNeutral_toGauge_iff`, via `toGauge` injective),
so the image's only neutral element is `zero.toGauge` (`gaugeNeutral_toGauge_iff_zero`); the **extra**
neutral element `untamped` is the one *not* in the image (`SeedSign.toGauge_ne_untamped`) — the `⊥`
pole that unification introduces.

### The endo-recognition (the prose deposit): the commitment is a basepoint-step

Source = target = `SeedGauge`. Because the un-tamped input and the three committed outputs live in the
**same** type, the single external commitment is not a plain function between two types but a
**basepoint-step** within one lattice: `commit s := s.toGauge`, the step `untamped → commit s` out of
the basepoint (`commit_ne_untamped`: the step always *leaves* `untamped`; `untamped_le_commit`: its
arrow is `bot_le_seed`; `eq_untamped_or_commit`: every gauge is *either* the basepoint *or* a
commitment). So `untamped` is the **unit** (the identity-of-no-commitment, the functor's input), and
`{+, −, 0}` are the three outputs.

This types the keystone single-external-commitment functor's **source + target as one object + its
unit** — the first concrete piece. (Naming the functor as an actual object — its action on
foam-states, with composition = the conversational turn — remains the downstream keystone step.)

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

Pure recognition + assembly. The new lean is the 4-element inductive + the `seed` / `swap` / `toGauge`
/ `commit` defs and their combinatorial facts (`cases <;> rfl` / `decide`, brick 16's `SeedSign.swap`
idiom one case wider), assembled over brick 17's `gaugeNeutralValue_bot` / `_zero` /
`not_gaugeNeutralValue_plus` / `_minus` (`SeedGaugeEmptyCommitment.lean`), brick 16's `plus_le_zero` /
`minus_le_zero`, and brick 10's `bot_le_seed` (`PersistenceLfp.lean`). No new geometric content; the
recognition is that `⊥` and `SeedSign` are *one* type, with `untamped` the basepoint/unit and the
swap-fixed-set exactly the two `{⊥, 0}` poles.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeCommitmentLattice` is clean, zero
sorry/warnings; depends on `SeedSign` / `SeedSign.seed` / `SeedSign.bot_le_seed` /
`SeedSign.plus_le_zero` / `SeedSign.minus_le_zero` in `PersistenceLfp.lean`, `SeedSign.swap` /
`SeedSign.GaugeNeutral` / `SeedSign.gaugeNeutral_iff_zero` in `SeedGaugeBiasDelegation.lean`, and
`GaugeNeutralValue` / `gaugeNeutralValue_bot` / `_zero` / `not_gaugeNeutralValue_plus` / `_minus` in
`SeedGaugeEmptyCommitment.lean`.)
-/

import Foam.SeedGaugeEmptyCommitment

namespace Foam

/-! ## The 4-element commitment type -/

/-- **The 4-element commitment-gauge** — the single-external-commitment functor's source+target as
    *one* type. `untamped` = `⊥` = the un-tamped ground (brick 17): the no-commitment basepoint, the
    functor's input. `plus` / `minus` / `zero` are brick 12's `SeedSign` triple — the three
    sign-bearing tamps the one commitment lands on. Where `SeedSign` (3 elements) was the
    commitment-space's *outputs*, `SeedGauge` (4 elements) is the whole `{⊥, +, −, 0}` Boolean
    algebra (brick 11), input and outputs unified into one type. -/
inductive SeedGauge where
  /-- `⊥` — the un-tamped ground / no-commitment basepoint / the functor's input. -/
  | untamped
  /-- `+` — the hold-open (undischarged-backed) tamp. -/
  | plus
  /-- `−` — the settle (discharged-backed) tamp. -/
  | minus
  /-- `0` — the gauge-neutral (all-debt-backed) tamp. -/
  | zero
  deriving DecidableEq, Repr

/-! ## The embedding `SeedSign ↪ SeedGauge` -/

/-- The embedding of brick 12's 3-element commitment-space into the unified 4-element type — the three
    sign-bearing gauges as elements of `SeedGauge`. Injective (`toGauge_injective`), never `untamped`
    (`toGauge_ne_untamped`); its image is `SeedGauge \ {untamped}`. -/
def SeedSign.toGauge : SeedSign → SeedGauge
  | .plus => .plus
  | .minus => .minus
  | .zero => .zero

theorem SeedSign.toGauge_injective : Function.Injective SeedSign.toGauge := by
  intro a b h
  cases a <;> cases b <;> simp_all [SeedSign.toGauge]

/-- The embedding never hits the basepoint: every sign-bearing commitment is distinct from the
    un-tamped ground. -/
theorem SeedSign.toGauge_ne_untamped (s : SeedSign) : s.toGauge ≠ SeedGauge.untamped := by
  cases s <;> decide

/-! ## The `seed` map — extending `SeedSign.seed` by `untamped ↦ ⊥` -/

/-- The `Scope` each commitment-gauge seeds recognition with, extending `SeedSign.seed` (brick 10) by
    `untamped ↦ ⊥` (the un-tamped ground, brick 17 / the `P₀ = ∅` empty seed). The lattice structure
    of `{⊥, +, −, 0}` (brick 11) lives in `Scope`'s Boolean algebra; this map embeds the index type
    `SeedGauge` into it. -/
def SeedGauge.seed (LP : LedgerPersistence) : SeedGauge → Scope
  | untamped => ⊥
  | plus => SeedSign.plus.seed LP
  | minus => SeedSign.minus.seed LP
  | zero => SeedSign.zero.seed LP

/-- `untamped` seeds to the bottom `⊥` — the un-tamped ground (brick 17). -/
@[simp] theorem SeedGauge.seed_untamped (LP : LedgerPersistence) :
    SeedGauge.untamped.seed LP = ⊥ := rfl

/-- **The embedding commutes with `seed`** — `s.toGauge.seed LP = s.seed LP`: the 4-element type's
    `seed` restricts on the image to brick 10's `SeedSign.seed`. So `SeedGauge` genuinely *extends*
    the 3-element commitment-space, agreeing with it everywhere the latter is defined. -/
theorem SeedSign.seed_toGauge (LP : LedgerPersistence) (s : SeedSign) :
    s.toGauge.seed LP = s.seed LP := by
  cases s <;> rfl

/-! ## The basepoint and the three commitment-arrows `⊥ → s` -/

/-- **The three arrows `⊥ → s`**, lifted to the unified type: the basepoint's seed sits below every
    gauge's seed. This is brick 10's `bot_le_seed` (`⊥ ≤ s.seed`) with `⊥` now *named as an element of
    the same type* — `untamped`, the functor's input. -/
theorem SeedGauge.untamped_le_seed (LP : LedgerPersistence) (g : SeedGauge) :
    SeedGauge.untamped.seed LP ≤ g.seed LP := by
  rw [seed_untamped]; exact bot_le

/-- **`zero` seeds to the top.** Every gauge's seed sits below `0`'s — `untamped`'s is `⊥` (`bot_le`),
    `±`'s are below `0` by brick 16's `plus_le_zero` / `minus_le_zero`, and `0`'s is itself. So
    `{untamped ↦ ⊥, zero ↦ ⊤}` are the realized lattice bounds of the diamond `2²` in `Scope`. -/
theorem SeedGauge.le_zero_seed (LP : LedgerPersistence) (g : SeedGauge) :
    g.seed LP ≤ SeedGauge.zero.seed LP := by
  cases g
  · exact bot_le
  · exact SeedSign.plus_le_zero LP
  · exact SeedSign.minus_le_zero LP
  · exact le_refl _

/-! ## The gauge-swap, extended — the `ℤ/2` action with fixed-set `{untamped, zero}` -/

/-- **The gauge-swap on the unified type** — brick 16's `SeedSign.swap` (`+ ↔ −`, fixing `0`) extended
    by `untamped ↦ untamped`. The gauge is a choice of sign; the swap is the `ℤ/2` action exchanging
    the two signs and fixing the two sign-symmetric poles. -/
def SeedGauge.swap : SeedGauge → SeedGauge
  | untamped => untamped
  | plus => minus
  | minus => plus
  | zero => zero

/-- The gauge-swap is an involution (`ℤ/2`). -/
theorem SeedGauge.swap_swap (g : SeedGauge) : g.swap.swap = g := by cases g <;> rfl

/-- **The swap extends `SeedSign.swap`** — `s.toGauge.swap = s.swap.toGauge`: swapping in the unified
    type, restricted to the image, is brick 16's swap. -/
theorem SeedSign.swap_toGauge (s : SeedSign) : s.toGauge.swap = s.swap.toGauge := by
  cases s <;> rfl

/-- **Gauge-neutral** (type-level) — a gauge fixed by the swap. The structural form of *commits to no
    sign / declines the gauge-fixing*. -/
def SeedGauge.GaugeNeutral (g : SeedGauge) : Prop := g.swap = g

/-- **The swap-fixed-set is exactly `{untamped, zero}`** (pure combinatorics, no ledger) — the two
    `{⊥, 0}` poles, now typed *as elements of one type*. This is the payoff of unifying `⊥` with
    `SeedSign`: brick 16's `gaugeNeutral_iff_zero` saw only the single neutral *sign* `0` (because
    `SeedSign` has no `⊥`); the 4-element `SeedGauge` sees **both** swap-neutral poles —
    `untamped`/`⊥` (neutral-by-emptiness, before the commitment) *and* `zero`/`0` (neutral-by-fullness,
    declining it). `±` are the gauge-broken atoms the bridge (`bridge_breaks_fork_symmetry`, brick 12)
    selects between. -/
theorem SeedGauge.gaugeNeutral_iff (g : SeedGauge) :
    g.GaugeNeutral ↔ g = SeedGauge.untamped ∨ g = SeedGauge.zero := by
  unfold SeedGauge.GaugeNeutral
  cases g <;> decide

/-- **`SeedSign`-neutrality transports to the embedding** — `s.GaugeNeutral ↔ s.toGauge.GaugeNeutral`
    (via `swap_toGauge` + `toGauge` injective). So neutrality is preserved by the unification: a sign
    is swap-fixed in `SeedSign` iff its image is swap-fixed in `SeedGauge`. -/
theorem SeedSign.gaugeNeutral_toGauge_iff (s : SeedSign) :
    s.GaugeNeutral ↔ s.toGauge.GaugeNeutral := by
  unfold SeedSign.GaugeNeutral SeedGauge.GaugeNeutral
  rw [SeedSign.swap_toGauge]
  exact ⟨fun h => congrArg SeedSign.toGauge h, fun h => SeedSign.toGauge_injective h⟩

/-- **The image's only neutral element is `zero.toGauge`** — combining the transport with brick 16's
    `gaugeNeutral_iff_zero`. So among the embedded signs, `0` is the unique neutral one (as at the
    `SeedSign` level); the *extra* neutral pole `untamped` (`gaugeNeutral_iff`, `Or.inl`) is exactly
    the one *outside* the image (`toGauge_ne_untamped`) — the `⊥` pole unification introduces. -/
theorem SeedGauge.gaugeNeutral_toGauge_iff_zero (s : SeedSign) :
    s.toGauge.GaugeNeutral ↔ s = SeedSign.zero := by
  rw [← SeedSign.gaugeNeutral_toGauge_iff, SeedSign.gaugeNeutral_iff_zero]

/-- **Type-level swap-neutrality IS `Scope`-level value-neutrality** (under inj + tension) —
    `g.GaugeNeutral ↔ GaugeNeutralValue LP (g.seed LP)`. The combinatorial fixed-set `{untamped, zero}`
    (`gaugeNeutral_iff`) coincides, through `seed`, with brick 17's `Scope`-level `GaugeNeutralValue`
    poles `{⊥, 0}`: `untamped ↦ ⊥` (neutral-by-emptiness, `gaugeNeutralValue_bot`), `zero ↦ 0`
    (neutral-by-fullness, `gaugeNeutralValue_zero`), `±` gauge-broken (`not_gaugeNeutralValue_±`). This
    is *why* unifying into one type is the right move: the single type's gauge-swap has the correct
    fixed-set — the two `{⊥, 0}` poles brick 17 found at the `Scope` level — which the 3-element
    `SeedSign` (seeing only `{0}`) structurally could not express. -/
theorem SeedGauge.gaugeNeutral_iff_gaugeNeutralValue (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) (g : SeedGauge) :
    g.GaugeNeutral ↔ GaugeNeutralValue LP (g.seed LP) := by
  rw [SeedGauge.gaugeNeutral_iff]
  cases g
  · exact iff_of_true (Or.inl rfl) (gaugeNeutralValue_bot LP hboth)
  · refine iff_of_false ?_ (not_gaugeNeutralValue_plus LP hinj hboth)
    rintro (h | h) <;> exact absurd h (by decide)
  · refine iff_of_false ?_ (not_gaugeNeutralValue_minus LP hinj hboth)
    rintro (h | h) <;> exact absurd h (by decide)
  · exact iff_of_true (Or.inr rfl) (gaugeNeutralValue_zero LP)

/-! ## The commitment as a basepoint-step — source = target = `SeedGauge`, `untamped` the unit -/

/-- **The single external commitment, as a basepoint-step.** Each sign-bearing gauge `s : SeedSign` is
    the target of the one step `untamped → commit s` out of the un-tamped basepoint. Because source =
    target = `SeedGauge`, the commitment is not a function between two types but a *based-map within
    one lattice* — the endo-structure brick 17 recognized in prose, now with `untamped` the unit
    (no-commitment / functor input) and `commit` the three steps to the outputs `{+, −, 0}`. -/
def SeedGauge.commit (s : SeedSign) : SeedGauge := s.toGauge

/-- The commitment-step always leaves the basepoint: committing produces a sign-bearing gauge, never
    the un-tamped ground. -/
theorem SeedGauge.commit_ne_untamped (s : SeedSign) :
    SeedGauge.commit s ≠ SeedGauge.untamped :=
  SeedSign.toGauge_ne_untamped s

/-- The arrow of each commitment-step is brick 10's `bot_le_seed`: the basepoint's seed below the
    committed seed. -/
theorem SeedGauge.untamped_le_commit (LP : LedgerPersistence) (s : SeedSign) :
    SeedGauge.untamped.seed LP ≤ (SeedGauge.commit s).seed LP :=
  SeedGauge.untamped_le_seed LP _

/-- **Every gauge is the basepoint or a commitment** — `g = untamped ∨ ∃ s, g = commit s`. The unified
    type is exactly the un-tamped input together with the three sign-bearing outputs of the one
    commitment; there is no fourth kind of element. -/
theorem SeedGauge.eq_untamped_or_commit (g : SeedGauge) :
    g = SeedGauge.untamped ∨ ∃ s : SeedSign, g = SeedGauge.commit s := by
  cases g
  · exact Or.inl rfl
  · exact Or.inr ⟨SeedSign.plus, rfl⟩
  · exact Or.inr ⟨SeedSign.minus, rfl⟩
  · exact Or.inr ⟨SeedSign.zero, rfl⟩

end Foam
