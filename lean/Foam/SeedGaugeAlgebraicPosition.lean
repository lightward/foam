/-
# SeedGaugeAlgebraicPosition — the seed-gauge `ℤ/2` IS the left/right-distrib reflection

## What this file lands (the brick after `SeedGaugeFaithful.lean`)

Brick 23 (`SeedGaugeFaithful.lean`) established that the single-external-commitment functor is
**faithful** under unresolved tension — it *embeds* the commitment-category, so its three non-trivial
commitments `{+, −, 0}` (the image of `SeedSign.toGauge` in `SeedGauge`) are a **genuinely-distinct**
triple. That well-poses the keystone's highest-value open target, the **3-cluster ↔ 3-gauge** match:
matching `{+, −, 0}` to the three σ-ring-hom gauges `{g1, g2, g3}` (`AlgebraicPosition`) is now
*meaningful* rather than vacuous. This file lays the **first bounded step**, and is the **first file
to bridge the two threads** that have been disconnected in the lean — the persistence/commitment
thread (`SeedSign`, from `PersistenceLfp` onward) and the FTPG/gauge thread (`AlgebraicPosition`, used
until now *only* in `StatelessSubstrate.lean`).

## The recognition that makes this the bounded step: a shared `ℤ/2`

Both 3-element sets carry a `ℤ/2` involution with the **same orbit-shape — one fixed point + one
two-cycle.**

* **Seed-gauge side** (landed, bricks 16/18): `SeedSign.swap` (`+ ↔ −`, `0 ↦ 0`) fixes `0` — the
  gauge-neutral / bias-delegation / *declined-commitment* seed (brick 16's `gaugeNeutral_iff_zero`),
  the join `+ ⊔ −` carrying both signs uncollapsed — and exchanges the two **gauge-broken atoms**
  `±` (the live self `+` and the settled `−` the bridge selects between, `bridge_breaks_fork_symmetry`).

* **Gauge side** (typed here): `AlgebraicPosition.reflect` — the **left/right-distributivity
  reflection** — fixes `g3` (mul-associativity: the `·`-preservation gauge, the *held-open* yield /
  silence-channel, the `dilation_compose_at_beta` site, README §VII's third crossing) and exchanges
  `g1 ↔ g2` (right-distributivity ↔ left-distributivity: the two `+`-preservation gauges, both
  *closable* signal gauges — `g1` proven as `coord_mul_right_distrib`, `g2` via `DesarguesianWitness`).
  Distributivity comes in a left and a right form (a genuine pair); associativity is the symmetric
  one with no left/right partner — so the reflection that swaps the distributivity pair fixes the
  associativity gauge.

## The forced fixed-point match — `0 ↔ g3`, not observer-supplied

`signAlgebraicEquiv : SeedSign ≃ AlgebraicPosition` (`+ ↦ g1`, `− ↦ g2`, `0 ↦ g3`) is the bijection,
and it is **`ℤ/2`-equivariant**: `signAlgebraicEquiv s.swap = (signAlgebraicEquiv s).reflect`
(`signAlgebraicEquiv_equivariant`) — crossing the bridge conjugates `swap` into `reflect`. The
fixed-point match is then **forced, not chosen**: `equivariant_zero` proves that *any* equivariant
map `e : SeedSign → AlgebraicPosition` (bijection or not) sends `0 ↦ g3`, because `0` is the unique
swap-fixed sign and `g3` the unique reflect-fixed gauge (a fixed point can only go to a fixed point).
Dually `equivariant_g3` sends `g3 ↦ 0`. So `0 ↔ g3` is **forced by the shared `ℤ/2`** — the match is
not observer-supplied.

## The within-pair freedom IS the gauge-orientation — bias-delegation

What the shared `ℤ/2` does *not* fix is the **within-pair assignment**: `+ ↦ g1, − ↦ g2`
(`signAlgebraicEquiv`) and `+ ↦ g2, − ↦ g1` (`signAlgebraicEquiv'`) are **both** equivariant
bijections (`toAlgebraic_swap` / `toAlgebraic'_swap`), differing on the broken atoms
(`toAlgebraic_ne_toAlgebraic'_plus`). The two orientations are related by **post-composing the FTPG
reflection, equivalently pre-composing the seed-gauge swap** (`toAlgebraic'_eq_postReflect` /
`toAlgebraic'_eq_preSwap`: `s.toAlgebraic' = s.toAlgebraic.reflect = s.swap.toAlgebraic`). So the
residual freedom `+ ↔ g1` vs `+ ↔ g2` **is** the gauge-orientation — the same symmetry-break that
`bridge_breaks_fork_symmetry` (brick 12) performs in selecting `+` over `−` is the act of orienting
right-vs-left distributivity. Per the §IV.d bias-delegation discipline (the seed `0` itself, brick 16),
this within-pair choice is **held open, not pre-collapsed**.

## The recognition (the prose deposit)

**The seed-gauge swap IS the left/right-distrib reflection.** Through the bridge they are *one*
involution (the equivariance is a conjugacy). The gauge-neutral / declined-commitment seed `0` IS the
held-open yield-gauge `g3` — both are the swap/reflect-**fixed**, neutral, *un-broken* one (the one
that declines to commit / stays open: `0` carries both signs, `g3` carries the open silence-channel).
The two gauge-broken atoms `±` ARE the two closable signal-gauges `g1/g2` — both the commitments the
external act *resolves*. The fixed-point match is forced; the within-pair match is the free
gauge-orientation. This is the first cross-thread bridge — the commitment-thread's `ℤ/2` and the
FTPG-thread's `ℤ/2` are the same group acting, identified through a single equivariant bijection.

## Grade

* **bin-1 (Bin-1-Mathlib-or-Foam)** for everything *typed here*: the gauge-side `ℤ/2` and its
  orbit-shape (`reflect`, `reflect_reflect`, `reflect_eq_self_iff_g3` — `cases <;> rfl`/`decide`), the
  equivariant bijection and its equivariance (`cases <;> rfl`), the forced fixed-point
  (`equivariant_zero` / `equivariant_g3` — assembling `reflect_eq_self_iff_g3` and brick 16's
  `gaugeNeutral_iff_zero`), and the freedom (the two orientations, `decide`). No new geometric
  content; the recognition is that the two `ℤ/2`s coincide through the bijection.

* **bin-2 / open-recognition-target** for *why this is the right match and not a coincidence*. The
  combinatorics force fixed↦fixed once you posit the equivariant bijection, but *that the seed-gauge
  `swap` and the distrib `reflect` are the same `ℤ/2` in substance* — rather than two `ℤ/2`s that
  happen to share an orbit-shape — is the deeper content: the `self_dual_iff_three` 6→3 collapse
  (`Rank.lean`), the `×2` read/write scrambling, README §VII's cluster-bijective HK map. That "why" is
  the horizon beyond this brick (evidence for the bireflective conjecture), not claimed here. What is
  claimed: *if* the two `ℤ/2`s are identified, the fixed-point match `0 ↔ g3` is **not** a further
  choice — it is forced.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeAlgebraicPosition` is clean, zero
sorry/warnings. Imports `Foam.SeedGaugeFaithful` (brick 23, the chain head) — transitively gives
`SeedSign` / `SeedSign.swap` / `SeedSign.gaugeNeutral_iff_zero` (PersistenceLfp / SeedGaugeBiasDelegation)
and `AlgebraicPosition` (StatelessSubstrate). New names: `AlgebraicPosition.reflect` /
`reflect_reflect` / `reflect_g1` / `reflect_g2` / `reflect_g3` / `reflect_eq_self_iff_g3`;
`SeedSign.toAlgebraic` / `AlgebraicPosition.toSign` / `signAlgebraicEquiv` / `signAlgebraicEquiv_apply`
/ `SeedSign.toAlgebraic_swap` / `signAlgebraicEquiv_equivariant` / `swap_conj_eq_reflect`;
`toAlgebraic_plus` / `toAlgebraic_minus` / `toAlgebraic_zero` / `equivariant_zero` / `equivariant_g3`;
`SeedSign.toAlgebraic'` / `AlgebraicPosition.toSign'` / `signAlgebraicEquiv'` / `toAlgebraic'_swap` /
`toAlgebraic'_eq_postReflect` / `toAlgebraic'_eq_preSwap` / `toAlgebraic_ne_toAlgebraic'_plus`.)
-/

import Foam.SeedGaugeFaithful

namespace Foam

/-! ## The gauge-side `ℤ/2` — the left/right-distributivity reflection

The FTPG-thread analogue of brick 16's `SeedSign.swap`. The σ-ring-hom gauges `{g1, g2, g3}`
(`AlgebraicPosition`, `StatelessSubstrate.lean`) carry a `ℤ/2` exchanging the two *distributivity*
gauges — `g1` (right-distrib) `↔` `g2` (left-distrib) — and fixing the *associativity* gauge `g3`.
Distributivity has a left and a right form; associativity is the symmetric one. -/

/-- **The left/right-distributivity reflection** — the `ℤ/2` action on the three gauges exchanging the
    two distributivity gauges and fixing mul-associativity. `g1` (right-distrib) `↔` `g2` (left-distrib);
    `g3` (mul-assoc, the held-open yield/silence-channel) fixed. The FTPG-side analogue of brick 16's
    `SeedSign.swap`. -/
def AlgebraicPosition.reflect : AlgebraicPosition → AlgebraicPosition
  | .g1 => .g2
  | .g2 => .g1
  | .g3 => .g3

@[simp] theorem AlgebraicPosition.reflect_g1 : AlgebraicPosition.g1.reflect = AlgebraicPosition.g2 := rfl
@[simp] theorem AlgebraicPosition.reflect_g2 : AlgebraicPosition.g2.reflect = AlgebraicPosition.g1 := rfl
@[simp] theorem AlgebraicPosition.reflect_g3 : AlgebraicPosition.g3.reflect = AlgebraicPosition.g3 := rfl

/-- The reflection is an involution (`ℤ/2`): reflecting twice is the identity. -/
theorem AlgebraicPosition.reflect_reflect (a : AlgebraicPosition) : a.reflect.reflect = a := by
  cases a <;> rfl

/-- **`g3` is the unique reflection-fixed gauge** (pure combinatorics, no ledger) — `a.reflect = a ↔
    a = g3`. The FTPG-side analogue of brick 16's `SeedSign.gaugeNeutral_iff_zero` (`s.swap = s ↔
    s = 0`): each `ℤ/2` has exactly one fixed point. So `reflect`'s orbit-shape is **{1 fixed `g3` +
    1 two-cycle `g1 ↔ g2`}**, matching `swap`'s **{1 fixed `0` + 1 two-cycle `± `}**. -/
theorem AlgebraicPosition.reflect_eq_self_iff_g3 (a : AlgebraicPosition) :
    a.reflect = a ↔ a = AlgebraicPosition.g3 := by
  cases a <;> decide

/-! ## The bijection `SeedSign ≃ AlgebraicPosition`, and its equivariance

`{+, −, 0} ≃ {g1, g2, g3}`. The canonical orientation `+ ↦ g1`, `− ↦ g2`, `0 ↦ g3`. It is
`ℤ/2`-equivariant — it carries `SeedSign.swap` to `AlgebraicPosition.reflect`. -/

/-- The canonical correspondence `{+, −, 0} → {g1, g2, g3}`: `+ ↦ g1` (right-distrib), `− ↦ g2`
    (left-distrib), `0 ↦ g3` (mul-assoc, the held-open one). -/
def SeedSign.toAlgebraic : SeedSign → AlgebraicPosition
  | .plus => .g1
  | .minus => .g2
  | .zero => .g3

/-- The inverse correspondence `{g1, g2, g3} → {+, −, 0}`. -/
def AlgebraicPosition.toSign : AlgebraicPosition → SeedSign
  | .g1 => .plus
  | .g2 => .minus
  | .g3 => .zero

@[simp] theorem SeedSign.toAlgebraic_plus : SeedSign.plus.toAlgebraic = AlgebraicPosition.g1 := rfl
@[simp] theorem SeedSign.toAlgebraic_minus : SeedSign.minus.toAlgebraic = AlgebraicPosition.g2 := rfl
@[simp] theorem SeedSign.toAlgebraic_zero : SeedSign.zero.toAlgebraic = AlgebraicPosition.g3 := rfl

/-- **The bijection `SeedSign ≃ AlgebraicPosition`** — the three non-trivial commitments of the
    (faithful, brick 23) single-external-commitment functor matched with the three σ-ring-hom gauges.
    The first typed object bridging the persistence/commitment thread and the FTPG/gauge thread. -/
def signAlgebraicEquiv : SeedSign ≃ AlgebraicPosition where
  toFun := SeedSign.toAlgebraic
  invFun := AlgebraicPosition.toSign
  left_inv s := by cases s <;> rfl
  right_inv a := by cases a <;> rfl

@[simp] theorem signAlgebraicEquiv_apply (s : SeedSign) :
    signAlgebraicEquiv s = s.toAlgebraic := rfl

/-- **Equivariance at the function level** — `s.swap.toAlgebraic = s.toAlgebraic.reflect`: applying the
    seed-gauge swap then crossing the bridge equals crossing the bridge then applying the distrib
    reflection. The two `ℤ/2`s are the *same* involution seen through the correspondence. -/
theorem SeedSign.toAlgebraic_swap (s : SeedSign) :
    s.swap.toAlgebraic = s.toAlgebraic.reflect := by
  cases s <;> rfl

/-- **The bijection is `ℤ/2`-equivariant** — `signAlgebraicEquiv s.swap = (signAlgebraicEquiv s).reflect`.
    Crossing the bridge **conjugates** `swap` into `reflect`: `reflect = signAlgebraicEquiv ∘ swap ∘
    signAlgebraicEquiv⁻¹`. This is the precise sense in which *the seed-gauge swap IS the left/right-
    distrib reflection*. -/
theorem signAlgebraicEquiv_equivariant (s : SeedSign) :
    signAlgebraicEquiv s.swap = (signAlgebraicEquiv s).reflect :=
  SeedSign.toAlgebraic_swap s

/-- **The conjugacy spelled out, at the function level** — `(a.toSign.swap).toAlgebraic = a.reflect`:
    cross back to a sign, swap, cross forward = reflect. `reflect = toAlgebraic ∘ swap ∘ toSign`, the
    `Equiv.symm`-free form of the conjugation in `signAlgebraicEquiv_equivariant`. -/
theorem swap_conj_eq_reflect (a : AlgebraicPosition) :
    (a.toSign.swap).toAlgebraic = a.reflect := by
  cases a <;> rfl

/-! ## The forced fixed-point match — `0 ↔ g3`

The fixed-point correspondence is **not** a further choice. *Any* `ℤ/2`-equivariant map sends the
swap-fixed `0` to the reflect-fixed `g3` (and dually), because a fixed point can only map to a fixed
point. No bijectivity is needed for the forced direction. -/

/-- **Forced: every equivariant map sends `0 ↦ g3`.** For any `e : SeedSign → AlgebraicPosition` with
    `e s.swap = (e s).reflect`, `e 0 = g3` — because `0` is swap-fixed (`0.swap = 0`), so `e 0` is
    reflect-fixed (`(e 0).reflect = e 0`), so `e 0 = g3` (`reflect_eq_self_iff_g3`). The fixed-point
    match is **forced by the shared `ℤ/2`**, not observer-supplied — and it does not even require `e`
    to be a bijection. -/
theorem equivariant_zero (e : SeedSign → AlgebraicPosition)
    (he : ∀ s, e s.swap = (e s).reflect) :
    e SeedSign.zero = AlgebraicPosition.g3 := by
  rw [← AlgebraicPosition.reflect_eq_self_iff_g3]
  exact (he SeedSign.zero).symm

/-- **Forced, dually: every equivariant map sends `g3 ↦ 0`.** For any `d : AlgebraicPosition →
    SeedSign` with `d a.reflect = (d a).swap`, `d g3 = 0` — `g3` reflect-fixed ⟹ `d g3` swap-fixed ⟹
    `d g3 = 0` (brick 16's `gaugeNeutral_iff_zero`). -/
theorem equivariant_g3 (d : AlgebraicPosition → SeedSign)
    (hd : ∀ a, d a.reflect = (d a).swap) :
    d AlgebraicPosition.g3 = SeedSign.zero := by
  rw [← SeedSign.gaugeNeutral_iff_zero]
  show (d AlgebraicPosition.g3).swap = d AlgebraicPosition.g3
  exact (hd AlgebraicPosition.g3).symm

/-- The canonical bijection realizes the forced match (`signAlgebraicEquiv 0 = g3`): the concrete
    orientation's fixed-point value is the one `equivariant_zero` forces for *every* equivariant map. -/
example : SeedSign.zero.toAlgebraic = AlgebraicPosition.g3 :=
  equivariant_zero SeedSign.toAlgebraic SeedSign.toAlgebraic_swap

/-! ## The within-pair freedom IS the gauge-orientation

The shared `ℤ/2` forces `0 ↔ g3` but leaves the 2-cycle assignment free: `+ ↦ g1` and `+ ↦ g2` are
**both** equivariant bijections. The two are related by post-composing `reflect` (= pre-composing
`swap`) — so the within-pair choice *is* the gauge-orientation (`bridge_breaks_fork_symmetry`,
brick 12), held open per bias-delegation (brick 16). -/

/-- The **other** orientation `+ ↦ g2`, `− ↦ g1`, `0 ↦ g3` — the gauge-orientation flip of
    `SeedSign.toAlgebraic`. -/
def SeedSign.toAlgebraic' : SeedSign → AlgebraicPosition
  | .plus => .g2
  | .minus => .g1
  | .zero => .g3

/-- The inverse of the flipped orientation. -/
def AlgebraicPosition.toSign' : AlgebraicPosition → SeedSign
  | .g1 => .minus
  | .g2 => .plus
  | .g3 => .zero

/-- **The flipped orientation is also a bijection** `SeedSign ≃ AlgebraicPosition` — the second of the
    exactly-two equivariant bijections. -/
def signAlgebraicEquiv' : SeedSign ≃ AlgebraicPosition where
  toFun := SeedSign.toAlgebraic'
  invFun := AlgebraicPosition.toSign'
  left_inv s := by cases s <;> rfl
  right_inv a := by cases a <;> rfl

/-- **The flipped orientation is equivariant too** — both orientations carry `swap` to `reflect`. So
    `ℤ/2`-equivariance does *not* pin the within-pair assignment; it pins only the fixed point. -/
theorem SeedSign.toAlgebraic'_swap (s : SeedSign) :
    s.swap.toAlgebraic' = s.toAlgebraic'.reflect := by
  cases s <;> rfl

/-- **The orientation flip = post-composing the FTPG reflection** — `s.toAlgebraic' =
    s.toAlgebraic.reflect`. The second orientation is the first followed by the distrib reflection. -/
theorem SeedSign.toAlgebraic'_eq_postReflect (s : SeedSign) :
    s.toAlgebraic' = s.toAlgebraic.reflect := by
  cases s <;> rfl

/-- **The orientation flip = pre-composing the seed-gauge swap** — `s.toAlgebraic' = s.swap.toAlgebraic`.
    Together with `toAlgebraic'_eq_postReflect`, this is the statement that *the gauge-orientation flip
    on the FTPG side (post-`reflect`) equals the gauge-orientation flip on the seed-gauge side
    (pre-`swap`)* — the two `ℤ/2`s' within-pair freedoms are the same freedom, the symmetry-break
    `bridge_breaks_fork_symmetry` (brick 12). -/
theorem SeedSign.toAlgebraic'_eq_preSwap (s : SeedSign) :
    s.toAlgebraic' = s.swap.toAlgebraic := by
  cases s <;> rfl

/-- **The two orientations genuinely differ** — they disagree on the broken atom `+` (`g1` vs `g2`).
    So the within-pair gauge-orientation is a genuine free choice (≥ 2 options), not forced — held
    open per bias-delegation (`0`/`g3` being the *fixed* one declines the break; the `±`/`g1,g2`
    assignment is where the orientation lives). -/
theorem toAlgebraic_ne_toAlgebraic'_plus :
    SeedSign.plus.toAlgebraic ≠ SeedSign.plus.toAlgebraic' := by
  decide

/-- Both orientations agree on the fixed point `0 ↦ g3` — the forced match is orientation-independent. -/
theorem toAlgebraic_eq_toAlgebraic'_zero :
    SeedSign.zero.toAlgebraic = SeedSign.zero.toAlgebraic' := rfl

end Foam
