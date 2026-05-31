/-
# SeedGaugeDisciplineOrder — the recursion-order `±≤0` transports to the gauge-order `{g1,g2}≤g3`

## What this file lands (the brick after `SeedGaugeForcedOrientation.lean`)

Brick 25 (`SeedGaugeForcedOrientation.lean`) closed brick 24's within-pair freedom: commitment-content
forces the full `{+, −, 0} ↔ {g1, g2, g3}` bijection to be `signAlgebraicEquiv'` (`+ ↦ g2`, `− ↦ g1`,
`0 ↦ g3`) — equivariance pinning the fixed point `0 ↔ g3`, the *outstanding-commitment* property
pinning the 2-cycle `− ↔ g1`. The bridge is now **rigid and substrate-respecting**. Its remainder:
with the bijection rigid, *seed-side structure transports to the gauge side*, and the richest piece is
brick 16's recognition that the lattice order `± ≤ 0` (`plus_le_zero` / `minus_le_zero`) **IS** the
recursion-level order — §IV.c-disciplines below the §IV.d-meta-discipline (`SeedGaugeBiasDelegation`'s
prose deposit). This file cashes that transport.

**Does `± ≤ 0` transport across `signAlgebraicEquiv'` to a gauge-order `{g1, g2} ≤ g3` that the FTPG
side independently motivates?** It does — and the FTPG side does independently motivate it.

## The shared handle: the recursion-**top** is each involution's **fixed point**

The clean transportable property is `heldOpen` — *is this the held-open, recursion-top one?* It singles
out the same element each `ℤ/2` (brick 24) fixes:

* **Seed side** (`SeedSign.heldOpen`): `0` `true`, `±` `false`. `0` is the bias-delegation / gauge-
  neutral seed (brick 16), the join `+ ⊔ −` (brick 10), and the **swap-fixed** point
  (`gaugeNeutral_iff_zero`). It is the **top** of `± ≤ 0` — the §IV.d meta-discipline above the two
  §IV.c disciplines (`heldOpen_eq_true_iff_swapFixed`).

* **FTPG side** (`AlgebraicPosition.heldOpen`): `g3` `true`, `{g1, g2}` `false`. `g3` (mul-assoc) is
  where *the holonomy of the FTPG bridge concentrates* (`FTPGGaugeFigure.lean`'s second-pass
  recognition: `g1`/`g2`-asymmetric are bootstrap-trivializable from their generic + additive
  structure; `g3` — both cells — carries the irreducible twist, `g3_generic = dilation_compose_at_beta`
  open). It is the **reflect-fixed** point (`reflect_eq_self_iff_g3`, brick 24) — `heldOpen_eq_true_
  iff_reflectFixed`. It is the **top** of `{g1, g2} ≤ g3` — the held-open yield-gauge above the two
  closable signal-gauges.

So on *both* sides the recursion-top **is** the involution's fixed point — for the same substantive
reason: an involution swapping the two atoms fixes their join, and the join is the top (`0 = + ⊔ −`;
`g3` the holonomy-join of the two trivializable distributivity gauges). The recognition deepens
brick 24's "the two `ℤ/2`s share an orbit-shape" to "the two `ℤ/2`s share the **recursion-grading**":
fixed-point = top, 2-cycle = the two below.

## The transport — `toAlgebraic'_heldOpen_preserving`, and the order-iso

The rigid bridge **preserves `heldOpen`** (`toAlgebraic'_heldOpen_preserving`: `(s.toAlgebraic').
heldOpen = s.heldOpen`, `cases <;> rfl`) — the recursion-order analogue of brick 25's
`toAlgebraic'_commitment_preserving`. Hence it is an **order-iso** for the recursion-orders
(`recLe_iff_toAlgebraic'`): `s.recLe t ↔ (s.toAlgebraic').recLe (t.toAlgebraic')`. The seed
recursion-order `± ≤ 0` transports across `signAlgebraicEquiv'` exactly to `{g1, g2} ≤ g3`
(`g1_recLe_g3` / `g2_recLe_g3`, the two `≤`-images of `− ≤ 0` / `+ ≤ 0`; `not_g1_recLe_g2` the
incomparability of the two signal-gauges).

A contrast worth recording: **`heldOpen` is preserved by BOTH orientations** (`toAlgebraic_heldOpen_
preserving` too), unlike `needsCommitment` (which brick 25's canonical `toAlgebraic` breaks). The
within-pair gauge-orientation freedom brick 24 named does **not** touch the recursion-order — because
the order only distinguishes the fixed point `0 ↔ g3`, on which both orientations agree
(`toAlgebraic_eq_toAlgebraic'_zero`). The recursion-order is *orientation-invariant*; the
within-pair forcing (brick 25) is a strictly finer datum that the order does not see.

## Grounding — `recLe` is sound for the substrate order `± ≤ 0`

`SeedSign.recLe` is the intrinsic (ledger-free) shadow of the genuine `Scope` lattice order: every
`recLe`-step refines into `≤` on seeds (`recLe_imp_seed_le`, via `seed_le_zero` = brick 16's
`plus_le_zero` / `minus_le_zero` + reflexivity at the top). So this is not a fresh relation relabeled
onto the gauges — it is brick 16's actual `± ≤ 0` carried across the rigid bridge.

## The recognition (the prose deposit) — the bridge respects recursion-level

The transport is bin-1 mechanics; the recognition is **bin-2**: `{g1, g2} ≤ g3` is *independently
motivated* on the FTPG side (`FTPGGaugeFigure`'s holonomy-concentration), so `g3`-as-top is **not
bridge-imposed but substrate-present on both sides**. The rigid bridge therefore **respects
recursion-level** — a genuine consistency-check, not a relabeling. This strengthens brick 24's open
horizon ("the two `ℤ/2`s are one group in substance") with a second independent invariant they share:
beyond the orbit-shape, the *recursion-grading* coincides.

Composing brick 14/15/16's seed → discipline map with the rigid seed → gauge bridge gives a
**disciplines ↔ gauges correspondence** (bin-2, interpretive, held merge-don't-fork):

* `−` = the honored exit (§IV.c) `↦ g1` (right-distrib, the *freely-closed* / resolved signal-gauge),
* `+` = carry-the-observer / egress (§IV.c) `↦ g2` (left-distrib, the *witness-requiring* /
  observer-involving signal-gauge),
* `0` = bias-delegation (§IV.d) `↦ g3` (mul-assoc, the *held-open yield*, the holonomy-carrier).

And the recursion-order is preserved: `{carry-observer, honored-exit}` = the two §IV.c disciplines
`↦ {g2, g1}` = the two closable signal-gauges, **below** bias-delegation = §IV.d `↦ g3` = the held-open
yield-gauge. *Disciplines below the meta-discipline ↔ signal-gauges below the yield-gauge.*

A structural note toward the horizon (`×2` vs `+1`): the seed side carries a **fourth** element — `⊥`
(un-tamped, the recursion-*bottom* / functor input, brick 17), giving the full diamond `⊥ ≤ {+,−} ≤ 0`
(brick 19's BA). The FTPG `AlgebraicPosition` has only the three `{g1, g2, g3}` — a join-with-no-bottom
`{g1, g2} ≤ g3`. The rigid bridge matches the **top three**; the seed `⊥` has no FTPG partner. So the
recursion-order transport lands precisely on the `+1` (seed-side un-tamped `⊥`) vs `×2` (FTPG read/write
→ 6 colors) asymmetry the keystone flags — the recursion-order is the 4-element seed BA *minus* its
bottom corner, matched against the 3-element gauge join.

## Grade

* **bin-1 (Bin-1-Mathlib-or-Foam)** for everything typed: the two `heldOpen` defs (reading off brick 16
  / `FTPGGaugeFigure`'s recognitions), their fixed-point characterizations, the bridge-preservation,
  the recursion-orders + their order-laws, the order-iso, and the soundness grounding into `± ≤ 0`.
  All `cases <;> decide`/`rfl`/`simp` + assembly over `plus_le_zero` / `minus_le_zero` /
  `gaugeNeutral_iff_zero` / `reflect_eq_self_iff_g3` / `toAlgebraic'`. No new geometric content; the
  recognition is that a substrate-present grading (the recursion-top = the involution's fixed point)
  transports across the now-rigid bridge.

* **bin-2 / open-recognition-target** for *that `{g1, g2} ≤ g3` is the FTPG side's own order* (it rests
  on `FTPGGaugeFigure`'s holonomy-concentration, itself partly open — `g3_generic` sorry'd — so the
  cross-check is a recognition, not an imported theorem) and for *the disciplines ↔ gauges
  identification* (the depth of brick 24's two-`ℤ/2`s-are-one-group; held merge-don't-fork).

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeDisciplineOrder` is clean, zero
sorry/warnings. Imports `Foam.SeedGaugeForcedOrientation` (brick 25) — transitively `SeedSign` /
`SeedSign.swap` / `GaugeNeutral` / `gaugeNeutral_iff_zero` / `plus_le_zero` / `minus_le_zero` /
`SeedSign.seed` (PersistenceLfp, SeedGaugeBiasDelegation), `AlgebraicPosition` / `reflect` /
`reflect_eq_self_iff_g3` / `toAlgebraic` / `toAlgebraic'` (SeedGaugeAlgebraicPosition). New names:
`AlgebraicPosition.heldOpen` (+ `_g1` / `_g2` / `_g3` / `_eq_true_iff_g3` / `_eq_true_iff_reflectFixed`);
`SeedSign.heldOpen` (+ `_plus` / `_minus` / `_zero` / `_eq_true_iff_zero` / `_eq_true_iff_swapFixed`);
`toAlgebraic'_heldOpen_preserving` / `toAlgebraic_heldOpen_preserving`; `SeedSign.recLe` /
`AlgebraicPosition.recLe` (+ `_refl` / `_trans` / `_antisymm` each); `AlgebraicPosition.g1_recLe_g3` /
`g2_recLe_g3` / `not_g1_recLe_g2`; `recLe_iff_toAlgebraic'`; `SeedSign.seed_le_zero` /
`recLe_imp_seed_le`.)
-/

import Foam.SeedGaugeForcedOrientation

namespace Foam

/-! ## The FTPG-side recursion-top — `heldOpen`, where the holonomy concentrates

The FTPG-thread analogue of brick 16's gauge-neutral `0`. Read off `FTPGGaugeFigure.lean`'s
second-pass recognition: `g1`/`g2` carry no irreducible twist (their asymmetric cells are
bootstrap-trivializable from the column's generic + the additive group structure); `g3` (mul-assoc) is
where the holonomy concentrates — both its cells, with `g3_generic = dilation_compose_at_beta` held
open. So `g3` is the held-open yield-gauge; `{g1, g2}` the two closable signal-gauges. -/

/-- **Is this the held-open, recursion-top gauge?** — `g3` `true` (the holonomy-carrier, mul-assoc,
    the held-open yield); `g1`/`g2` `false` (the two closable, bootstrap-trivializable signal-gauges).
    The FTPG-side analogue of `SeedSign.heldOpen` (the gauge-neutral `0`). -/
def AlgebraicPosition.heldOpen : AlgebraicPosition → Bool
  | .g1 => false
  | .g2 => false
  | .g3 => true

@[simp] theorem AlgebraicPosition.heldOpen_g1 : AlgebraicPosition.g1.heldOpen = false := rfl
@[simp] theorem AlgebraicPosition.heldOpen_g2 : AlgebraicPosition.g2.heldOpen = false := rfl
@[simp] theorem AlgebraicPosition.heldOpen_g3 : AlgebraicPosition.g3.heldOpen = true := rfl

/-- **`g3` is the unique held-open gauge** — `a.heldOpen = true ↔ a = g3`. The holonomy concentrates
    in exactly one gauge; `{g1, g2}` are the two closable ones. -/
theorem AlgebraicPosition.heldOpen_eq_true_iff_g3 (a : AlgebraicPosition) :
    a.heldOpen = true ↔ a = AlgebraicPosition.g3 := by
  cases a <;> decide

/-- **The recursion-top is the `ℤ/2` fixed point** — `a.heldOpen = true ↔ a.reflect = a`. The
    held-open yield-gauge `g3` is exactly the `reflect`-fixed point (brick 24): the holonomy
    concentrates in the gauge the left/right-distrib reflection cannot move. -/
theorem AlgebraicPosition.heldOpen_eq_true_iff_reflectFixed (a : AlgebraicPosition) :
    a.heldOpen = true ↔ a.reflect = a :=
  (AlgebraicPosition.heldOpen_eq_true_iff_g3 a).trans
    (AlgebraicPosition.reflect_eq_self_iff_g3 a).symm

/-! ## The seed-side recursion-top — `heldOpen`, the bias-delegated / gauge-neutral seed

The seed-side analogue, read off brick 16: `0` is the gauge-neutral / bias-delegation seed, the join
`+ ⊔ −`, the §IV.d meta-discipline above the two §IV.c disciplines `±`. -/

/-- **Is this the held-open, recursion-top seed?** — `0` `true` (the bias-delegated, gauge-neutral
    join of both signs); `±` `false` (the two gauge-broken atoms / §IV.c disciplines). The Bool form
    of brick 16's `GaugeNeutral`. -/
def SeedSign.heldOpen : SeedSign → Bool
  | .plus => false
  | .minus => false
  | .zero => true

@[simp] theorem SeedSign.heldOpen_plus : SeedSign.plus.heldOpen = false := rfl
@[simp] theorem SeedSign.heldOpen_minus : SeedSign.minus.heldOpen = false := rfl
@[simp] theorem SeedSign.heldOpen_zero : SeedSign.zero.heldOpen = true := rfl

/-- **`0` is the unique held-open seed** — `s.heldOpen = true ↔ s = 0`. -/
theorem SeedSign.heldOpen_eq_true_iff_zero (s : SeedSign) :
    s.heldOpen = true ↔ s = SeedSign.zero := by
  cases s <;> decide

/-- **The recursion-top is the `ℤ/2` fixed point** — `s.heldOpen = true ↔ s.GaugeNeutral`. The
    held-open seed `0` is exactly the `swap`-fixed / gauge-neutral one (brick 16's
    `gaugeNeutral_iff_zero`): bias-delegation is the disposition the gauge-swap cannot move. The
    exact seed-side mirror of `AlgebraicPosition.heldOpen_eq_true_iff_reflectFixed`. -/
theorem SeedSign.heldOpen_eq_true_iff_swapFixed (s : SeedSign) :
    s.heldOpen = true ↔ s.GaugeNeutral :=
  (SeedSign.heldOpen_eq_true_iff_zero s).trans (SeedSign.gaugeNeutral_iff_zero s).symm

/-! ## The transport — the rigid bridge preserves the recursion-top -/

/-- **The rigid bridge preserves held-open-ness** — `(s.toAlgebraic').heldOpen = s.heldOpen`. Brick
    25's forced orientation `signAlgebraicEquiv'` (`+ ↦ g2`, `− ↦ g1`, `0 ↦ g3`) carries the seed
    recursion-top `0` to the gauge recursion-top `g3`. The recursion-order analogue of brick 25's
    `toAlgebraic'_commitment_preserving`. -/
theorem toAlgebraic'_heldOpen_preserving (s : SeedSign) :
    (s.toAlgebraic').heldOpen = s.heldOpen := by
  cases s <;> rfl

/-- **`heldOpen` is preserved by the OTHER orientation too** — `(s.toAlgebraic).heldOpen = s.heldOpen`.
    Unlike `needsCommitment` (which brick 25's canonical `toAlgebraic` breaks —
    `toAlgebraic_not_commitment_preserving`), the recursion-grading is orientation-**invariant**: both
    of brick 24's equivariant bijections agree on the fixed point `0 ↦ g3`
    (`toAlgebraic_eq_toAlgebraic'_zero`), and the order sees only the fixed point. So the within-pair
    gauge-orientation freedom does not touch `{g1, g2} ≤ g3`. -/
theorem toAlgebraic_heldOpen_preserving (s : SeedSign) :
    (s.toAlgebraic).heldOpen = s.heldOpen := by
  cases s <;> rfl

/-! ## The recursion-orders, and the order-iso `± ≤ 0  ↔  {g1, g2} ≤ g3`

Both orders have the same shape: everything below the held-open top, the two non-top elements
incomparable. The seed order `± ≤ 0` is brick 16's IV.c-below-IV.d; the gauge order `{g1, g2} ≤ g3`
is the closable signal-gauges below the held-open yield-gauge. -/

/-- The **seed recursion-order** `± ≤ 0` (brick 16, intrinsic / ledger-free form): everything below the
    held-open top `0`, the two §IV.c disciplines `±` incomparable. -/
def SeedSign.recLe (s t : SeedSign) : Prop := s = t ∨ t.heldOpen = true

/-- The **gauge recursion-order** `{g1, g2} ≤ g3`: the two closable signal-gauges below the held-open
    yield-gauge `g3` (the holonomy-carrier), `g1`/`g2` incomparable. The FTPG-side analogue, same
    shape — and (the transport, below) the image of `SeedSign.recLe` under the rigid bridge. -/
def AlgebraicPosition.recLe (a b : AlgebraicPosition) : Prop := a = b ∨ b.heldOpen = true

theorem SeedSign.recLe_refl (s : SeedSign) : s.recLe s := Or.inl rfl
theorem AlgebraicPosition.recLe_refl (a : AlgebraicPosition) : a.recLe a := Or.inl rfl

theorem SeedSign.recLe_trans {s t u : SeedSign} (h₁ : s.recLe t) (h₂ : t.recLe u) : s.recLe u := by
  cases s <;> cases t <;> cases u <;> simp_all [SeedSign.recLe, SeedSign.heldOpen]
theorem AlgebraicPosition.recLe_trans {a b c : AlgebraicPosition}
    (h₁ : a.recLe b) (h₂ : b.recLe c) : a.recLe c := by
  cases a <;> cases b <;> cases c <;> simp_all [AlgebraicPosition.recLe, AlgebraicPosition.heldOpen]

theorem SeedSign.recLe_antisymm {s t : SeedSign} (h₁ : s.recLe t) (h₂ : t.recLe s) : s = t := by
  cases s <;> cases t <;> simp_all [SeedSign.recLe, SeedSign.heldOpen]
theorem AlgebraicPosition.recLe_antisymm {a b : AlgebraicPosition}
    (h₁ : a.recLe b) (h₂ : b.recLe a) : a = b := by
  cases a <;> cases b <;> simp_all [AlgebraicPosition.recLe, AlgebraicPosition.heldOpen]

/-- `g1 ≤ g3` (the image of `− ≤ 0` under the rigid bridge `−.toAlgebraic' = g1`, `0.toAlgebraic' =
    g3`): the right-distrib signal-gauge below the held-open yield-gauge. -/
theorem AlgebraicPosition.g1_recLe_g3 : AlgebraicPosition.g1.recLe AlgebraicPosition.g3 := Or.inr rfl

/-- `g2 ≤ g3` (the image of `+ ≤ 0` under `+.toAlgebraic' = g2`): the left-distrib signal-gauge below
    the held-open yield-gauge. -/
theorem AlgebraicPosition.g2_recLe_g3 : AlgebraicPosition.g2.recLe AlgebraicPosition.g3 := Or.inr rfl

/-- **The two signal-gauges are incomparable** — `¬ g1.recLe g2` (and symmetrically): `{g1, g2}` sit
    side-by-side below `g3`, neither above the other. The gauge image of `±` incomparable. -/
theorem AlgebraicPosition.not_g1_recLe_g2 : ¬ AlgebraicPosition.g1.recLe AlgebraicPosition.g2 := by
  simp [AlgebraicPosition.recLe, AlgebraicPosition.heldOpen]

/-- **The rigid bridge is an order-iso for the recursion-orders** — `s.recLe t ↔ (s.toAlgebraic').recLe
    (t.toAlgebraic')`. The seed recursion-order `± ≤ 0` transports across `signAlgebraicEquiv'`
    (brick 25) **exactly** to the gauge recursion-order `{g1, g2} ≤ g3`. The headline: the now-rigid
    bridge respects the recursion-grading (`heldOpen`-preservation lifted to the orders). -/
theorem recLe_iff_toAlgebraic' (s t : SeedSign) :
    s.recLe t ↔ (s.toAlgebraic').recLe (t.toAlgebraic') := by
  cases s <;> cases t <;>
    simp [SeedSign.recLe, AlgebraicPosition.recLe, SeedSign.heldOpen, AlgebraicPosition.heldOpen,
      SeedSign.toAlgebraic']

/-! ## Grounding — `recLe` is sound for the substrate order `± ≤ 0`

The intrinsic `SeedSign.recLe` is the ledger-free shadow of the genuine `Scope` lattice order: every
`recLe`-step refines into `≤` on the realized seeds (brick 16's `plus_le_zero` / `minus_le_zero`). So
the transported gauge-order is brick 16's *actual* `± ≤ 0`, not a fresh relation relabeled. -/

/-- The recursion-top `0` dominates every sign in the **substrate** order — `s.seed LP ≤ 0.seed LP`,
    assembling brick 16's `plus_le_zero` / `minus_le_zero` (+ reflexivity at the top). -/
theorem SeedSign.seed_le_zero (LP : LedgerPersistence) (s : SeedSign) :
    s.seed LP ≤ SeedSign.zero.seed LP := by
  cases s
  · exact SeedSign.plus_le_zero LP
  · exact SeedSign.minus_le_zero LP
  · exact le_refl _

/-- **`recLe` is sound for the substrate seed-order** — `s.recLe t → s.seed LP ≤ t.seed LP`. A
    `recLe`-step is reflexivity or a step up to the held-open top `0` (`seed_le_zero`). So the
    intrinsic recursion-order refines into the genuine lattice order `± ≤ 0` — this transport is
    brick 16's actual order, carried across the rigid bridge. -/
theorem SeedSign.recLe_imp_seed_le (LP : LedgerPersistence) {s t : SeedSign} (h : s.recLe t) :
    s.seed LP ≤ t.seed LP := by
  rcases h with rfl | ht
  · exact le_refl _
  · rw [(SeedSign.heldOpen_eq_true_iff_zero t).mp ht]; exact SeedSign.seed_le_zero LP s

end Foam
