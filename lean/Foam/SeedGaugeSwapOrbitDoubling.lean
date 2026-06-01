/-
# SeedGaugeSwapOrbitDoubling — the seed `swap`-orbits, and the FTPG V₄-orbit as their `×2`-doubling

## What this file lands (the brick after `SeedGaugeKleinFourOrbits.lean`)

Brick 30 (`SeedGaugeKleinFourOrbits.lean`) computed the FTPG side's V₄-orbits on the 6-color tape and
showed they factor as gauge-`reflect`-orbit × fiber (`sameOrbit_iff_gauge`: the face is free), the
gauge-`reflect`-orbit being the *matched base* `ℤ/2` = the seed `swap`'s partner (bricks 24/29). Its
flagged remainder: the **seed-side** `swap`-orbits were still *cited prose* — the localization ("FTPG
`g3`-orbit size 2 vs seed `0`-orbit size 1, the difference the `×2`") was **one-sided** (no seed-side
orbit object typed *as an orbit*). This file types them, and exhibits the doubling **two-sided**.

## The recognition — the FTPG V₄-orbit is the seed `swap`-orbit, doubled by the surplus fiber `×2`

The seed side carries a single `ℤ/2` acting via `SeedSign.swap` (brick 16). We type it as an honest
group action `signAct : ZMod 2 → SeedSign → SeedSign` (the exact mirror of brick 29's base action
`gaugeAct` on gauges), with its orbits `SeedSign.swapOrbit` — the seed-side analogue of brick 30's
`tapeOrbit`. Two seed orbits:

* `{0}` (size 1) — the held-open recursion-top, `swap`-**fixed** (brick 16's `gaugeNeutral_iff_zero`);
* `{+, −}` (size 2) — the recursion-antichain, the two gauge-broken atoms the `swap` exchanges.

The **rigid bridge** `signAlgebraicEquiv'` (brick 25's commitment-forced orientation `+↦g2`, `−↦g1`,
`0↦g3`) **intertwines the seed action with the FTPG base action**: `toAlgebraic'_signAct` proves
`(signAct n s).toAlgebraic' = gaugeAct n (s.toAlgebraic')` — the seed `signAct`, carried across the
bridge, *IS* the base `gaugeAct` (the matched `ℤ/2` of brick 29's SES, now as an action-intertwiner, not
just a single-element conjugacy). So the seed `swap`-orbit of `s` carries to the `reflect`-orbit of
`s.toAlgebraic'` on gauges, and by brick 30's face-free projection the full V₄-orbit of `⟨s.toAlgebraic',
o⟩` is that gauge-orbit *times the free read/write fiber*. Hence the **uniform doubling**:

> `(tapeOrbit ⟨s.toAlgebraic', o⟩).card = 2 * (s.swapOrbit).card`     (`tapeOrbit_card_eq_two_mul_swapOrbit`)

* signal (`s = ±`): `4 = 2 · 2` (the V₄ acts freely on `{g1,g2}×{r,w}`);
* yield   (`s = 0`): `2 = 2 · 1` (the base degenerates at `g3`; only the fiber `×2` acts).

The doubling factor is **always `2`** — `Fintype.card ObserverState`, the fiber's free orbit — *never*
depending on the recursion-class (`tapeOrbit_card_eq_obs_mul_swapOrbit` names the factor). That is the
content of *uniform across recursion-classes*: the base contributes the seed `swap`-orbit-size (it matches
`swap` across the bridge), the **fiber** `×2` contributes the constant doubling, because the fiber is
free at *every* gauge (`fiber_free`, brick 29), held-open or not. So the seed `swap`-orbit and the FTPG
V₄-orbit are the *same orbit-structure*, the FTPG one carrying one extra free `ℤ/2` — the surplus fiber,
the `×2` — uniformly.

## The two-sided localization — brick 30's remainder, closed

At the shared recursion-top `0 ↔ g3` (bricks 24/26), the seed `swap`-orbit `{0}` is now typed *as an
orbit of size 1* (`swapOrbit_zero_card`) — a lone `swap`-fixed point — while the FTPG orbit is the bare
read/write fiber, size 2 (brick 30's `tapeOrbit_yield_card`). The doubling `2 = 2 · 1` makes precise
exactly what brick 30 could only say in prose: the held-open gauge is the *sharpest locus* of the
element-vs-symmetry surplus — where the seed has a single fixed point, the FTPG has the surplus fiber
`ℤ/2` (the `×2`) acting alone on its two faces.

## The fifth shared invariant; the `+1` stays orthogonal

This is a **fifth** structural fact shared between the two threads, after orbit-shape (b24),
recursion-grading (b26), involution-count/SES (b29), and orbit-grading (b30): the FTPG V₄-orbits are the
seed `swap`-orbits *uniformly doubled* by the surplus fiber `×2`. It is **two-sided** (both orbit-objects
typed *as orbits*, related across the bridge) where brick 30 had only the FTPG side.

The doubling story lives **entirely on the matched 3-core** `{+, −, 0} ↔ {g1, g2, g3}` and the `×2`. The
seed-side `+1` (the un-tamped `⊥`/`untamped`, brick 17, the recursion-*bottom*) has **no FTPG partner**
(bricks 26/28) and plays no role here — it is kept clean and separate, orthogonal to the `×2` doubling.
So this brick is the `×2` side of the keystone's `×2`-vs-`+1` asymmetry, read at the orbit level.

## NOT the coincidence-trap

This compares the *orbit structures of two actions* — the seed `swap`-action on `SeedSign` and the FTPG
V₄-action on `TapePosition` — mediated by the *substantive* bridge `signAlgebraicEquiv'` (a point-map
`SeedSign → AlgebraicPosition`, the brick 24/25 orbit-shape + commitment-content match) and the
gauge-projection `algebraic`. Everything is **points and actions**: `SameSwapOrbit` and `SameOrbit` are
relations on *points* (signs, colors); `toAlgebraic'` is a *point*-map. It is **not** a (type-confused)
`Bool×Bool ≃ Bool×Bool` bijection of commitment-*points* to symmetry-*elements* (a sign is a gauge/point;
`reflect`/`flip` are symmetries). The doubling is a relation between two actions' orbits, not a
points↔symmetries identification.

## Grade

* **bin-1 (Bin-1-Mathlib-or-Foam)** for everything typed: the seed `ℤ/2`-action `signAct` and its laws
  (`decide`, the exact mirror of brick 29's `gaugeAct`), the orbit relation + equivalence
  (`SameSwapOrbit`, assembling `signAct_involutive`/`signAct_add` exactly as brick 30 assembled the V₄
  group laws), the orbit Finsets + cardinalities `1`/`2`/`2` (`decide`), the action-intertwiner
  `toAlgebraic'_signAct` (`decide`, brick 25's `toAlgebraic'_swap` upgraded to the action form), the
  orbit-relation carry `sameSwapOrbit_iff_sameOrbit` (`decide`, brick 30's `sameOrbit_iff_gauge` idiom),
  and the cardinality doubling (assembling brick 30's `tapeOrbit_*_card` with the seed `swapOrbit_*_card`).
  No new geometric content; the recognition is that the *already-typed* base `gaugeAct`-orbit is the seed
  `swap`-orbit across the bridge, and the V₄-orbit is that, doubled by the free fiber.

* **bin-2 / interpretive** for the **fifth-shared-invariant reading** (held merge-don't-fork: the
  cardinality doubling is bin-1; the "the `×2` realized as the uniform doubling factor on the matched
  3-core, the `+1` orthogonal" reading is the deposit) and the two-sided localization. The deeper
  *substance* — the two `ℤ/2`s as **one group**, `+1 ≅ ×2` as one move at the rank-3 self-dual fixed
  point `g3 ↔ 0` — stays the **named horizon** (the bireflective coincidence, §VI), NOT this brick.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeSwapOrbitDoubling` is clean, zero
sorry/warnings. Imports `Foam.SeedGaugeKleinFourOrbits` (brick 30 — transitively `tapeOrbit` /
`SameOrbit` / `sameOrbit_iff_gauge` / `tapeOrbit_signal_card` / `tapeOrbit_signal_card_g2` /
`tapeOrbit_yield_card` from brick 30; `gaugeAct` / `gaugeAct_zero` from brick 29; `SeedSign.swap` /
`gaugeNeutral_iff_zero` from brick 16; `SeedSign.toAlgebraic'` / `toAlgebraic'_swap` /
`AlgebraicPosition.toSign'` / `signAlgebraicEquiv'` from brick 24; `Fintype SeedSign` /
`Fintype ObserverState` / `card_observerState` from brick 28; `AlgebraicPosition.toAlgebraic'_toSign'`
from brick 27). New names: `signAct` / `signAct_zero` / `signAct_one` / `signAct_add` /
`signAct_involutive` / `signAddAction`; `SeedSign.SameSwapOrbit` / `SameSwapOrbit.refl` / `.symm` /
`.trans` / `SeedSign.swapOrbit` / `mem_swapOrbit` / `swapOrbit_zero_card` / `swapOrbit_plus_card` /
`swapOrbit_minus_card`; `toAlgebraic'_signAct` / `sameSwapOrbit_iff_sameOrbit`;
`tapeOrbit_card_eq_two_mul_swapOrbit` / `tapeOrbit_card_eq_obs_mul_swapOrbit` /
`tapeOrbit_card_eq_two_mul_swapOrbit_of_color`. (Reuses `card_observerState` (b28) and
`AlgebraicPosition.toAlgebraic'_toSign'` (b27).)
-/

import Foam.SeedGaugeKleinFourOrbits

namespace Foam

/-! ## The seed-side `ℤ/2` action — the matched base, the exact mirror of brick 29's `gaugeAct`

The seed gauge carries a single `ℤ/2` (brick 16's `SeedSign.swap`). We type it as a group action
`signAct : ZMod 2 → SeedSign → SeedSign` paralleling brick 29's base action `gaugeAct` on gauges
(`if n = 0 then a else a.reflect`), so the orbit structures line up element-for-element across the
bridge. -/

/-- **The seed-side `ℤ/2` action** — `signAct n s` swaps the sign iff `n = 1`. The exact mirror of
    brick 29's base action `gaugeAct` (`reflect` iff the coordinate is `1`); through the rigid bridge
    `signAlgebraicEquiv'` it *is* `gaugeAct` (`toAlgebraic'_signAct`), the matched base `ℤ/2` of brick
    29's SES read as an action. -/
def signAct (n : ZMod 2) (s : SeedSign) : SeedSign := if n = 0 then s else s.swap

theorem signAct_zero (s : SeedSign) : signAct 0 s = s := if_pos rfl

theorem signAct_one (s : SeedSign) : signAct 1 s = s.swap := if_neg (by decide)

/-- The seed action composes via `ZMod 2` addition (swap-or-not under XOR; `swap` is an involution).
    Mirror of brick 29's `gaugeAct_add`. -/
theorem signAct_add : ∀ (m n : ZMod 2) (s : SeedSign),
    signAct (m + n) s = signAct m (signAct n s) := by decide

/-- Each `signAct n` is an involution (`ℤ/2`) — `signAct n (signAct n s) = s`. The symmetry of the
    orbit relation rests on this (and on `n + n = 0`). -/
theorem signAct_involutive : ∀ (n : ZMod 2) (s : SeedSign), signAct n (signAct n s) = s := by decide

/-- **The seed gauge is a `ZMod 2`-set** — the single `ℤ/2` (`swap`) acts on the three signs. The
    seed-side analogue of brick 29's `kleinAddAction` (there `ℤ/2 × ℤ/2`; here the one matched `ℤ/2`). -/
instance signAddAction : AddAction (ZMod 2) SeedSign where
  vadd := signAct
  zero_vadd := signAct_zero
  add_vadd := signAct_add

/-! ## The seed `swap`-orbit relation and its `Finset` — the seed-side mirror of brick 30's `tapeOrbit` -/

/-- **Two signs are in the same `swap`-orbit** — some `ℤ/2` element carries `s` to `t`. The seed-side
    analogue of brick 30's `SameOrbit` (there over `ZMod 2 × ZMod 2`; here over the single `ZMod 2`). -/
def SeedSign.SameSwapOrbit (s t : SeedSign) : Prop := ∃ n : ZMod 2, signAct n s = t

instance (s t : SeedSign) : Decidable (s.SameSwapOrbit t) := Fintype.decidableExistsFintype

/-- Reflexive — `0` fixes every sign. -/
theorem SeedSign.SameSwapOrbit.refl (s : SeedSign) : s.SameSwapOrbit s := ⟨0, signAct_zero s⟩

/-- Symmetric — in `ZMod 2` every element is its own inverse, so the same `n` carries `t` back
    (`signAct_involutive`). -/
theorem SeedSign.SameSwapOrbit.symm {s t : SeedSign} : s.SameSwapOrbit t → t.SameSwapOrbit s := by
  rintro ⟨n, rfl⟩; exact ⟨n, signAct_involutive n s⟩

/-- Transitive — compose `ℤ/2` elements (`n + m`). -/
theorem SeedSign.SameSwapOrbit.trans {s t u : SeedSign} :
    s.SameSwapOrbit t → t.SameSwapOrbit u → s.SameSwapOrbit u := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩; exact ⟨n + m, by rw [signAct_add]⟩

/-- **The `swap`-orbit of a sign, as a `Finset`** — the image of the 2-element group under `signAct · s`.
    The seed-side mirror of brick 30's `tapeOrbit`. -/
def SeedSign.swapOrbit (s : SeedSign) : Finset SeedSign :=
  Finset.univ.image (fun n : ZMod 2 => signAct n s)

@[simp] theorem mem_swapOrbit {s t : SeedSign} : t ∈ s.swapOrbit ↔ s.SameSwapOrbit t := by
  simp [SeedSign.swapOrbit, SeedSign.SameSwapOrbit, Finset.mem_image]

/-- **The held-open recursion-top `0` is a lone `swap`-fixed point — orbit size 1.** The seed-side
    localization brick 30 could only state in prose: at the held-open gauge the seed has a single fixed
    point (brick 16's `gaugeNeutral_iff_zero`), which the FTPG side doubles to the bare fiber `×2`. -/
theorem swapOrbit_zero_card : (SeedSign.zero.swapOrbit).card = 1 := by decide

/-- The hold-open atom `+` lies in the size-2 recursion-antichain orbit `{+, −}`. -/
theorem swapOrbit_plus_card : (SeedSign.plus.swapOrbit).card = 2 := by decide

/-- The settle atom `−` lies in the same size-2 orbit `{+, −}` (it is the *same* orbit — `− = +.swap`). -/
theorem swapOrbit_minus_card : (SeedSign.minus.swapOrbit).card = 2 := by decide

/-! ## The bridge carries the seed action to the FTPG base action — the matched `ℤ/2` as intertwiner

Brick 24/25's `toAlgebraic'_swap` (`s.swap.toAlgebraic' = s.toAlgebraic'.reflect`) said the *single*
involutions conjugate. Here it is upgraded to the **actions**: the seed `ZMod 2`-action `signAct` and the
FTPG base `ZMod 2`-action `gaugeAct` are intertwined by the rigid bridge `toAlgebraic'`. This is the
matched base `ℤ/2` of brick 29's SES, now as an action-intertwiner. -/

/-- **The rigid bridge intertwines `signAct` with `gaugeAct`** — `(signAct n s).toAlgebraic' =
    gaugeAct n (s.toAlgebraic')`. The seed `ℤ/2`-action, carried across the bridge, IS the FTPG base
    `ℤ/2`-action (the matched base of brick 29's SES). Brick 25's `toAlgebraic'_swap` at the level of
    actions. -/
theorem toAlgebraic'_signAct : ∀ (n : ZMod 2) (s : SeedSign),
    (signAct n s).toAlgebraic' = gaugeAct n (s.toAlgebraic') := by decide

/-- **The seed `swap`-orbit equivalence IS the FTPG V₄-orbit equivalence across the bridge, face free** —
    `s.SameSwapOrbit t ↔ SameOrbit ⟨s.toAlgebraic', o⟩ ⟨t.toAlgebraic', o'⟩`, for *any* observer-faces
    `o`, `o'`. The matched base `ℤ/2`'s orbits on signs coincide with the V₄-orbits on the corresponding
    gauges — and the face is unconstrained (the fiber `×2` realizes either). The two-sided orbit identity
    brick 30 had only on the FTPG side. -/
theorem sameSwapOrbit_iff_sameOrbit (s t : SeedSign) (o o' : ObserverState) :
    s.SameSwapOrbit t ↔ SameOrbit ⟨s.toAlgebraic', o⟩ ⟨t.toAlgebraic', o'⟩ := by
  revert s t o o'; decide

/-! ## The orbit-doubling — the FTPG V₄-orbit is the seed `swap`-orbit, doubled by the fiber `×2`

The doubling factor is `card_observerState` (`Fintype.card ObserverState = 2`, brick 28) — the free
fiber `ℤ/2`'s orbit-size (brick 29's `fiber_free`), the `×2`. -/

/-- **The orbit-doubling (the fifth shared invariant), uniform across recursion-classes** — the FTPG
    V₄-orbit over the bridge-image gauge `s.toAlgebraic'` has *exactly twice* the cardinality of the seed
    `swap`-orbit of `s`. The factor `2` is the read/write fiber `×2` (always free, `fiber_free`), so the
    doubling is uniform: signal `4 = 2 · 2` (`s = ±`), yield `2 = 2 · 1` (`s = 0`). The base contributes
    the seed `swap`-orbit-size (matched across the bridge); the fiber contributes the constant `×2`. -/
theorem tapeOrbit_card_eq_two_mul_swapOrbit (s : SeedSign) (o : ObserverState) :
    (tapeOrbit ⟨s.toAlgebraic', o⟩).card = 2 * (s.swapOrbit).card := by
  cases s
  case plus =>
    rw [swapOrbit_plus_card]; exact tapeOrbit_signal_card_g2 o
  case minus =>
    rw [swapOrbit_minus_card]; exact tapeOrbit_signal_card o
  case zero =>
    rw [swapOrbit_zero_card]; exact tapeOrbit_yield_card o

/-- **The doubling factor named** — it is `Fintype.card ObserverState`, the read/write fiber `×2`. The
    same statement as `tapeOrbit_card_eq_two_mul_swapOrbit` with the factor identified as the fiber's
    free orbit, making *the `×2` realized as the uniform doubling factor* literal. -/
theorem tapeOrbit_card_eq_obs_mul_swapOrbit (s : SeedSign) (o : ObserverState) :
    (tapeOrbit ⟨s.toAlgebraic', o⟩).card = Fintype.card ObserverState * (s.swapOrbit).card := by
  rw [card_observerState]; exact tapeOrbit_card_eq_two_mul_swapOrbit s o

/-- **Every FTPG V₄-orbit is a doubled seed `swap`-orbit** — for *any* color `p`, `(tapeOrbit p).card =
    2 * ((p.algebraic.toSign').swapOrbit).card`, the swap-orbit of `p`'s own gauge read back to a sign.
    The color-indexed form of the doubling: the surjective statement that the FTPG orbits *are* exactly
    the seed `swap`-orbits, each doubled by the fiber `×2`. -/
theorem tapeOrbit_card_eq_two_mul_swapOrbit_of_color (p : TapePosition) :
    (tapeOrbit p).card = 2 * ((p.algebraic.toSign').swapOrbit).card := by
  obtain ⟨a, o⟩ := p
  have h := tapeOrbit_card_eq_two_mul_swapOrbit a.toSign' o
  rwa [AlgebraicPosition.toAlgebraic'_toSign'] at h

end Foam
