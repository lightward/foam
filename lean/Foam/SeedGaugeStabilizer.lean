/-
# SeedGaugeStabilizer — the Orbit-Stabilizer dual; the held-open's stabilizer IS the matched base `ℤ/2`

## What this file lands (the brick after `SeedGaugeSwapOrbitDoubling.lean`)

Brick 31 (`SeedGaugeSwapOrbitDoubling.lean`) exhibited the **uniform doubling**
`(tapeOrbit ⟨s.toAlgebraic', o⟩).card = 2 * (s.swapOrbit).card` — the FTPG V₄-orbit is the seed
`swap`-orbit, doubled by the free fiber `×2` (signal `4 = 2·2`, yield `2 = 2·1`). That came from
`|V₄·p| = |base-orbit| · |fiber-orbit|` with the **fiber free** (its orbit-factor always `2`). Its
flagged remainder is the **dual** count.

**Orbit-Stabilizer**: `|orbit| · |stab| = |group|`. Where the orbit *shrinks*, the stabilizer *grows*.
Brick 31 watched the orbit; this file watches the stabilizer — the dual face of the same `|group|`. The
recognition: at the held-open `0 ↔ g3` (bricks 24/26, the shared recursion-top), the orbit is *small*
(seed `1`, FTPG `2`), so the stabilizer is *big* — and it is **the matched base `ℤ/2`** on both sides,
while the **surplus fiber `×2`** never stabilizes anything. The matched/surplus SES (brick 29) localized
at the fixed point.

## The two stabilizers, and the dual arithmetic

We type the stabilizers as `decide`-friendly `Finset`s (the family idiom — brick 30's `tapeOrbit`, brick
31's `swapOrbit`), the seed `signStab s := {n | signAct n s = s}` (a subset of the single matched `ℤ/2`)
and the FTPG `tapeStab p := {g | kleinVAdd g p = p}` (a subset of the V₄). The cardinalities are the
Orbit-Stabilizer mirror of brick 31's orbit cards:

| locus            | seed orbit | seed stab | FTPG orbit | FTPG stab |
|------------------|:----------:|:---------:|:----------:|:---------:|
| held-open `0/g3` |     1      |   **2**   |     2      |   **2**   |
| signal `±/g1,g2` |     2      |     1     |     4      |     1     |

`|orbit| · |stab|` is `|group|` throughout — seed `1·2 = 2·1 = 2 = |ℤ/2|` (`seed_orbit_stabilizer`),
FTPG `2·2 = 4·1 = 4 = |ℤ/2 × ℤ/2|` (`tape_orbit_stabilizer`). The held-open's stabilizer is *maximal*
exactly where its orbit is *minimal*: the Orbit-Stabilizer dual of brick 31's doubling.

## The matched base / surplus fiber split, localized at the fixed point

The whole content is **where the stabilizing happens**, read against brick 29's SES
`1 → ⟨complement⟩(×2, fiber) → V₄ → ⟨reflectColor⟩(base = swap's partner) → 1`:

* **The surplus fiber `×2` never stabilizes.** An element `(m, 1)` flips the observer-face
  (`faceAct 1 o = o.flip ≠ o`), so it moves *every* color: `fiber_not_mem_tapeStab` (the surplus
  generator `(0,1) = complement` is in no stabilizer, brick 29's `fiber_free`), and more,
  `tapeStab_subset_base` — *every* stabilizer is contained in the base subgroup `{(0,0), (1,0)}`.
  Stabilizing **requires** a zero fiber-coordinate; the surplus `×2` contributes nothing to any
  stabilizer, anywhere. (Dual to brick 31, where the surplus fiber contributed the *entire* free orbit
  doubling-factor: fiber → all-orbit, never-stab.)

* **The matched base `ℤ/2` is where stabilizing lives, maximal at the held-open.** At `g3` the base
  *fully* stabilizes — `gaugeAct m g3 = g3` for both `m` (brick 24's `reflect` fixes `g3`), so
  `tapeStab ⟨g3, o⟩ = {(0,0), (1,0)}` is the **whole base subgroup** `⟨reflectColor⟩`
  (`tapeStab_yield_eq_base`). At a signal the base acts freely (`gaugeAct 1 g1 = g2 ≠ g1`), so
  `tapeStab ⟨g1/g2, o⟩ = {(0,0)}` is trivial (`tapeStab_signal`/`_g2`). The base contributes to the
  stabilizer *or* the orbit by gauge — held-open → stab, signal → orbit — exactly mirroring the seed
  `ℤ/2` (`signStab 0 = univ` whole group at the held-open, `signStab ± = {0}` trivial at signals).

* **The bridge intertwines the two matched parts.** `mem_tapeStab_base_iff_signStab` — the base-part of
  the FTPG stabilizer **is** the seed stabilizer carried across the rigid bridge:
  `(m, 0) ∈ tapeStab ⟨s.toAlgebraic', o⟩ ↔ m ∈ signStab s`. The seed-side analogue of brick 31's
  `sameSwapOrbit_iff_sameOrbit`, at the stabilizer level: the matched base `ℤ/2`'s stabilizing on signs
  coincides with its stabilizing on the corresponding gauges, face free.

So the FTPG stabilizer factors as **(matched base part = seed stabilizer across the bridge) × (surplus
fiber part = trivial)** — the SES split read *inside* every stabilizer. This is the complete
Orbit-Stabilizer picture, dual to brick 31: the surplus fiber `×2` is **all-orbit, never-stab**; the
matched base is **orbit-or-stab by gauge**, mirroring the seed.

## The sixth shared invariant

A **sixth** structural fact shared between the two threads, after orbit-shape (b24), recursion-grading
(b26), involution-count/SES (b29), orbit-grading (b30), and orbit-doubling (b31): the held-open fixed
point `0 ↔ g3`'s stabilizer is the **full matched base `ℤ/2`** on both sides (seed: all of `⟨swap⟩`;
FTPG: the base subgroup `⟨reflectColor⟩`), and the surplus fiber `×2` never stabilizes. It is the
**Orbit-Stabilizer dual** of brick 31's doubling, localizing brick 29's matched/surplus SES at the shared
fixed point.

## NOT the coincidence-trap

The stabilizers are *subgroups of the two acting groups* (`ZMod 2`, `ZMod 2 × ZMod 2`). Identifying the
held-open's stabilizer-subgroup with the matched base `⟨swap⟩` / `⟨reflectColor⟩` *via brick 29's SES*
(and the bridge intertwiner `mem_tapeStab_base_iff_signStab`) is legitimate — a relation between the two
**actions'** stabilizer-subgroups, mediated by the *substantive* point-map `toAlgebraic'`. It is **not**
a (type-confused) `Bool×Bool ≃ Bool×Bool` bijection of commitment-*points* (signs/gauges) to
symmetry-*elements* (`swap`/`reflect`/`flip`). Everything here is subgroups, orbits, and a point-map.

## Grade

* **bin-1 (Bin-1-Mathlib-or-Foam)** for everything typed: the stabilizer `Finset`s `signStab`/`tapeStab`
  and their membership simp-lemmas, the cardinalities `1`/`2` (`decide`), the base-subgroup equality at
  `g3` (`tapeStab_yield_eq_base`, `decide`), the trivial stabilizers at signals (`decide`), the
  surplus-fiber-never-stabilizes facts (`fiber_not_mem_tapeStab`/`tapeStab_subset_base`, `decide`), the
  bridge intertwiner at the stabilizer level (`mem_tapeStab_base_iff_signStab`, `decide` — brick 31's
  `toAlgebraic'_signAct` read at the stabilizer), and the Orbit-Stabilizer relations
  (`seed_orbit_stabilizer`/`tape_orbit_stabilizer`, assembling brick 30/31's orbit cards with these stab
  cards). No new geometric content; the recognition is that the *already-typed* actions' stabilizers sit
  inside the matched base, with the surplus fiber contributing nothing — the Orbit-Stabilizer dual of the
  doubling.

* **bin-2 / interpretive** for the **sixth-shared-invariant reading** (the held-open's stabilizer IS the
  matched base, the dual of b31's doubling, the SES localized at the fixed point — held
  merge-don't-fork: the stabilizer Finsets + cards + OS relation are bin-1; the "dual / matched-base /
  sixth-invariant toward two-`ℤ/2`s-one-group" reading is the deposit). The deeper *substance* — the two
  `ℤ/2`s as **one group**, `+1 ≅ ×2` as one move at the rank-3 self-dual fixed point `g3 ↔ 0` — stays
  the **named horizon** (the bireflective coincidence, §VI), NOT this brick.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeStabilizer` is clean, zero
sorry/warnings. Imports `Foam.SeedGaugeSwapOrbitDoubling` (brick 31 — transitively `signAct` /
`SeedSign.swapOrbit` / `swapOrbit_zero_card` / `swapOrbit_plus_card` / `swapOrbit_minus_card` /
`toAlgebraic'_signAct` from brick 31; `tapeOrbit` / `tapeOrbit_signal_card` / `tapeOrbit_signal_card_g2` /
`tapeOrbit_yield_card` from brick 30; `kleinVAdd` / `fiber_free` / `bothColor_ne` / `klein_card` from
brick 29; `SeedSign.toAlgebraic'` from brick 24; `Fintype`/`DecidableEq` for `SeedSign` / `ObserverState`
/ `TapePosition` / `ZMod 2 × ZMod 2`). New names: `signStab` / `mem_signStab` / `signStab_zero_eq_univ` /
`signStab_plus` / `signStab_minus` / `signStab_zero_card` / `signStab_plus_card` / `signStab_minus_card`;
`tapeStab` / `mem_tapeStab` / `fiber_not_mem_tapeStab` / `tapeStab_subset_base` / `tapeStab_yield_eq_base`
/ `tapeStab_signal` / `tapeStab_signal_g2` / `tapeStab_yield_card` / `tapeStab_signal_card` /
`tapeStab_signal_card_g2`; `mem_tapeStab_base_iff_signStab`; `seed_orbit_stabilizer` /
`tape_orbit_stabilizer`.)
-/

import Foam.SeedGaugeSwapOrbitDoubling

namespace Foam

/-! ## The seed stabilizer — a subset of the single matched `ℤ/2`

The seed gauge carries one `ℤ/2` (`signAct`, brick 31). Its point-stabilizers are subsets of that group;
the held-open `0` is fixed by *all* of it (`swap`-fixed, brick 16), the signs `±` by *only* the identity. -/

/-- **The seed stabilizer** — the `ℤ/2` elements fixing the sign `s` under `signAct`. A subset of the
    single matched `ℤ/2`; the seed-side analogue of `tapeStab`. -/
def signStab (s : SeedSign) : Finset (ZMod 2) :=
  Finset.univ.filter (fun n => signAct n s = s)

@[simp] theorem mem_signStab {s : SeedSign} {n : ZMod 2} :
    n ∈ signStab s ↔ signAct n s = s := by simp [signStab]

/-- **The held-open `0`'s stabilizer is the WHOLE matched `ℤ/2`** — `0` is `swap`-fixed (brick 16's
    `gaugeNeutral_iff_zero`), so every group element stabilizes it. The seed face of "the held-open's
    stabilizer is the full matched base": on the seed side the matched `ℤ/2` *is* the whole group. -/
theorem signStab_zero_eq_univ : signStab SeedSign.zero = Finset.univ := by decide

/-- The hold-open atom `+`'s stabilizer is trivial — only the identity fixes it (`swap` exchanges `±`). -/
theorem signStab_plus : signStab SeedSign.plus = {0} := by decide

/-- The settle atom `−`'s stabilizer is trivial — only the identity fixes it. -/
theorem signStab_minus : signStab SeedSign.minus = {0} := by decide

theorem signStab_zero_card : (signStab SeedSign.zero).card = 2 := by decide
theorem signStab_plus_card : (signStab SeedSign.plus).card = 1 := by decide
theorem signStab_minus_card : (signStab SeedSign.minus).card = 1 := by decide

/-! ## The FTPG stabilizer — contained in the matched base subgroup; the surplus fiber never stabilizes -/

/-- **The FTPG stabilizer** — the V₄ elements fixing the color `p` under `kleinVAdd`. We show it is always
    contained in the base subgroup `{(0,0), (1,0)} = ⟨reflectColor⟩` (the surplus fiber `×2` never
    contributes), maximal (the *whole* base subgroup) exactly at the held-open `g3`. -/
def tapeStab (p : TapePosition) : Finset (ZMod 2 × ZMod 2) :=
  Finset.univ.filter (fun g => kleinVAdd g p = p)

@[simp] theorem mem_tapeStab {p : TapePosition} {g : ZMod 2 × ZMod 2} :
    g ∈ tapeStab p ↔ kleinVAdd g p = p := by simp [tapeStab]

/-- **The surplus fiber `×2` never stabilizes** — the fiber generator `(0,1) = complement` (brick 29's
    `fiber_free`) is in no color's stabilizer. The dual of brick 31, where the *same* free fiber
    contributed the entire orbit-doubling factor: fiber → all-orbit, never-stab. -/
theorem fiber_not_mem_tapeStab (p : TapePosition) : ((0, 1) : ZMod 2 × ZMod 2) ∉ tapeStab p := by
  revert p; decide

/-- **Every stabilizer is contained in the matched base subgroup** — `tapeStab p ⊆ {(0,0), (1,0)}` for
    every color. Stabilizing *requires* a zero fiber-coordinate (any `(m, 1)` flips the observer-face),
    so the surplus fiber `×2` contributes nothing to any stabilizer, anywhere. The base
    `⟨reflectColor⟩ = {(0,0), (1,0)}` is the only stabilizing-capable part of the V₄. -/
theorem tapeStab_subset_base (p : TapePosition) :
    tapeStab p ⊆ ({(0, 0), (1, 0)} : Finset (ZMod 2 × ZMod 2)) := by
  revert p; decide

/-- **The held-open `g3`'s stabilizer is the FULL base subgroup** — `tapeStab ⟨g3, o⟩ = {(0,0), (1,0)} =
    ⟨reflectColor⟩`. The base `reflect` fixes `g3` (brick 24) for *both* coordinates, so the whole base
    `ℤ/2` stabilizes; only the surplus fiber moves the color (its read/write bubble). The FTPG face of
    "the held-open's stabilizer is the matched base." -/
theorem tapeStab_yield_eq_base (o : ObserverState) :
    tapeStab ⟨AlgebraicPosition.g3, o⟩ = ({(0, 0), (1, 0)} : Finset (ZMod 2 × ZMod 2)) := by
  cases o <;> decide

/-- The signal-gauge `g1`'s stabilizer is trivial — the V₄ acts freely on the signal block (`reflect`
    swaps `g1 ↔ g2`, the fiber swaps the faces). -/
theorem tapeStab_signal (o : ObserverState) :
    tapeStab ⟨AlgebraicPosition.g1, o⟩ = ({0} : Finset (ZMod 2 × ZMod 2)) := by cases o <;> decide

/-- The other signal-gauge `g2`'s stabilizer is likewise trivial. -/
theorem tapeStab_signal_g2 (o : ObserverState) :
    tapeStab ⟨AlgebraicPosition.g2, o⟩ = ({0} : Finset (ZMod 2 × ZMod 2)) := by cases o <;> decide

/-- **The held-open `g3`'s stabilizer has size 2** — the base subgroup. Maximal exactly where the orbit
    is minimal (brick 30's `tapeOrbit_yield_card = 2`): the Orbit-Stabilizer dual. -/
theorem tapeStab_yield_card (o : ObserverState) :
    (tapeStab ⟨AlgebraicPosition.g3, o⟩).card = 2 := by cases o <;> decide

theorem tapeStab_signal_card (o : ObserverState) :
    (tapeStab ⟨AlgebraicPosition.g1, o⟩).card = 1 := by cases o <;> decide
theorem tapeStab_signal_card_g2 (o : ObserverState) :
    (tapeStab ⟨AlgebraicPosition.g2, o⟩).card = 1 := by cases o <;> decide

/-! ## The matched-base intertwiner — the base-part of the FTPG stabilizer IS the seed stabilizer

Brick 31's `toAlgebraic'_signAct` intertwined the seed `ℤ/2`-action `signAct` with the FTPG base
`ℤ/2`-action `gaugeAct` across the rigid bridge. Here it is read at the stabilizer: the base-coordinate
part of the FTPG stabilizer coincides with the seed stabilizer, face free. -/

/-- **The base-part of the FTPG stabilizer is the seed stabilizer across the bridge** —
    `(m, 0) ∈ tapeStab ⟨s.toAlgebraic', o⟩ ↔ m ∈ signStab s`, for any observer-face `o`. The seed-side
    analogue of brick 31's `sameSwapOrbit_iff_sameOrbit`, at the stabilizer level: the matched base
    `ℤ/2`'s stabilizing on signs is its stabilizing on the corresponding gauges (the fiber-coordinate is
    `0` — no surplus — and the face is free). So the FTPG stabilizer factors as (matched base part = seed
    stabilizer) × (surplus fiber part = trivial). -/
theorem mem_tapeStab_base_iff_signStab (s : SeedSign) (o : ObserverState) (m : ZMod 2) :
    ((m, 0) : ZMod 2 × ZMod 2) ∈ tapeStab ⟨s.toAlgebraic', o⟩ ↔ m ∈ signStab s := by
  revert s o m; decide

/-! ## Orbit-Stabilizer — the dual of brick 31's doubling

`|orbit| · |stab| = |group|`, both sides. Where brick 31 watched the orbit (doubled by the free fiber),
this is the dual face: the held-open's stabilizer is *maximal* (the matched base) exactly where its orbit
is *minimal*. -/

/-- **Orbit-Stabilizer, seed side** — `|swapOrbit s| · |signStab s| = 2 = |ℤ/2|`. Held-open `0`: `1 · 2`
    (orbit minimal, stabilizer the whole group); signs `±`: `2 · 1` (orbit maximal, stabilizer trivial).
    Assembles brick 31's `swapOrbit_*_card` with the seed stab cards. -/
theorem seed_orbit_stabilizer (s : SeedSign) :
    (s.swapOrbit).card * (signStab s).card = 2 := by cases s <;> decide

/-- **Orbit-Stabilizer, FTPG side** — `|tapeOrbit p| · |tapeStab p| = 4 = |ℤ/2 × ℤ/2|` (brick 29's
    `klein_card`). Held-open `g3`: `2 · 2` (orbit the fiber `×2`, stabilizer the base subgroup); signals
    `g1/g2`: `4 · 1` (orbit the free signal-block, stabilizer trivial). The Orbit-Stabilizer dual of brick
    31's doubling — orbit-small ⟺ stabilizer-big, the surplus fiber's `2` going *entirely* into the orbit
    (b31) and *nothing* into the stabilizer (this file). Assembles brick 30's `tapeOrbit_*_card` with the
    FTPG stab cards. -/
theorem tape_orbit_stabilizer (p : TapePosition) :
    (tapeOrbit p).card * (tapeStab p).card = 4 := by
  obtain ⟨a, o⟩ := p; cases a <;> cases o <;> decide

end Foam
