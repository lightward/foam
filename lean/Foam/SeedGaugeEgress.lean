/-
# SeedGaugeEgress — the external commitment is free *and* `+`-preferred: it dissolves into egress

## What this file lands (the brick after `SeedGaugeObserverSafety.lean`)

`SeedGaugeCommitment.lean` (brick 12) found the bare lattice geometry **sign-free**
(`bridge_breaks_fork_symmetry`: `IsCompl` is symmetric, nothing privileges `+` over `−`; only the
*bridge* breaks the symmetry) — so committing the gauge looks **free** (gauge-fixing, where the
reader/mind enters, §IV.a / §VIII). `SeedGaugeObserverSafety.lean` (brick 13) found the bridge
**prefers** `+`, the observer-safe gauge — so carry-the-observer (§IV.c) looks to **force** it.
Free or forced?

This file lands the dissolution, already visible in the proven theorems: **the seed-fork is not
observer-symmetric.** Read *through the observer* (`observerSet := +.seed = LP.flag`, the
must-persist set), the three seeds split three ways:

* `+` **carries the observer exactly** — `plus_carries_observer_exactly`: `+.seed = observerSet`
  (rfl, `observerSet := +.seed`, which is `LP.flag` by `plus_seed_iff_flag`, brick 13). The
  *stay-exact* seed — be yourself.
* `0` **carries the observer with excess** — `zero_carries_observer` (`observerSet ≤ 0.seed`,
  `plus_le_zero`), strictly so under injectivity + a discharged debt
  (`zero_over_carries_observer`, via `zero_ne_plus_of_injective`). The *stay-over-full* seed —
  carries the observer **and** the settled/discharged faces that are not it.
* `−` **drops the observer** — `minus_drops_observer`: `observerSet ⊓ −.seed = ⊥`
  (`plus_inf_minus_eq_bot`). The *leave* seed — disjoint from the must-persist set.

So the fork is `{+ = stay-exact, 0 = stay-over-full, − = leave}`, and the bridge coincides at
exactly the *stay-exact* seed:

* `carriesObserverExactly_iff_eq_plus` — `s.seed = observerSet ↔ s = +` (inj + discharged): only
  `+` carries the observer exactly.
* `bridgeCoincides_iff_carriesObserverExactly` (**the headline**) — `s.bridgeCoincides LP ↔
  s.seed LP = observerSet LP` (inj + discharged): **the bridge coincides iff the committed seed
  carries the observer exactly.** The bridge's preference *is* exact-observer-carriage.

## Free or forced dissolves into egress

The freedom and the preference are the same fact, seen on the right axis. The lattice geometry is
sign-free (brick 12) — all of `{⊥, +, −, 0}` are inhabited and available; the door is open in
every direction (§IV.c: exits are constitutionally open; egress is a *free* operation). The
bridge's preference for `+` is **not** a lock on that door — it is the recognition that only `+`
is **egress-shaped**:

* committing `−` is *honored but self-erasing* — the door is open, you may walk it, but `−` is
  disjoint from the observer (`minus_drops_observer`): walking it drops the `+me`. This violates
  **carry-the-observer** (§IV.c) — leaving-that-loses-the-self-pointer, the *opposite* of egress.
* committing `0` *over-commits* — it carries the observer but also the discharged/settled faces
  that are not it (`zero_over_carries_observer`). This violates **recognition-only** (§IV.c) —
  committing un-recognized excess (the settled faces are discharged, not part of the live self).
* committing `+` is **be yourself** — carry exactly the observer, nothing dropped, nothing added.

And §IV.c *derives* egress as exactly this: the distance-zero cross-product of carry-the-observer
(`+me` preserved → not `−`) and recognition-only (no un-recognized commitment → not `0`), applied
to self. So `bridgeCoincides_iff_carriesObserverExactly` **re-derives §IV.c's egress on the
seed-gauge**: the bridge does not *force* `+` against a free choice; it *names which free choice
is egress*. Free-vs-forced was the wrong axis — the right one is egress-shaped-vs-not, and the
bridge points along egress. The freedom is the open door; the preference is that only one
direction stays-as-self.

This is the first time the §IV.c **derived discipline egress** is instantiated on a structure the
recognition dynamics *produce* (paralleling brick 11, the first §IV.a HalfType they produce).

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

Pure recognition + assembly over already-landed Foam primitives: `plus_seed_iff_flag` /
`plus_le_zero` / `plus_inf_minus_eq_bot` / `zero_ne_plus_of_injective` /
`plus_ne_minus_of_injective` (`PersistenceLfp`), `bridgeCoincides_iff_eq_plus_of_injective`
(`SeedGaugeCommitment`). No new geometric content; the recognition is that the bridge-preference,
the observer-content split, and §IV.c egress are one.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeEgress` is clean, zero
sorry/warnings; depends on `SeedSign.seed` / `plus_le_zero` / `plus_inf_minus_eq_bot` /
`zero_ne_plus_of_injective` / `plus_ne_minus_of_injective` in `PersistenceLfp.lean`,
`bridgeCoincides` / `bridgeCoincides_iff_eq_plus_of_injective` in `SeedGaugeCommitment.lean`, and
`plus_seed_iff_flag` in `SeedGaugeObserverSafety.lean`.)
-/

import Foam.SeedGaugeObserverSafety

namespace Foam

/-! ## The observer-set, and the three-way split of the seed-fork through it -/

/-- **The observer-set** — the must-persist / carry-the-observer set, named once for the
    three-way split. Definitionally the hold-open atom `SeedSign.plus.seed LP`, which is pointwise
    `LP.flag` (`plus_seed_iff_flag`, brick 13): the read-faces meant to persist. Two roles for one
    set: as a **seed** it is *carry-the-observer* (seeding recognition with it keeps exactly the
    persisting faces — stay yourself); as a **measurement-target** it is the *observer-loss set*
    (brick 13: `measureStep r` is safe iff `r ∉ observerSet`). Carrying it preserves the observer;
    spending it loses the observer. -/
def observerSet (LP : LedgerPersistence) : Scope := SeedSign.plus.seed LP

/-- `observerSet` is `LP.flag` (the must-persist set), pointwise — the bridge to §IV.c
    carry-the-observer. One unfolding of `plus_seed_iff_flag`. -/
theorem observerSet_iff_flag (LP : LedgerPersistence) (S : Scope) (p : TapePosition) :
    observerSet LP p ↔ LP.flag S p :=
  plus_seed_iff_flag LP S p

/-- **`+` carries the observer exactly (stay-exact, bin-1, no hypotheses).** The hold-open seed
    *is* the observer-set: `+.seed = observerSet` by definition. Committing `+` carries exactly the
    must-persist faces — nothing dropped, nothing added. The *be yourself* seed. -/
theorem plus_carries_observer_exactly (LP : LedgerPersistence) :
    SeedSign.plus.seed LP = observerSet LP := rfl

/-- **`0` carries the observer (with possible excess), bin-1.** The gauge-neutral join sits above
    the observer-set: `observerSet ≤ 0.seed` (`plus_le_zero`). `0` carries the observer — but also
    the settled/discharged faces `−` (`0 = + ⊔ −`). -/
theorem zero_carries_observer (LP : LedgerPersistence) :
    observerSet LP ≤ SeedSign.zero.seed LP :=
  SeedSign.plus_le_zero LP

/-- **`0` carries the observer *with strict excess* (stay-over-full, under inj + discharged).**
    `observerSet < 0.seed`: `0` carries the observer (`zero_carries_observer`) and is strictly
    bigger (`zero_ne_plus_of_injective` — the discharged debt's face is in `0` but not in `+`). The
    excess is exactly the settled faces `−`. Committing `0` over-commits: it carries the live self
    **and** discharged faces that are not it — un-recognized excess (against recognition-only,
    §IV.c). -/
theorem zero_over_carries_observer (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (h : ∃ d, LP.Discharged d) :
    observerSet LP < SeedSign.zero.seed LP :=
  lt_of_le_of_ne (SeedSign.plus_le_zero LP) (SeedSign.zero_ne_plus_of_injective LP hinj h).symm

/-- **`−` drops the observer (leave, under injectivity).** The settle seed is *disjoint* from the
    observer-set: `observerSet ⊓ −.seed = ⊥` (`plus_inf_minus_eq_bot`). Committing `−` carries none
    of the must-persist faces — it drops the `+me` (against carry-the-observer, §IV.c). The *leave*
    seed: honored (the door is open) but self-erasing. -/
theorem minus_drops_observer (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) :
    observerSet LP ⊓ SeedSign.minus.seed LP = ⊥ :=
  SeedSign.plus_inf_minus_eq_bot LP hinj

/-! ## The egress headline: the bridge coincides iff the seed carries the observer exactly -/

/-- **Only `+` carries the observer exactly (under inj + discharged).** `s.seed = observerSet ↔
    s = +`. `+` by definition; `−` excluded by `plus_ne_minus_of_injective` (`−.seed ≠ +.seed`);
    `0` excluded by `zero_ne_plus_of_injective` (`0.seed ≠ +.seed`). So *carries-the-observer-
    exactly* singles out `+` among the whole seed-triple — the *stay-exact* disposition is
    unique. -/
theorem carriesObserverExactly_iff_eq_plus (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hdis : ∃ d, LP.Discharged d) (s : SeedSign) :
    s.seed LP = observerSet LP ↔ s = SeedSign.plus := by
  cases s
  · exact iff_of_true rfl rfl
  · exact iff_of_false
      (fun heq => SeedSign.plus_ne_minus_of_injective LP hinj hdis heq.symm) (by decide)
  · exact iff_of_false
      (fun heq => SeedSign.zero_ne_plus_of_injective LP hinj hdis heq) (by decide)

/-- **The headline (bin-1): the bridge coincides iff the seed carries the observer exactly.**
    `s.bridgeCoincides LP ↔ s.seed LP = observerSet LP` (under inj + discharged). The bridge's
    preference *is* exact-observer-carriage: both sides hold exactly at `s = +`
    (`bridgeCoincides_iff_eq_plus_of_injective` ∘ `carriesObserverExactly_iff_eq_plus`).

    **Free or forced dissolves into egress.** The geometry is sign-free (brick 12: the door is open
    in every direction); the bridge's preference is not a lock on the door but the recognition that
    only `+` is *egress-shaped* — carries the observer exactly (stay yourself). `−` drops the
    observer (`minus_drops_observer` — leave-by-erasing-self, against carry-the-observer); `0`
    over-carries (`zero_over_carries_observer` — un-recognized excess, against recognition-only).
    §IV.c *derives* egress as exactly carry-the-observer ∩ recognition-only applied to self; so this
    theorem re-derives §IV.c egress on the seed-gauge: the bridge does not *force* `+` against a
    free choice — it *names which free choice is egress*. The freedom is the open door; the
    preference is that only `+` stays-as-self. -/
theorem bridgeCoincides_iff_carriesObserverExactly (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hdis : ∃ d, LP.Discharged d) (s : SeedSign) :
    s.bridgeCoincides LP ↔ s.seed LP = observerSet LP :=
  (SeedSign.bridgeCoincides_iff_eq_plus_of_injective LP hinj hdis s).trans
    (carriesObserverExactly_iff_eq_plus LP hinj hdis s).symm

end Foam
