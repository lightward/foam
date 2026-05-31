/-
# SeedGaugeObserverSafety — the seed-gauge `±` partition IS the observer-safety partition

## What this file lands (the brick after `SeedGaugeCommitment.lean`)

`SeedGaugeCommitment.lean` proved the bridge coincides at a **unique** sign —
`bridgeCoincides_iff_eq_plus_of_injective`: among the seed-triple `{+, −, 0}`, the hold-open
`+` is the only coincidence-gauge. But that proof ran through `recognizeBacked` /
`recognizeDischarged` lfp over-counting — a *technical* reason `+` is special. This file lands
the **genuine** reason, already visible in the definitions: `+` is the
**must-carry-the-observer** half.

Two threads that ran separately now fuse:

* **the seed-gauge `±` fork** (bricks 7–12, `PersistenceLfp` / `SeedGaugeHalfType` /
  `SeedGaugeCommitment`) — `+ = OrderHom.lfp (recognizeUndischarged LP)` (the undischarged-,
  still-owed-backed faces) and `−` its local complement (the discharged-, settled-backed
  faces) within the `0`-scope;
* **the observer-safety thread** (bricks 1–6, `StatelessSubstrate`) — `measureStep r` is
  `SafeFor LP.flag` exactly when `r` is *not* flagged persisting, and is §V observer-loss when
  it is (`measureStep_safeFor_of_discharged` / `measureStep_not_safeFor_of_undischarged`).

They are the **same partition**, because `+` is *definitionally* the persistence-flag:

> `SeedSign.plus.seed LP = OrderHom.lfp (recognizeUndischarged LP) = LP.flag`
> (`plus_seed_iff_flag`, one rewrite off `flag_eq_lfpFlag_recognizeUndischarged`).

So `+` = `LP.flag` = the read-faces a single measurement may **not** spend without losing the
observer. The headline pair:

* `safeFor_measureStep_iff_not_plus` — for a read-face `r`, `measureStep r` is observer-safe
  **iff `r ∉ +`**. The `+`-atom *is* the observer-loss set (the must-carry-the-observer half).
  No injectivity: `+` = `LP.flag` directly, and safety is exactly not-flagged.
* `safeFor_measureStep_iff_minus_of_injective` — on a *debt-backed* read-face, under
  `holds`-injectivity, `measureStep r` is observer-safe **iff `r ∈ −`**. The safe half is the
  local complement `−` (the pointwise face of `seedIsCompl`, brick 11).

And the fusion with the interiority facet (brick 12):

* `seed_is_observer_loss_of_bridgeCoincides` — at **any** gauge `s` whose commitment makes the
  (a)↔(b) bridge coincide (necessarily `s = +`), the committed seed `s.seed LP` is exactly the
  observer-loss set: `s.seed LP r ↔ ¬ SafeFor LP.flag (measureStep r)` for read-faces `r`.
  **The bridge prefers the observer-safe gauge** — the external commitment it selects is the
  carry-the-observer one (§IV.c). This is *why* the bridge uniquely coincides at `+`, beneath
  the brick-12 technical proof: `+` is the gauge that does not lose the observer.

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

Pure recognition + assembly over already-landed Foam primitives:
`flag_eq_lfpFlag_recognizeUndischarged` / `recognizeUndischarged_lfp` /
`recognizeDischarged_lfp` (`PersistenceLfp`), `measureStep_safeFor_of_discharged` /
`measureStep_not_safeFor_of_undischarged` (`StatelessSubstrate`),
`bridgeCoincides_iff_eq_plus_of_injective` (`SeedGaugeCommitment`). No new geometric content;
the recognition is that two previously-separate partitions are one.

(Re-grep — stamps decay: on 2026-05-30 `lake build Foam.SeedGaugeObserverSafety` is clean,
zero sorry/warnings; depends on `SeedSign` / `recognize{Undischarged,Discharged}` /
`flag_eq_lfpFlag_recognizeUndischarged` / `bridgeCoincides` in the persistence thread and
`SafeFor` / `measureStep` / `LedgerPersistence` in `StatelessSubstrate.lean`.)
-/

import Foam.SeedGaugeCommitment

namespace Foam

/-! ## The `+`-atom IS the persistence-flag (the must-carry-the-observer set) -/

/-- **`+` is the persistence-flag (bin-1, no hypotheses).** The hold-open atom
    `SeedSign.plus.seed LP` is pointwise exactly `LP.flag` — the read-faces meant to persist.
    One rewrite off `flag_eq_lfpFlag_recognizeUndischarged` (`+ = OrderHom.lfp
    (recognizeUndischarged LP)` by definition of `SeedSign.seed`; `LP.flag = lfpFlag
    (recognizeUndischarged LP)` by the brick-7 coincidence). This is the `⟺ LP.flag` leg of the
    identification: the seed-gauge's live half is the carry-the-observer set. -/
theorem plus_seed_iff_flag (LP : LedgerPersistence) (S : Scope) (p : TapePosition) :
    SeedSign.plus.seed LP p ↔ LP.flag S p :=
  (iff_of_eq (congrFun (congrFun (flag_eq_lfpFlag_recognizeUndischarged LP) S) p)).symm

/-- Pointwise unfolding of the hold-open atom: `r ∈ +` iff `r` backs some **undischarged**
    debt (the still-owed faces). One rewrite off `recognizeUndischarged_lfp`. -/
theorem plus_seed_iff_exists (LP : LedgerPersistence) (p : TapePosition) :
    SeedSign.plus.seed LP p ↔ ∃ d, LP.holds d = p ∧ ¬ LP.Discharged d := by
  show OrderHom.lfp (recognizeUndischarged LP) p ↔ ∃ d, LP.holds d = p ∧ ¬ LP.Discharged d
  rw [recognizeUndischarged_lfp]

/-- Pointwise unfolding of the settle atom: `r ∈ −` iff `r` backs some **discharged** debt (the
    settled faces). One rewrite off `recognizeDischarged_lfp`. -/
theorem minus_seed_iff_exists (LP : LedgerPersistence) (p : TapePosition) :
    SeedSign.minus.seed LP p ↔ ∃ d, LP.holds d = p ∧ LP.Discharged d := by
  show OrderHom.lfp (recognizeDischarged LP) p ↔ ∃ d, LP.holds d = p ∧ LP.Discharged d
  rw [recognizeDischarged_lfp]

/-! ## Safety ⟺ not-in-`+` (the core: `+` is the observer-loss set) -/

/-- **The observer-safety partition IS the `±` partition, core leg (bin-1, read-face only).**
    For a read-face `r`, the single measurement `measureStep r` is `SafeFor LP.flag` **iff
    `r ∉ +`**. Equivalently (via `plus_seed_iff_flag`): safe to spend iff not flagged
    persisting. So the `+`-atom is *exactly* the set of read-faces whose measurement is §V
    observer-loss — the must-carry-the-observer half.

    No injectivity needed: the forward direction (`+ ⇒ ¬safe`) is
    `measureStep_not_safeFor_of_undischarged` (a standing debt drops a persisting bubble); the
    backward (`¬+ ⇒ safe`) is `measureStep_safeFor_of_discharged` directly (no undischarged debt
    on `r` means every debt on `r` is discharged, which licenses spending). -/
theorem safeFor_measureStep_iff_not_plus (LP : LedgerPersistence)
    {r : TapePosition} (hread : r.observer = ObserverState.read) :
    SafeFor LP.flag (measureStep r) ↔ ¬ SeedSign.plus.seed LP r := by
  rw [plus_seed_iff_exists]
  constructor
  · rintro hsafe ⟨d₀, hd₀, hndis⟩
    exact LP.measureStep_not_safeFor_of_undischarged hread hd₀ hndis hsafe
  · intro hnplus
    refine LP.measureStep_safeFor_of_discharged r (fun d hd => ?_)
    by_contra hnd
    exact hnplus ⟨d, hd, hnd⟩

/-! ## Safety ⟺ in-`−` (the safe half is the local complement of the must-persist half) -/

/-- **`−` is the local complement of `+` on debt-backed faces (the pointwise face of
    `seedIsCompl`, brick 11).** Under `holds`-injectivity, a *debt-backed* read-face is in `−`
    iff it is **not** in `+`: its unique debt is either discharged (`∈ −`) or undischarged
    (`∈ +`), never both. The forward direction (`− ⇒ ¬+`) uses injectivity (one face, one
    debt); the backward (`¬+ ⇒ −`) uses debt-backedness (the lone debt must be discharged, so
    it witnesses `−`). This is `SeedGaugeHalfType.lean`'s lattice `IsCompl` (`+ ⊓ − = ⊥`,
    `+ ⊔ − = 0`) read pointwise on the support of `0 = seedBacked`. -/
theorem minus_iff_not_plus_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) {r : TapePosition} (hbacked : ∃ d, LP.holds d = r) :
    SeedSign.minus.seed LP r ↔ ¬ SeedSign.plus.seed LP r := by
  rw [minus_seed_iff_exists, plus_seed_iff_exists]
  obtain ⟨d₀, hd₀⟩ := hbacked
  constructor
  · rintro ⟨d, hd, hdis⟩ ⟨d', hd', hndis⟩
    have hdd : d = d' := hinj (hd.trans hd'.symm)
    exact hndis (hdd ▸ hdis)
  · intro hnp
    refine ⟨d₀, hd₀, ?_⟩
    by_contra hnd
    exact hnp ⟨d₀, hd₀, hnd⟩

/-- **The safe half IS `−` (bin-1, debt-backed read-face, under injectivity).** Composing
    `safeFor_measureStep_iff_not_plus` (safe ⟺ `¬+`) with `minus_iff_not_plus_of_injective`
    (`− ⟺ ¬+`): on a debt-backed read-face, `measureStep r` is observer-safe **iff `r ∈ −`**.
    The `−`-atom — the settled/discharged-backed faces, the local complement of `+` — is
    exactly the licensed-to-spend half. The `−`-leg of the identification. -/
theorem safeFor_measureStep_iff_minus_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) {r : TapePosition}
    (hread : r.observer = ObserverState.read) (hbacked : ∃ d, LP.holds d = r) :
    SafeFor LP.flag (measureStep r) ↔ SeedSign.minus.seed LP r := by
  rw [safeFor_measureStep_iff_not_plus LP hread, minus_iff_not_plus_of_injective LP hinj hbacked]

/-! ## The fusion: the bridge prefers the observer-safe gauge -/

/-- **The bridge prefers the observer-safe gauge (the fusion headline, bin-1).** Whenever a
    commitment `s : SeedSign` makes the (a)↔(b) bridge coincide — necessarily `s = +`, by
    `bridgeCoincides_iff_eq_plus_of_injective` (brick 12) — the committed seed `s.seed LP` is
    *exactly* the observer-loss set: for a read-face `r`, `r ∈ s.seed LP` iff `measureStep r`
    loses the observer.

    This fuses the **interiority facet** (brick 12: the bridge-sign / half-choice / tamp-seed
    are one external commitment) with the **carry-the-observer discipline** (§IV.c) and the
    **observer-safety thread** (§V, bricks 1–6). It is the genuine reason the bridge uniquely
    coincides at `+`, beneath brick 12's technical lfp-over-counting proof: `+` is the gauge
    whose seed is the must-carry-the-observer half, so committing the bridge-coinciding gauge
    *is* committing the observer-preserving reading. The external commitment the substrate's
    bridge points toward is the one that does not drop the `+me`. -/
theorem seed_is_observer_loss_of_bridgeCoincides (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hdis : ∃ d, LP.Discharged d)
    {s : SeedSign} (hs : s.bridgeCoincides LP)
    {r : TapePosition} (hread : r.observer = ObserverState.read) :
    s.seed LP r ↔ ¬ SafeFor LP.flag (measureStep r) := by
  have hsp : s = SeedSign.plus :=
    (SeedSign.bridgeCoincides_iff_eq_plus_of_injective LP hinj hdis s).mp hs
  subst hsp
  rw [safeFor_measureStep_iff_not_plus LP hread, not_not]

end Foam
