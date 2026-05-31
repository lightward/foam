/-
# SeedGaugeEmptyCommitment — the empty seed `⊥` is the un-tamped ground: the functor's input

## What this file lands (the brick after `SeedGaugeBiasDelegation.lean`)

The seed-lattice is the 4-element Boolean algebra `{⊥, +, −, 0}` (`SeedGaugeHalfType.lean`,
brick 11) — and that BA is exactly the **powerset of the two signs `{+, −}`**:

| BA element | sign-content | disposition | landed |
|---|---|---|---|
| `0 = + ⊔ −` | `{+, −}` — **both** | §IV.d **bias-delegation** (hold the full spectrum) | brick 16 |
| `+` | `{+}` — only `+` | §IV.c **carry-the-observer / egress** (be yourself) | brick 14 |
| `−` | `{−}` — only `−` | §IV.c **the honored exit** (leave, drop the `+me`) | brick 14 |
| `⊥ = + ⊓ −` | `∅` — **neither** | *the empty commitment* — **the un-tamped ground** | **this file** |

Bricks 14–16 mapped the three *nonzero* seeds `{+, −, 0}` (the dispositions the single external
commitment can commit *to*). This file maps the **bottom** `⊥` — the one BA element left without a
disposition-reading. The recognition: **`⊥` is not a fourth disposition. It is the *absence* of the
external commitment** — the no-tamp, the un-committed ground the three dispositions rise from.

### `⊥` carries neither sign — completing the powerset characterization

`HoldsFullSpectrum` (brick 16) says `0` carries *both* signs; this file's `HoldsNeitherSign` is its
**dual**: `⊥` carries *neither* (`bot_holdsNeitherSign`, under unresolved tension `BothDebtKinds` —
no injectivity needed). The two facts that drive it are the contrapositive-companions of brick 15's
collapse-lemmas: a live debt makes `+.seed ≠ ⊥` (`plus_seed_ne_bot_of_undischarged`), a settled debt
makes `−.seed ≠ ⊥` (`minus_seed_ne_bot_of_discharged`) — each read-face that backs a debt is a witness
that the corresponding fork-seed is non-empty, so under both-debt-kinds neither fork-seed is `⊥`, and
`⊥` (carrying `± ≤ ⊥ ⟺ ±.seed = ⊥`, `le_bot_iff`) carries neither. With the `±` reflexive-carry and
brick 16's `not_{minus,plus}_le_{plus,minus}_of_both`, all four BA elements are now characterized by
which signs they carry: `⊥` neither / `±` one each / `0` both = the four subsets of `{+, −}`. **The
"sign-content" map IS the Boolean-algebra isomorphism `{⊥, +, −, 0} ≃ 𝒫({+, −})`.**

The two lattice anchors that pin the `2²`, now **dual**: `0 = + ⊔ −` (top = join of the atoms,
`seed_zero_eq_join`, brick 10) and `⊥ = + ⊓ −` (bottom = meet of the atoms,
`bot_eq_plus_inf_minus`, from `plus_inf_minus_eq_bot`, brick 11). So `⊥` has a second reading beside
"carries neither": it is the **overlap of the two one-sign commitments** — what `+` and `−` agree on
is nothing, so committing to nothing is exactly their meet.

### `⊥` is the un-tamped ground — the single-external-commitment functor's *input*

`⊥ = P₀ = ∅` is README §III's *empty initial substrate*. The tamp (§IV.a/§VIII — the single external
commitment, gauge-fixing, where mind enters) is the choice of a **nonempty, sign-bearing** seed
`P₀ ∈ {+, −, 0}`; choosing `⊥` is the **no-tamp**. So the full lattice `{⊥, +, −, 0}` is the
single-external-commitment functor's **source + target in one object**: `⊥` the identity/input (the
gauge-free, uncertainty-free §VIII "geometry-only" pre-commitment state — committing introduces
uncertainty via §VII von-Neumann→Shannon, and `⊥` is *before* it), and `{+, −, 0}` the three gauges
the one tamp can commit to. This is the no-commitment **fixed point** brick 9 already typed:
`applyRules_lfp_bot` (`RecognitionApplier.lean`) — the gated `F` run from `⊥` stays `⊥`, recognition
fires nothing from nothing. The empty commitment is fixed under recognition exactly because there is
no observer-commitment in it to propagate.

This completes the `{⊥, +, −, 0}` ↔ commitment-structure: a concrete, bounded facet of the keystone
single-external-commitment functor — its source (`⊥`), its three possible targets (`{+, −, 0}`), and
the sign-content iso to `𝒫({+, −})` that organizes them.

### `{⊥, 0}` are the two gauge-neutral *values* — refining brick 16

Brick 16's `gaugeNeutral_iff_zero` says `0` is the unique gauge-neutral *sign* — but that lives at the
`SeedSign` level, where there are only three elements `{+, −, 0}` and `⊥` is not a sign. At the
`Scope`/BA level there are **four** elements, and the gauge-swap `+ ↔ −` (acting on sign-content as
`(a, b) ↦ (b, a)`) fixes the two swap-symmetric subsets `∅` and `{+, −}` — so the gauge-neutral
*values* are **`{⊥, 0}`**, not just `{0}`. `GaugeNeutralValue S := (+ ≤ S ↔ − ≤ S)` (S's sign-content
is unchanged under exchanging the signs); `gaugeNeutralValue_bot` / `gaugeNeutralValue_zero` /
`not_gaugeNeutralValue_plus` / `not_gaugeNeutralValue_minus` prove exactly `{⊥, 0}` neutral and `{±}`
gauge-broken among the BA's four elements. **`⊥` is neutral-by-emptiness (commits to nothing), `0` is
neutral-by-fullness (commits to both, collapses nothing — bias-delegation); `±` are the gauge-broken
values, one sign each — the gauge-fixing landed.** The bridge (`bridge_breaks_fork_symmetry`, brick
12) breaks the symmetry by selecting `+` from the `±` pair; it cannot move either neutral pole. So the
two §VII von-Neumann→Shannon poles are: `⊥` (before the commitment — geometry-only, no sign) and `0`
(declining the commitment — both signs held, bias-delegated); the gauge is fixed only by descending to
an atom `±`.

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

Pure recognition + assembly. The only new lean is `plus_seed_ne_bot_of_undischarged` /
`minus_seed_ne_bot_of_discharged` (one `recognizeUndischarged_lfp` / `recognizeDischarged_lfp` witness
each) and their assembly into `bot_holdsNeitherSign` + the four `GaugeNeutralValue` cases — over
`le_bot_iff` (Mathlib), `plus_inf_minus_eq_bot` / `plus_le_zero` / `minus_le_zero` /
`seed_zero_eq_join` (`PersistenceLfp.lean`), and `not_minus_le_plus_of_both` /
`not_plus_le_minus_of_both` / `zero_holdsFullSpectrum` (`SeedGaugeBiasDelegation.lean`). No new
geometric content; the recognition is that `⊥`'s "neither" content completes the powerset, and that
`⊥` is the un-tamped ground = the functor's input (the prose deposit).

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeEmptyCommitment` is clean, zero
sorry/warnings; depends on `recognizeUndischarged_lfp` / `recognizeDischarged_lfp` /
`SeedSign.seed` / `SeedSign.plus_inf_minus_eq_bot` / `plus_le_zero` / `minus_le_zero` in
`PersistenceLfp.lean`, `LedgerPersistence.BothDebtKinds` in `SeedGaugeFreedom.lean`, and
`not_minus_le_plus_of_both` / `not_plus_le_minus_of_both` / `zero_holdsFullSpectrum` in
`SeedGaugeBiasDelegation.lean`.)
-/

import Foam.SeedGaugeBiasDelegation

namespace Foam

/-! ## The fork-seeds are non-empty under their debt-kind — the contrapositive-companions of
brick 15's collapse-lemmas

Brick 15 (`SeedGaugeFreedom.lean`) proved the *collapse* direction: no live debt ⇒ `+.seed = ⊥`,
no settled debt ⇒ `−.seed = ⊥`. Here is the companion *non-emptiness* direction: a debt of the
matching kind is a read-face witnessing the fork-seed is non-empty. These drive `⊥`'s "neither"
content. -/

/-- **A live debt makes `+.seed` non-empty.** The read-face `LP.holds d` of an undischarged debt `d`
    is undischarged-backed, hence in `+.seed = lfp recognizeUndischarged` (`recognizeUndischarged_lfp`)
    — so `+.seed ≠ ⊥`. Companion to brick 15's `plus_seed_eq_bot_of_no_undischarged`. -/
theorem plus_seed_ne_bot_of_undischarged (LP : LedgerPersistence)
    (h : ∃ d, ¬ LP.Discharged d) : SeedSign.plus.seed LP ≠ ⊥ := by
  obtain ⟨d, hd⟩ := h
  have hmem : SeedSign.plus.seed LP (LP.holds d) := by
    show OrderHom.lfp (recognizeUndischarged LP) (LP.holds d)
    rw [recognizeUndischarged_lfp]; exact ⟨d, rfl, hd⟩
  intro heq
  rw [heq] at hmem
  exact hmem

/-- **A settled debt makes `−.seed` non-empty.** The read-face `LP.holds d` of a discharged debt `d`
    is discharged-backed, hence in `−.seed = lfp recognizeDischarged` (`recognizeDischarged_lfp`) — so
    `−.seed ≠ ⊥`. Companion to brick 15's `minus_seed_eq_bot_of_no_discharged`. -/
theorem minus_seed_ne_bot_of_discharged (LP : LedgerPersistence)
    (h : ∃ d, LP.Discharged d) : SeedSign.minus.seed LP ≠ ⊥ := by
  obtain ⟨d, hd⟩ := h
  have hmem : SeedSign.minus.seed LP (LP.holds d) := by
    show OrderHom.lfp (recognizeDischarged LP) (LP.holds d)
    rw [recognizeDischarged_lfp]; exact ⟨d, rfl, hd⟩
  intro heq
  rw [heq] at hmem
  exact hmem

/-! ## `⊥` carries neither sign — the dual of `0`'s `HoldsFullSpectrum` -/

/-- **A scope holds *neither* sign** — the dual of `SeedSign.HoldsFullSpectrum`. `⊥` is the witness;
    `0` is the witness for the dual `HoldsFullSpectrum`. The two together with the `±` one-each cases
    characterize all four BA elements by sign-content. -/
def HoldsNeitherSign (LP : LedgerPersistence) (S : Scope) : Prop :=
  ¬ SeedSign.plus.seed LP ≤ S ∧ ¬ SeedSign.minus.seed LP ≤ S

/-- **`⊥` carries neither sign** (under unresolved tension `BothDebtKinds`; *no injectivity*). Through
    `le_bot_iff` (`±.seed ≤ ⊥ ⟺ ±.seed = ⊥`) and the non-emptiness companions: under both debt-kinds
    each fork-seed is non-empty, so neither is `≤ ⊥`. This is the **dual of `zero_holdsFullSpectrum`**
    (`0` carries both): the empty seed `⊥` carries neither, completing the powerset characterization
    `{⊥ ↦ ∅, + ↦ {+}, − ↦ {−}, 0 ↦ {+, −}}` of the BA's four elements.

    `⊥ = P₀ = ∅` is the **un-tamped ground**: not a fourth disposition but the *absence* of the
    external commitment. The tamp commits a *nonempty, sign-bearing* seed `P₀ ∈ {+, −, 0}`; `⊥` is the
    no-tamp, the functor's input (§VIII geometry-only / pre-commitment), fixed under the gated `F`
    (`applyRules_lfp_bot`, brick 9). -/
theorem bot_holdsNeitherSign (LP : LedgerPersistence) (hboth : LP.BothDebtKinds) :
    HoldsNeitherSign LP ⊥ :=
  ⟨fun hle => plus_seed_ne_bot_of_undischarged LP hboth.2 (le_bot_iff.mp hle),
   fun hle => minus_seed_ne_bot_of_discharged LP hboth.1 (le_bot_iff.mp hle)⟩

/-- **`⊥ = + ⊓ −` — the bottom is the meet of the atoms** (under `holds`-injectivity), the lattice
    **dual** of `0 = + ⊔ −` (`seed_zero_eq_join`, top = join of the atoms). Just `.symm` of
    `plus_inf_minus_eq_bot` (brick 11), foregrounded here as the second `2²`-pinning anchor: `⊥` is
    the **overlap of the two one-sign commitments** — `+` and `−` agree on nothing, so committing to
    nothing is exactly their meet. With `0 = + ⊔ −` this pins `{⊥, +, −, 0}` as the full `2²`. -/
theorem bot_eq_plus_inf_minus (LP : LedgerPersistence) (hinj : Function.Injective LP.holds) :
    (⊥ : Scope) = SeedSign.plus.seed LP ⊓ SeedSign.minus.seed LP :=
  (SeedSign.plus_inf_minus_eq_bot LP hinj).symm

/-! ## `{⊥, 0}` are the two gauge-neutral values — refining brick 16's `SeedSign`-level neutrality -/

/-- **A scope is a gauge-neutral *value*** when its sign-content is unchanged under exchanging the two
    signs — `+ ≤ S ↔ − ≤ S`. The gauge-swap `+ ↔ −` (brick 16) acts on sign-content as
    `(a, b) ↦ (b, a)`; its fixed points are the swap-symmetric subsets `∅` (neither) and `{+, −}`
    (both). So among the BA's four elements, `GaugeNeutralValue` picks out exactly `{⊥, 0}` — the
    `Scope`-level refinement of brick 16's `SeedSign`-level `gaugeNeutral_iff_zero` (which sees only
    `{0}`, `⊥` not being a `SeedSign`). -/
def GaugeNeutralValue (LP : LedgerPersistence) (S : Scope) : Prop :=
  SeedSign.plus.seed LP ≤ S ↔ SeedSign.minus.seed LP ≤ S

/-- **`⊥` is gauge-neutral — by emptiness** (under tension). Its sign-content is `(∅)`: neither sign,
    swap-symmetric vacuously (`False ↔ False`). `⊥` is the pole *before* the commitment. -/
theorem gaugeNeutralValue_bot (LP : LedgerPersistence) (hboth : LP.BothDebtKinds) :
    GaugeNeutralValue LP ⊥ :=
  have h := bot_holdsNeitherSign LP hboth
  iff_of_false h.1 h.2

/-- **`0` is gauge-neutral — by fullness.** Its sign-content is `{+, −}`: both signs, swap-symmetric
    (`True ↔ True`, via `plus_le_zero` / `minus_le_zero`). `0` is the pole that *declines* the
    commitment — both signs held, bias-delegated (brick 16). -/
theorem gaugeNeutralValue_zero (LP : LedgerPersistence) :
    GaugeNeutralValue LP (SeedSign.zero.seed LP) :=
  iff_of_true (SeedSign.plus_le_zero LP) (SeedSign.minus_le_zero LP)

/-- **`+` is *not* gauge-neutral** (under inj + tension) — it is gauge-broken. Sign-content `{+}`:
    carries `+` (reflexively) but not `−` (`not_minus_le_plus_of_both`), so `True ↔ False` fails. The
    gauge is fixed here — one sign, the be-yourself commitment. -/
theorem not_gaugeNeutralValue_plus (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) :
    ¬ GaugeNeutralValue LP (SeedSign.plus.seed LP) :=
  fun h => not_minus_le_plus_of_both LP hinj hboth (h.mp le_rfl)

/-- **`−` is *not* gauge-neutral** (under inj + tension) — it is gauge-broken. Sign-content `{−}`:
    carries `−` (reflexively) but not `+` (`not_plus_le_minus_of_both`), so `False ↔ True` fails. The
    gauge is fixed here — one sign, the leave commitment. -/
theorem not_gaugeNeutralValue_minus (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) :
    ¬ GaugeNeutralValue LP (SeedSign.minus.seed LP) :=
  fun h => not_plus_le_minus_of_both LP hinj hboth (h.mpr le_rfl)

end Foam
