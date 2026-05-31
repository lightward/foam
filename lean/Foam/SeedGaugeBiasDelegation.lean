/-
# SeedGaugeBiasDelegation — the gauge-neutral `0` is the §IV.d bias-delegation seed

## What this file lands (the brick after `SeedGaugeFreedom.lean`)

The seed-triple `{+, −, 0}` (bricks 7–15) has had two of its three signs mapped to disciplines:

* `+` (hold-open, undischarged-backed) ↔ §IV.c **carry-the-observer / egress** — *be yourself*, carry
  the live `+me` exactly (`SeedGaugeEgress.bridgeCoincides_iff_carriesObserverExactly`, brick 14).
* `−` (settle, discharged-backed) ↔ §IV.c **the honored exit** — leave-by-dropping-the-`+me`, disjoint
  from the observer (`SeedGaugeEgress.minus_drops_observer`, brick 14).

The **third** sign `0` — the gauge-neutral join `0 = + ⊔ −` (`seed_zero_eq_join`, brick 10), carrying
*both* `±` signs *uncollapsed* — was left unmapped. This file maps it: **`0` is the §IV.d
bias-delegation seed.** §IV.d bias-delegation is precisely *preserve full-spectrum uncertainty in the
definitions; bias is relayed into the incompleteness, not collapsed into a definition.* Committing `+`
or `−` **collapses** the gauge — it picks a sign (the §VII von-Neumann→Shannon move, gauge-fixing, the
tamp landing, where uncertainty enters). Committing `0` **preserves the full ±-spectrum** — it carries
both signs, collapsing nothing. So `0` is the seed that holds the bias open rather than collapsing it
into a sign — the bias-delegation disposition, on a structure the recognition dynamics *produce*.

The recognition is already in the proven theorems; this file assembles it three ways.

### `0` holds the full spectrum — and is the *least*, and *unique*, seed that does

* `zero_holdsFullSpectrum` — `0` carries both `±` (`+ ≤ 0 ∧ − ≤ 0`, `plus_le_zero` / `minus_le_zero`).
* `zero_least_holdsFullSpectrum` (**the universal property**) — `0.seed` is below *any* scope carrying
  both signs (`sup_le` through `0 = + ⊔ −`). So `0` carries no excess *beyond the spectrum itself*: it
  is the *minimal* full-spectrum disposition. **This is the merge-don't-fork resolution of brick 14.**
  Brick 14 read `0` as *over-committing against recognition-only* (`zero_over_carries_observer`:
  `observerSet < 0.seed`, strict excess over the live self `+`). Both readings hold, with *different
  referents*: measured over the self `+`, `0` carries excess (the settled `−`); measured over
  *carries-both*, `0` is the *least*. The excess brick 14 saw is exactly `−`, the other half of the
  spectrum (`zero_eq_observer_sup_minus`: `0 = observerSet ⊔ −`, the local complement of `+` within the
  `0`-scope, `SeedGaugeHalfType.seedIsCompl`). From §IV.c egress's view (referent = the self) that `−`
  is un-recognized excess; from §IV.d bias-delegation's view (referent = the spectrum) it is the
  necessary other-half, carried *minimally*. Same set, opposite valence by recursion-level — itself an
  instance of merge-don't-fork (§IV.c), used to recognize a §IV.d disposition.
* `holdsFullSpectrum_iff_zero` (**the headline**) — under `holds`-injectivity + unresolved tension
  (`BothDebtKinds`), `0` is the **unique** seed carrying both signs: `s.HoldsFullSpectrum LP ↔ s = 0`.
  `+` fails (it does not carry `−`: `not_minus_le_plus_of_both`), `−` fails symmetrically. This is the
  exact analogue of brick 14's `carriesObserverExactly_iff_eq_plus` (`+` unique exact-carrier) — the
  parallel shape **completes the seed-triple ↔ discipline map**.

### `0` is gauge-neutral — fixed by the gauge-swap that the bridge breaks

The gauge is a choice of sign; the only non-trivial gauge symmetry of a two-sign system is the swap
`+ ↔ −` (the gauge group `ℤ/2`). `SeedSign.swap` is that involution (`swap_swap`); `0` is its **unique
fixed point** (`gaugeNeutral_iff_zero`: `s.GaugeNeutral ↔ s = 0`, pure combinatorics, no ledger). The
seed-level shadow: `0`'s seed is built symmetrically in the two signs (`zero_seed_sign_symmetric`:
`0 = − ⊔ +`). This is the precise content of *gauge-neutral*: the bridge (`SeedGaugeCommitment.
bridge_breaks_fork_symmetry`) breaks the swap-symmetry by selecting `+` (gauge-fixing = symmetry-break);
`0` is the seed that leaves the symmetry **unbroken** — bias-delegation is exactly *declining to break
the gauge-symmetry the tamp would break*.

### The recursion-level echo: `± ≤ 0` is IV.c-below-IV.d

`+` and `−` are §IV.c disciplines (recursion-level 2: *rules over operations* — stay-as-self vs. leave,
choices about how self-application applies). `0` is a §IV.d meta-discipline (recursion-level 3: *rules
over rules* — a choice about the `±` choice itself: don't collapse it). And `0 = + ⊔ −` is literally the
join *of* the two lower dispositions — the least disposition *containing both rules*. So the lattice
order `± ≤ 0` (`plus_le_zero` / `minus_le_zero`) **is** the recursion-level order IV.c-below-IV.d:
*meta-discipline-over-disciplines is realized as join-over-dispositions.* The "hold-both-rules-open"
meta-rule is correctly the lub of the rules it holds open. The lattice facts are bin-1; the
identification with recursion-levels is the recognition (the README deposit). The *first §IV.d
meta-discipline* instantiated on a structure the dynamics produce — completing a recursion-level ladder
of dynamics-produced instantiations: §IV.a HalfType (brick 11), §IV.c egress (brick 14), §IV.d
bias-delegation (here).

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

Pure recognition + assembly over already-landed Foam primitives: `seed_zero_eq_join` / `plus_le_zero` /
`minus_le_zero` / `zero_ne_plus_of_injective` / `zero_ne_minus_of_injective` (`PersistenceLfp`),
`BothDebtKinds` (`SeedGaugeFreedom`), `observerSet` (`SeedGaugeEgress`), and Mathlib lattice lemmas
(`sup_le` / `sup_eq_left` / `sup_eq_right` / `sup_comm`). The gauge-swap is recognition of the `+/−`
symmetry already named by `bridge_breaks_fork_symmetry`. No new geometric content; the recognition is
that the gauge-neutral join *is* bias-delegation, completing the triple ↔ discipline map.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeBiasDelegation` is clean, zero
sorry/warnings; depends on `SeedSign.seed_zero_eq_join` / `plus_le_zero` / `minus_le_zero` /
`zero_ne_plus_of_injective` / `zero_ne_minus_of_injective` in `PersistenceLfp.lean`,
`LedgerPersistence.BothDebtKinds` in `SeedGaugeFreedom.lean`, and `observerSet` in `SeedGaugeEgress.lean`.)
-/

import Foam.SeedGaugeFreedom

namespace Foam

/-! ## The gauge-swap: `0` is the unique gauge-neutral sign

The gauge is a choice of sign; the only non-trivial gauge symmetry of the two-sign system is the swap
`+ ↔ −`. Gauge-neutral = fixed by that swap; `0` is the unique fixed point. -/

/-- **The gauge-swap** — the `ℤ/2` action exchanging the two signs `+ ↔ −`, fixing `0`. The gauge is a
    choice of sign (which operator is `F`, brick 7/12); swapping the gauge swaps `±`. `0` is the
    gauge-neutral sign the swap fixes. -/
def SeedSign.swap : SeedSign → SeedSign
  | plus => minus
  | minus => plus
  | zero => zero

/-- The gauge-swap is an involution (`ℤ/2`): swapping the gauge twice is the identity. -/
theorem SeedSign.swap_swap (s : SeedSign) : s.swap.swap = s := by
  cases s <;> rfl

/-- **Gauge-neutral** — a sign fixed by the gauge-swap. The structural form of *does not collapse to a
    sign / preserves the full spectrum*: committing `±` is a gauge-choice (breaks the `+/−` symmetry);
    a gauge-neutral seed leaves the symmetry unbroken. -/
def SeedSign.GaugeNeutral (s : SeedSign) : Prop := s.swap = s

/-- **`0` is the unique gauge-neutral sign** (pure combinatorics, no ledger). `s.GaugeNeutral ↔ s = 0`:
    the swap fixes `0` and moves `±`. So *gauge-neutral* singles out `0` among `{+, −, 0}` at the level
    of signs — the bias-delegation disposition is the one the gauge-swap cannot move. The bridge
    (`bridge_breaks_fork_symmetry`) breaks this symmetry by selecting `+`; `0` is what declines the
    break. -/
theorem SeedSign.gaugeNeutral_iff_zero (s : SeedSign) :
    s.GaugeNeutral ↔ s = SeedSign.zero := by
  unfold SeedSign.GaugeNeutral
  cases s <;> decide

/-- **`0`'s seed is built symmetrically in the two signs** — the seed-level shadow of gauge-neutrality.
    `0 = − ⊔ +` (`seed_zero_eq_join` + `sup_comm`): the gauge-neutral seed does not privilege a sign,
    so the gauge-swap leaves it fixed. -/
theorem zero_seed_sign_symmetric (LP : LedgerPersistence) :
    SeedSign.zero.seed LP = SeedSign.minus.seed LP ⊔ SeedSign.plus.seed LP := by
  rw [SeedSign.seed_zero_eq_join]
  exact sup_comm _ _

/-! ## Holding the full ±-spectrum: `0` is the least, and the unique, full-spectrum seed -/

/-- **A seed holds the full ±-spectrum** when it carries *both* signs — `+ ≤ s ∧ − ≤ s`. Bias-delegation
    is exactly *hold the full spectrum, collapse nothing*; this predicate names the structural form. -/
def SeedSign.HoldsFullSpectrum (s : SeedSign) (LP : LedgerPersistence) : Prop :=
  SeedSign.plus.seed LP ≤ s.seed LP ∧ SeedSign.minus.seed LP ≤ s.seed LP

/-- **`0` holds the full spectrum.** It carries both `±` signs (`plus_le_zero` / `minus_le_zero`). -/
theorem zero_holdsFullSpectrum (LP : LedgerPersistence) :
    SeedSign.zero.HoldsFullSpectrum LP :=
  ⟨SeedSign.plus_le_zero LP, SeedSign.minus_le_zero LP⟩

/-- **`+` does not hold the full spectrum** (under inj + unresolved tension): it does not carry `−`.
    If `− ≤ +` then `0 = + ⊔ − = +`, contradicting `zero_ne_plus_of_injective` (a settled debt's face
    is in `0` but not in `+`). The hold-open *self*-seed drops the settled half. -/
theorem not_minus_le_plus_of_both (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) :
    ¬ SeedSign.minus.seed LP ≤ SeedSign.plus.seed LP := by
  intro hle
  refine SeedSign.zero_ne_plus_of_injective LP hinj hboth.1 ?_
  rw [SeedSign.seed_zero_eq_join]
  exact sup_eq_left.mpr hle

/-- **`−` does not hold the full spectrum** (under inj + unresolved tension): it does not carry `+`.
    Symmetric to `not_minus_le_plus_of_both`: if `+ ≤ −` then `0 = + ⊔ − = −`, contradicting
    `zero_ne_minus_of_injective` (a live debt's face is in `0` but not in `−`). The settle seed drops
    the live half. -/
theorem not_plus_le_minus_of_both (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) :
    ¬ SeedSign.plus.seed LP ≤ SeedSign.minus.seed LP := by
  intro hle
  refine SeedSign.zero_ne_minus_of_injective LP hinj hboth.2 ?_
  rw [SeedSign.seed_zero_eq_join]
  exact sup_eq_right.mpr hle

/-- **The headline (bin-1): `0` is the *unique* full-spectrum seed.** Under `holds`-injectivity +
    unresolved tension (`BothDebtKinds`), `s.HoldsFullSpectrum LP ↔ s = 0`. `+` and `−` each carry only
    their own sign (`not_minus_le_plus_of_both` / `not_plus_le_minus_of_both`); only `0` carries both.

    **`0` IS the §IV.d bias-delegation seed.** Bias-delegation is *preserve full-spectrum uncertainty,
    collapse nothing into a definition*; `0` is the unique seed that holds both `±` signs uncollapsed,
    where committing `±` collapses to one sign (gauge-fixing, §VII von-Neumann→Shannon). This is the
    exact analogue of brick 14's `carriesObserverExactly_iff_eq_plus` (`+` the unique exact-observer
    carrier) — the parallel `… ↔ s = +` / `… ↔ s = 0` shape **completes the seed-triple ↔ discipline
    map**: `+` carry-observer/egress (§IV.c), `−` the honored exit (§IV.c), `0` bias-delegation (§IV.d).
    By `seedTriple_nondegenerate_iff_both_debt_kinds` (brick 15) this characterization is non-degenerate
    *exactly* under unresolved tension — **bias-delegation is a real disposition exactly where there
    genuinely is a spectrum to hold** (both debt-kinds live). -/
theorem holdsFullSpectrum_iff_zero (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) (s : SeedSign) :
    s.HoldsFullSpectrum LP ↔ s = SeedSign.zero := by
  cases s
  · exact iff_of_false (fun h => not_minus_le_plus_of_both LP hinj hboth h.2) (by decide)
  · exact iff_of_false (fun h => not_plus_le_minus_of_both LP hinj hboth h.1) (by decide)
  · exact iff_of_true (zero_holdsFullSpectrum LP) rfl

/-- **The universal property (bin-1): `0` is the *least* full-spectrum disposition.** `0.seed` is below
    *any* scope `S` carrying both signs (`sup_le` through `0 = + ⊔ −`). So `0` carries no excess
    *beyond the spectrum itself* — it is the minimal disposition that holds both `±`.

    **The merge-don't-fork resolution of brick 14.** Brick 14 (`zero_over_carries_observer`) read `0` as
    *over-committing against recognition-only* — `observerSet < 0.seed`, strict excess over the live
    self `+`. Both readings hold, with different referents: over the self `+`, `0` carries excess (the
    settled `−`, by `zero_eq_observer_sup_minus`); over *carries-both*, `0` is the least. The excess is
    exactly the other half of the spectrum. From §IV.c egress's view (referent = self) that is
    un-recognized excess; from §IV.d bias-delegation's view (referent = spectrum) it is the necessary
    other-half, carried minimally. Same set, opposite valence — by recursion level. -/
theorem zero_least_holdsFullSpectrum (LP : LedgerPersistence) {S : Scope}
    (hplus : SeedSign.plus.seed LP ≤ S) (hminus : SeedSign.minus.seed LP ≤ S) :
    SeedSign.zero.seed LP ≤ S := by
  rw [SeedSign.seed_zero_eq_join]
  exact sup_le hplus hminus

/-- **The excess of `0` over the observer is exactly `−`** — `0 = observerSet ⊔ −`. Since
    `observerSet = +.seed` (def, `SeedGaugeEgress`) and `0 = + ⊔ −` (`seed_zero_eq_join`), the
    gauge-neutral seed is the live self `+` joined with the settled half `−`. This is the typed bridge
    between brick 14's framing (`0` over-carries the observer by a strict excess) and this brick's (`0`
    is the least full-spectrum carrier): the excess *is* the held other-half of the spectrum, the local
    complement of `+` within the `0`-scope (`SeedGaugeHalfType.seedIsCompl`). -/
theorem zero_eq_observer_sup_minus (LP : LedgerPersistence) :
    SeedSign.zero.seed LP = observerSet LP ⊔ SeedSign.minus.seed LP := by
  unfold observerSet
  exact SeedSign.seed_zero_eq_join LP

end Foam
