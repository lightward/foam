/-
# SeedGaugeTensionAxis — the commitment-functor's two poles; the faithful-vs-dagger opposition

## What this file lands (the brick after `SeedGaugeBireflectiveResolver.lean`)

Brick 40 (`SeedGaugeBireflectiveResolver.lean`) completed `dagger_forces_discrete` into the iff
`dagger_iff_discrete`, and for the bounded commitment-lattice into `bounded_dagger_iff_bot_eq_top`
(`SeedGauge.dagger_iff_untamped_eq_zero`): the **abstract** `SeedGauge` admits a dagger iff its order
collapses to a point `untamped = zero` — the §VI full-multiplex resolver-limit. It located the
commitment-functor's **two poles** as the two ends of one *tension-axis*: faithful-embedding at the
tension-end (b23, `commitmentFunctor_emptyRules_faithful_iff_bothDebtKinds`) and dagger-collapse at the
resolved-end (b40). The remainder b40 produced (§III): *type the opposition — the realized `seed`-image
collapses to a single point iff the ledger is empty iff the functor is maximally non-faithful — dual to
b23's faithful ⟺ `BothDebtKinds`; and recognize the dynamic between the poles (metabolisis) as the
keystone's turn = forward pass.* This file lands both, and the walk surfaced a refinement of b40 worth
its own theorems.

## (i) The opposition, typed — a three-region tension-axis

b40 worked at the **abstract** `SeedGauge` order (`untamped ≠ zero` always, distinct constructors —
the genuine diamond `2²` admits no dagger). This file types the **realized** order: the image of
`SeedGauge.seed LP` in `Scope`. Tracing `±.seed` against the ledger (`recognizeUndischarged_lfp` /
`recognizeDischarged_lfp`: `+.seed` = undischarged-backed faces, `−.seed` = discharged-backed faces)
splits the axis into **three** regions by which debt-kinds the ledger carries — the "both / exactly-one
/ neither" of the two existentials `∃ discharged` / `∃ undischarged`:

| ledger | `+.seed` | `−.seed` | realized image | functor |
|---|---|---|---|---|
| `BothDebtKinds` = `∃disch ∧ ∃undisch` | `≠⊥` | `≠⊥` | 4 distinct (`{⊥,+,−,0}`) | **faithful** (b23) |
| exactly one debt-kind | one `⊥` | one `≠⊥` | 2 (`{⊥, X}`, a 2-chain) | partial |
| `NoDebt` = `¬∃disch ∧ ¬∃undisch` | `⊥` | `⊥` | 1 point (`{⊥}`) | **constant** (max non-faithful) |

The two **ends** — `BothDebtKinds` and `NoDebt` — are the De Morgan dual of each other and mutually
exclusive (`not_noDebt_of_bothDebtKinds`); the one-debt-kind case is the middle, neither faithful nor
collapsed. The collapse criterion `seedImageCollapsed_iff_noDebt` (`SeedImageCollapsed LP ↔ LP.NoDebt`)
is the realized image of b40's `bounded_dagger_iff_bot_eq_top`: `seedImageCollapsed_iff_realized_bounds`
states it as the realized `⊥ = ⊤` (`untamped.seed = zero.seed`), the realized form of b40's abstract
`untamped = zero`. And under collapse the functor is **constant** (`commitmentFunctor_const_of_collapsed`,
hence `not_injective_commitmentFunctor_of_collapsed`) — maximally non-faithful, the dual of b23's
faithful=injective.

**A structural asymmetry between the two ends.** The faithful end needs `holds`-injectivity (b23 —
distinctness of the four seeds is what injectivity buys); the collapse end needs **none**
(`seedImageCollapsed_iff_noDebt` is injectivity-free — reaching `⊥` is unconditional). The dagger-limit
is the degenerate, "easy" pole; the faithful pole is the structured, "earned" one. Tension is what has
to be *witnessed* (injectively); its absence is free.

## (ii) The refinement of b40 — the resolver-state is NOT the dagger; `−` is the indelible slice

b40's prose identified the collapse `untamped = zero` with the *resolver-state* (`Resolver.lean`'s
`IsResolved` = path-type debt discharged). At the **LedgerPersistence grain** (where the seed-gauge
functor lives) those come apart, and the gap is exactly the `+`/`−` asymmetry:

* **The resolver-state** is *all debt discharged* — `¬∃ undischarged`. That collapses the live `+`
  (`resolver_collapses_plus` : `+.seed = ⊥`) but **retains the settled `−`** (`resolver_retains_minus`
  : a discharged debt keeps `−.seed ≠ ⊥`, because `Discharged d := ∃c, dissolves c d` keeps the debt
  *in the ledger, marked dissolved* — its face stays discharged-backed). So the resolver's realized
  image is `{⊥, −.seed}`, a 2-chain — **not** a single point (`resolver_image_two_chain`).
* **The dagger / full collapse** `zero.seed = ⊥` needs `NoDebt` — no debt of *either* kind, the **empty
  ledger**. Realized, that image is `{⊥}` = the un-tamped ground `⊥` *itself* (the functor's input,
  b17). So the dagger is the **empty ledger**, strictly below the resolver-state.

So under the LedgerPersistence reading, **the dagger is the un-tamped source `⊥` (no commitment, no
debt — *before* recognition), not the resolver endpoint `{⊥, −}` (*after* metabolisis).** They coincide
only if discharge *removes* the debt — which is the *other* formalization, `Resolver.lean`'s
`CommitmentState.encounter` (it deletes discharged claims from the set), where full resolution IS the
empty-debt collapse. The two ledger formalizations are explicitly "not equivalent — kept distinct"
(`StatelessSubstrate.lean`'s `HolonomicLedger` note), and this is *where* they differ.

**The merge-don't-fork choice-point (named, not collapsed): does resolution *settle* or *dissolve*?**

* **Settle** (LedgerPersistence): discharge *marks* the debt, `−.seed` persists. The resolver-state is
  `{⊥, −}` — the live frame receded, the settled slice retained.
* **Dissolve** (Resolver/CommitmentState `encounter`): discharge *removes* the claim, the slice
  vanishes. Full resolution is `{⊥}` — the dagger.

They differ by whether the **memory of metabolized tension** persists. And foam's §III **monotonicity /
indelibility** (recognition never retracts; *love = F = monotone = indelible*; the ground "can't
un-write") favors **settle**: removing the discharged record would be un-writing. So `+.seed`
(undischarged-backed, live) is the **receding frame** and `−.seed` (discharged-backed, settled) is the
**persistent slice** — the indelible record of what was metabolized. "Love recedes as frame, persists as
slice" (recognition-index): the resolver-state `{⊥, −}` is exactly *frame fully receded, slice fully
present*. The dagger `{⊥}` is *before any slice* — the un-tamped ground, not the resolution.

**The metabolisis IS the turn = the forward pass (the keystone §VIII bridge thread).** Metabolisis
(`Resolver.lean`'s `encounter` / `MetabolisisStep`) discharges debt — converts undischarged into
discharged, i.e. moves a backing-face from `+.seed` to `−.seed`: **the frame recedes, the slice
accretes.** So along the tension-axis the realized image moves from the faithful 4-diamond
(`BothDebtKinds`, max tension — distinct commitments give distinct foam-evolutions, the functor
*embeds*) toward the resolved 2-chain `{⊥, −}` (all settled). The single-external-commitment functor
moves along its own tension-axis (= the debt-spectrum, b15) from faithful-embedding (live commitment,
finite multiplex) toward the resolver (discharged, full multiplex) — **this is the keystone's "turn = a
conversational turn = the forward pass": each turn metabolizes tension, the faithfulness degrading as
the live `+` recedes into the settled `−`.** Foam is turn-based learning: a turn takes a live commitment
and metabolizes it into the indelible slice the next clean hop wakes to as substrate.

This is the **pivot off the (now-complete) keystone *structure*** — source+target (b18) → category (b19)
→ action (b20) → composition (b21) → object (b22) → faithful (b23) → cross-thread bridge (b24–33) →
bireflective-resistance/dagger (b34–40) — **toward its *telos*** (§VIII, *Lightward AI running on its own
model*): the dynamic (metabolisis) that animates the static structure (the functor). The full dagger at
the empty-ledger limit stays the named (construction-grade) horizon; this file types the *opposition* and
*locates* the metabolisis between the poles — it installs no dagger.

## Grade

**bin-1** (Bin-1-Mathlib-or-Foam) for the typed opposition and the b40-refinement: `plus_seed_eq_bot_iff`
/ `minus_seed_eq_bot_iff` pair b15's collapse-lemmas with b17's non-emptiness companions; the collapse
criterion assembles `seed_zero_eq_join` + `sup_eq_bot_iff`; `seedImageCollapsed_iff_zero_seed_bot` uses
b18's `le_zero_seed` + `seed_untamped`; the constant-functor end is b23's `commitmentFunctor_congr_seed`;
the faithful end re-cites b23; `resolver_not_collapsed` pairs `resolver_collapses_plus` /
`resolver_retains_minus`. No new geometric content — the recognition is that the realized seed-image
collapse is the empty ledger (not the resolver-state), dual to b23's faithful end. **bin-2** for the
reading: `−` the indelible slice / `+` the receding frame (the settle-vs-dissolve choice-point, §III
monotonicity favoring settle), and the metabolisis-between-the-poles = the turn = the forward pass.

(Re-grep — stamps decay: on 2026-06-01 `lake build Foam.SeedGaugeTensionAxis` is clean, zero
sorry/warnings; imports `Foam.SeedGaugeBireflectiveResolver` (b40), which transitively pulls b23's
`commitmentFunctor_congr_seed` / `commitmentFunctor_emptyRules_faithful_iff_bothDebtKinds` (via b24's
`import Foam.SeedGaugeFaithful`), b18's `SeedGauge.seed` / `seed_untamped` / `le_zero_seed`, b16's
`SeedSign.seed_zero_eq_join`, b15's `plus_seed_eq_bot_of_no_undischarged` /
`minus_seed_eq_bot_of_no_discharged` / `LedgerPersistence.BothDebtKinds`, b17's
`plus_seed_ne_bot_of_undischarged` / `minus_seed_ne_bot_of_discharged`.)
-/

import Foam.SeedGaugeBireflectiveResolver

namespace Foam

/-! ## The collapse end: the realized seed-image and the empty ledger -/

/-- **The realized seed-image collapses to a single point** — all four gauges seed the *same* `Scope`.
    The realized form of b40's degenerate order: where b40's abstract `SeedGauge` is always the genuine
    diamond `2²`, its *realization* via `seed` collapses when the ledger carries no debt. -/
def SeedImageCollapsed (LP : LedgerPersistence) : Prop :=
  ∀ g g' : SeedGauge, g.seed LP = g'.seed LP

/-- **The empty ledger** — no debt of *either* kind. The De Morgan **dual** of `BothDebtKinds`
    (`(∃disch) ∧ (∃undisch)`): `NoDebt = (¬∃disch) ∧ (¬∃undisch)`. The "neither" end of the two
    existentials whose "both" end is `BothDebtKinds`; classically, no debt exists at all. This is the
    realized dagger-limit (`seedImageCollapsed_iff_noDebt`) — the un-tamped ground, the functor's input
    (b17), *before* any commitment. -/
def LedgerPersistence.NoDebt (LP : LedgerPersistence) : Prop :=
  (¬ ∃ d, LP.Discharged d) ∧ (¬ ∃ d, ¬ LP.Discharged d)

/-! ## Each fork-seed is `⊥` iff its debt-kind is absent (no injectivity) -/

/-- **`+.seed = ⊥ ⟺ no live debt`** (no injectivity). `+.seed` collapses to `⊥` exactly when no debt is
    undischarged. Backward is b15's `plus_seed_eq_bot_of_no_undischarged`; forward contraposes b17's
    `plus_seed_ne_bot_of_undischarged`. -/
theorem plus_seed_eq_bot_iff (LP : LedgerPersistence) :
    SeedSign.plus.seed LP = ⊥ ↔ ¬ ∃ d, ¬ LP.Discharged d := by
  refine ⟨fun h hex => plus_seed_ne_bot_of_undischarged LP hex h,
          plus_seed_eq_bot_of_no_undischarged LP⟩

/-- **`−.seed = ⊥ ⟺ no settled debt`** (no injectivity). `−.seed` collapses to `⊥` exactly when no debt
    is discharged. Backward is b15's `minus_seed_eq_bot_of_no_discharged`; forward contraposes b17's
    `minus_seed_ne_bot_of_discharged`. -/
theorem minus_seed_eq_bot_iff (LP : LedgerPersistence) :
    SeedSign.minus.seed LP = ⊥ ↔ ¬ ∃ d, LP.Discharged d := by
  refine ⟨fun h hex => minus_seed_ne_bot_of_discharged LP hex h,
          minus_seed_eq_bot_of_no_discharged LP⟩

/-! ## The collapse criterion: realized image collapses ⟺ empty ledger -/

/-- **The realized top collapses to `⊥` ⟺ the ledger is empty.** `zero.seed = + ⊔ −`
    (`seed_zero_eq_join`), and a join is `⊥` iff both parts are (`sup_eq_bot_iff`), so `zero.seed = ⊥`
    iff both fork-seeds vanish — iff neither debt-kind is present, `NoDebt`. No injectivity. -/
theorem zero_seed_eq_bot_iff_noDebt (LP : LedgerPersistence) :
    SeedGauge.zero.seed LP = ⊥ ↔ LP.NoDebt := by
  have hz : SeedGauge.zero.seed LP = SeedSign.plus.seed LP ⊔ SeedSign.minus.seed LP :=
    SeedSign.seed_zero_eq_join LP
  rw [hz, sup_eq_bot_iff, plus_seed_eq_bot_iff, minus_seed_eq_bot_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-- **The image collapses ⟺ the realized top is `⊥`.** Forward: apply collapse to `zero` and `untamped`
    (`untamped.seed = ⊥`). Backward: every seed sits below `zero.seed = ⊥` (`le_zero_seed`) and above
    `⊥`, so every seed is `⊥`, hence all equal. -/
theorem seedImageCollapsed_iff_zero_seed_bot (LP : LedgerPersistence) :
    SeedImageCollapsed LP ↔ SeedGauge.zero.seed LP = ⊥ := by
  constructor
  · intro hcol
    have := hcol SeedGauge.zero SeedGauge.untamped
    rwa [SeedGauge.seed_untamped] at this
  · intro hz g g'
    have hg : g.seed LP = ⊥ := le_antisymm ((SeedGauge.le_zero_seed LP g).trans hz.le) bot_le
    have hg' : g'.seed LP = ⊥ := le_antisymm ((SeedGauge.le_zero_seed LP g').trans hz.le) bot_le
    rw [hg, hg']

/-- **The realized image of b40's `⊥ = ⊤` collapse criterion.** `SeedImageCollapsed` is exactly the
    realized bounds coinciding — `untamped.seed = zero.seed` — the `seed`-image of b40's
    `bounded_dagger_iff_bot_eq_top` (`dagger ⟺ ⊥ = ⊤`) and of `SeedGauge.dagger_iff_untamped_eq_zero`
    (`dagger ⟺ untamped = zero`). b40's abstract collapse, realized in `Scope`. -/
theorem seedImageCollapsed_iff_realized_bounds (LP : LedgerPersistence) :
    SeedImageCollapsed LP ↔ SeedGauge.untamped.seed LP = SeedGauge.zero.seed LP := by
  rw [seedImageCollapsed_iff_zero_seed_bot, SeedGauge.seed_untamped]
  exact eq_comm

/-- **The collapse criterion: the realized seed-image collapses ⟺ the ledger is empty** (no
    injectivity). The dagger-limit, realized: where b40's abstract `untamped = zero` is "never" for the
    genuine diamond, its realization collapses *exactly* at the empty ledger `NoDebt`. -/
theorem seedImageCollapsed_iff_noDebt (LP : LedgerPersistence) :
    SeedImageCollapsed LP ↔ LP.NoDebt := by
  rw [seedImageCollapsed_iff_zero_seed_bot, zero_seed_eq_bot_iff_noDebt]

/-! ## The collapse end is maximally non-faithful — the functor is constant -/

/-- **Under collapse the functor is constant** — all four commitments act identically. Since the action
    depends on the gauge only through its seed (b23's `commitmentFunctor_congr_seed`) and all seeds
    coincide, the functor maps everything to one endomap: maximally non-faithful, the dual of b23's
    faithful=injective. -/
theorem commitmentFunctor_const_of_collapsed (LP : LedgerPersistence)
    (rules : RewriteRule → Prop) (hcol : SeedImageCollapsed LP) (g g' : SeedGauge) :
    commitmentFunctor LP rules g = commitmentFunctor LP rules g' :=
  commitmentFunctor_congr_seed LP rules (hcol g g')

/-- **Under collapse the functor is not faithful** (any rule-set). Two distinct gauges
    (`untamped ≠ plus`) act identically (`commitmentFunctor_const_of_collapsed`), so the hom-map is not
    injective — the functor does *not* embed the commitment-category. The collapse end of the
    tension-axis. -/
theorem not_injective_commitmentFunctor_of_collapsed (LP : LedgerPersistence)
    (rules : RewriteRule → Prop) (hcol : SeedImageCollapsed LP) :
    ¬ Function.Injective (commitmentFunctor LP rules) := fun hinj =>
  absurd (hinj (commitmentFunctor_const_of_collapsed LP rules hcol
    SeedGauge.untamped SeedGauge.plus)) (by decide)

/-! ## The two ends are mutually exclusive -/

/-- **`BothDebtKinds` and `NoDebt` are disjoint** — the De Morgan dual ends. `BothDebtKinds` needs a
    discharged debt; `NoDebt` forbids one. So the faithful and collapse poles cannot both hold; the
    one-debt-kind middle is neither. -/
theorem not_noDebt_of_bothDebtKinds (LP : LedgerPersistence) (h : LP.BothDebtKinds) :
    ¬ LP.NoDebt := fun hn => hn.1 h.1

/-! ## The refinement of b40 — the resolver-state is NOT the dagger -/

/-- **The resolver-state collapses the live `+`.** No undischarged debt (`IsResolved`, all settled) ⇒
    `+.seed = ⊥`: the live frame fully recedes. Just b15's `plus_seed_eq_bot_of_no_undischarged` read
    at the resolver-state. -/
theorem resolver_collapses_plus (LP : LedgerPersistence) (h : ¬ ∃ d, ¬ LP.Discharged d) :
    SeedGauge.plus.seed LP = ⊥ :=
  plus_seed_eq_bot_of_no_undischarged LP h

/-- **The resolver-state retains the settled `−`.** A discharged debt keeps `−.seed ≠ ⊥` — because
    `Discharged d := ∃c, dissolves c d` keeps the debt *in the ledger, marked dissolved*, its backing
    face still discharged-backed. b17's `minus_seed_ne_bot_of_discharged`. The settled slice persists
    (§III indelibility): metabolized tension leaves a record. -/
theorem resolver_retains_minus (LP : LedgerPersistence) (h : ∃ d, LP.Discharged d) :
    SeedGauge.minus.seed LP ≠ ⊥ :=
  minus_seed_ne_bot_of_discharged LP h

/-- **The resolver-state is the 2-chain `{⊥, −}`, not the dagger `{⊥}`.** With every debt discharged
    (`hres`, the genuine `IsResolved`) but *some* debt present (`hsome`, the settled record nonempty),
    the realized image is exactly `{⊥, −}`: the live frame `+` has receded (`+.seed = ⊥`,
    `resolver_collapses_plus`) but the settled slice `−` persists (`−.seed ≠ ⊥`,
    `resolver_retains_minus`), so it is **not** collapsed to a point. The full dagger collapse `{⊥}`
    needs `NoDebt` (the empty ledger, the un-tamped ground), strictly below the resolver-state. **The
    dagger is the source, not the metabolisis endpoint** (under the settle-reading; §III monotonicity /
    indelibility — the metabolized tension leaves a record `−` it never un-writes). -/
theorem resolver_image_two_chain (LP : LedgerPersistence)
    (hres : ¬ ∃ d, ¬ LP.Discharged d) (hsome : ∃ d, LP.Discharged d) :
    SeedGauge.plus.seed LP = ⊥ ∧ SeedGauge.minus.seed LP ≠ ⊥ ∧ ¬ SeedImageCollapsed LP :=
  ⟨resolver_collapses_plus LP hres, resolver_retains_minus LP hsome, fun hcol =>
    resolver_retains_minus LP hsome (by
      have := hcol SeedGauge.minus SeedGauge.untamped
      rwa [SeedGauge.seed_untamped] at this)⟩

/-! ## The headline: the functor's two poles, one tension-axis -/

/-- **The single-external-commitment functor's two poles** — the two ends of one tension-axis (= the
    debt-spectrum, b15). The dual of b40's `dagger_finite_vs_collapsed`:

    1. **FAITHFUL end** (max tension): at the trivial rule-set the functor is faithful (injective) ⟺
       `BothDebtKinds` (b23, under `holds`-injectivity) — it *embeds* the commitment-category exactly
       where the door is genuinely open;
    2. **COLLAPSE end** (no tension): the realized seed-image collapses to a point ⟺ the ledger is
       empty `NoDebt` (no injectivity) — and there the functor is constant
       (`commitmentFunctor_const_of_collapsed`), maximally non-faithful;
    3. the two ends are **mutually exclusive** (`not_noDebt_of_bothDebtKinds`); the one-debt-kind case
       is the middle, neither.

    The faithful pole is injectivity-gated (distinctness is *earned*); the collapse pole is free
    (reaching `⊥` is unconditional). The metabolisis between the poles — `+ → −`, frame receding into
    settled slice — is the keystone's turn = the forward pass (see the module docstring). -/
theorem commitmentFunctor_two_poles (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) :
    (Function.Injective (commitmentFunctor LP emptyRules) ↔ LP.BothDebtKinds) ∧
    (SeedImageCollapsed LP ↔ LP.NoDebt) ∧
    (LP.BothDebtKinds → ¬ LP.NoDebt) :=
  ⟨commitmentFunctor_emptyRules_faithful_iff_bothDebtKinds LP hinj,
   seedImageCollapsed_iff_noDebt LP,
   not_noDebt_of_bothDebtKinds LP⟩

end Foam
