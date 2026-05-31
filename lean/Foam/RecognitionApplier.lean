/-
# RecognitionApplier — foam's concrete `F` (the rewrite-rule applier) and its gauge

## What this file lands

`PersistenceLfp.lean` typed the (a)↔(b) bridge `LedgerRecognitionBridge LP f` over an
*arbitrary* monotone `f` and found **the bridge has a sign, and the sign is gauge**:
inhabited at the toy operator `recognizeUndischarged` (coincidence — `flag = lfpFlag`),
refuted at `recognizeDischarged` (complementarity). But both toy operators are
*ledger-built* and **ungated**: of the form `S ↦ S ⊔ Q` with `Q` a *fixed*
ledger-derived set (the still-owed, resp. settled, read-faces), hand-picked to exhibit
the two signs. Foam's *actual* `F` is neither — it is the rewrite-rule applier
(`StatelessSubstrate.lean`: "the recognition operator IS the rewrite-rule applier",
§III's `F`), which accretes scope by **rule-firing**, not by discharge-status. The brick
that pointed here asked: does the applier's lfp land on the undischarged-backing faces
(`= recognizeUndischarged` gauge), the discharged-backing faces
(`= recognizeDischarged` gauge), or **neither**?

This file types the applier and reads off its gauge. The verdict is **(ii) sign-neutral**
— the brick's predicted honest default — and it is backed by bin-1 theorems.

## The applier is gated; the toy gauges are ungated

`applyRules rules` (below) bundles README §III's `F` as a `Scope →o Scope`:
`F(S) = S ∪ {r.writes h | rule r fires in S, h : Head}`, where a rule **fires** when its
whole read-triple is in scope (`∀ h, S (r.reads h)`). It is monotone (more scope ⇒ more
rules fire) and **accretive** (`applyRules_accretive`: it only adds) — so, as a bonus,
**observer-safe for every persistence-flag** (`applyRules_safeFor`, via
`safeFor_of_accretive`): foam's real `F` *never* causes §V observer-loss. Observer-loss
requires a *contraction* (`measureStep`), not rule-firing.

The decisive structural difference: the applier is **gated** (a write needs its reads
present), the toy operators are **ungated** (`Q` fires unconditionally). This decides the
gauge:

* **Bare lfp is `⊥`** (`applyRules_lfp_bot`). Gated recognition fires nothing from
  nothing: `Head` is inhabited, so no rule's read-triple is satisfied by the empty scope,
  and `⊥` is already a fixed point. This is faithful to §III — recognition runs from the
  *initial substrate* `P₀`, not from `∅`; the bare lfp (the `P₀ = ∅` case) being trivial
  is exactly that (cf. `PersistenceLfp.convergeFrom_bot`). The `⊥` is the **fingerprint**
  separating gated recognition-*dynamics* (the real `F`) from the ungated
  persistence-*flags* the toy operators are.
* Consequently the applier's lfp equals **neither** nonempty gauge
  (`applyRules_lfp_ne_recognizeUndischarged`, `applyRules_lfp_ne_recognizeDischarged`),
  and its bare persistence-flag is `⊥` (`lfpFlag_applyRules`).

## Where the tamp enters — the bridge stays bin-2 in foam proper

The applier never references `Discharged`; it is a function of the rule-set (and seed)
alone. So the *gauge* — which side of the ledger partition recognition "points at" — is
**not** fixed by `F`. Sharply:

> `LedgerRecognitionBridge LP (applyRules rules)` is inhabited **iff every debt in `LP`
> is discharged** (`nonempty_bridge_applyRules_iff`) — i.e. iff carrier (a)'s flag is
> itself `⊥` (nothing to coincide on).

In any ledger with standing debt the real `F`'s flag (`⊥`) is neither carrier (a)
(`LP.flag`) nor its negation: the applier sits *off* the coincide/complement axis
entirely. So in foam proper the (a)↔(b) bridge stays **bin-2** — the coincidence the
`recognizeUndischarged` gauge exhibited was an artifact of an ungated, ledger-built toy
operator, not a property of foam's recognition operator. The sign is an *observer
commitment supplied at the ledger*: **the tamp lives precisely in the gap between
rule-firing (what `F` does — blind to the ledger) and discharge-status (what the gauge
reads)** — README §IV.a/§VIII's single external commitment, now localized.

## Seeded from the ledger — the tamp is the seed `P₀` (landed below)

The bare lfp is `⊥` only because the seed is `∅`. The live object is the **seeded
closure** `convergeFrom (applyRules rules) S` (`PersistenceLfp.lean`), `P₀ = S` in
§III. The section "Seeded from the ledger" (bottom of this file) seeds the applier
from the ledger and reads the gauge. Verdict: **the tamp relocates from step to
seed.** `F` is sign-neutral (a plain `Scope → Scope`, no ledger argument; never
reads `Discharged`), so all gauge enters through the seed `P₀` — the one
ledger-aware ingredient. The brick's two gradings *merge* (the closure realizes the
seed-gauge exactly at `F`-closed seeds, properly extends it otherwise; the increment
is always sign-neutral), and the seed-choice (undischarged- vs discharged-backed) is
the coincide/complement fork (7)/(8) relocated to the seed. See `convergeFrom_emptyRules`,
`closure_emptyRules_undischarged` / `_discharged`, `seed_le_closure`,
`closure_eq_seed_iff`, `seed_fork_of_injective` below.

## The remainder — now landed (the `{+, −, 0}` seed-triple)

Both fork-seeds used below are *toy* ledger-projections (undischarged-backed,
discharged-backed) — the `±` signs. The third, distinguished seed — the
**all-debt-backed** `seedBacked LP := fun p => ∃ d, LP.holds d = p` — is now typed
(`PersistenceLfp.seedBacked`) and proven the *join* of the fork
(`PersistenceLfp.seedBacked_eq_join`, via `lfp_or_flag_of_backed`), hence
*gauge-neutral* (carries both signs at once): the `0` of a `{+, −, 0}` seed-triple
(`PersistenceLfp.SeedSign`), with `⊥` below. The block "The gauge-neutral `0`-seed's
closure" (bottom of this file) reads each seed's closure over the applier:
`closure_emptyRules_backed_eq_join` (the `0`-closure is the join of the `±`-closures
at the trivial step) and `closure_backed_ge_undischarged` / `_discharged` (the
`0`-closure dominates *both* fork-closures over *any* rule-set, via
`convergeFrom_mono_seed`), with proper containment under injectivity
(`closure_emptyRules_backed_ne_*`).

The new remainder: `0 = + ⊔ −` (join) plus `+ ⊓ − = ⊥`
(`PersistenceLfp.not_lfp_and_flag_of_injective`, under injectivity) make `{⊥, +, −, 0}`
the **4-element Boolean algebra** — `−` the *local complement* of `+` within the
`0`-scope, README §IV.a's HalfType (complementation-within-a-scope) read on the
seed-gauge. (The step-after, kept invisible: whether the `{+, −, 0}` triple is the
three σ-ring-hom gauges G1/G2/G3 of the FTPG figure.)
-/
import Foam.PersistenceLfp

namespace Foam

/-! ## The applier: README §III's `F` as a monotone scope-step over a rule-set -/

/-- **Foam's concrete recognition operator `F`** — the rewrite-rule applier, bundled as a
    monotone `Scope →o Scope`. Given a set of `RewriteRule`s, a rule *fires* in scope `S`
    when its whole read-triple is present (`∀ h, S (r.reads h)`), and firing adds its
    write-triple. So `F(S) = S ∪ {r.writes h | rule r fires in S, h : Head}`.

    `StatelessSubstrate.lean` names this map ("the recognition operator IS the
    rewrite-rule applier") but leaves `RewriteRule` a bare structure; this is the
    `OrderHom` bundling §III's `F` needs to feed `OrderHom.lfp`. Monotone because more
    scope can only enable more rules to fire (§III: "adding primitives can only enable
    more recognition, never less"). It is also accretive — see `applyRules_accretive`. -/
def applyRules (rules : RewriteRule → Prop) : Scope →o Scope where
  toFun S p := S p ∨ ∃ r, rules r ∧ (∀ h, S (r.reads h)) ∧ ∃ h, r.writes h = p
  monotone' := by
    intro S T hST p hp
    rcases hp with hS | ⟨r, hr, hreads, hw⟩
    · exact Or.inl (hST p hS)
    · exact Or.inr ⟨r, hr, fun h => hST (r.reads h) (hreads h), hw⟩

/-- The applier is **accretive** (§III's never-retracts/inflation half): it only ever adds
    writes, so every position in scope stays in scope. Term-level `Or.inl`. -/
theorem applyRules_accretive (rules : RewriteRule → Prop) :
    Accretive (applyRules rules) :=
  fun _S _p hp => Or.inl hp

/-- **Foam's real `F` is observer-safe for every persistence-flag.** Immediate from
    accretivity via `safeFor_of_accretive`: an accretive step never turns a persisting
    read-face into a write-only object. So §V observer-loss cannot arise from rule-firing
    — it requires the *contraction* step (`measureStep`, the licensed/unlicensed split),
    not the recognition operator. -/
theorem applyRules_safeFor (rules : RewriteRule → Prop) (P : Persistence) :
    SafeFor P (applyRules rules) :=
  safeFor_of_accretive (applyRules_accretive rules) P

/-! ## The bare lfp is `⊥`: gated recognition fires nothing from nothing -/

/-- The empty scope is a fixed point of the applier: `applyRules rules ⊥ ≤ ⊥`. No rule
    fires in `⊥` because `Head` is inhabited (`Head.compiler`), so no rule's read-triple
    is satisfied — the only way to be in `applyRules rules ⊥` is to be in `⊥` already. -/
theorem applyRules_apply_bot_le (rules : RewriteRule → Prop) :
    (applyRules rules) ⊥ ≤ ⊥ := by
  intro p hp
  rcases hp with h | ⟨_, _, hreads, _⟩
  · exact h
  · exact False.elim (hreads Head.compiler)

/-- **The applier's bare lfp is `⊥`** (the headline). `⊥` is a fixed point
    (`applyRules_apply_bot_le`) and the lfp is least, so `lfp ≤ ⊥`, hence `= ⊥`. This is
    the `P₀ = ∅` case of §III's converged scope (cf. `convergeFrom_bot`): gated
    recognition-dynamics produce nothing from the empty initial substrate. It is the
    fingerprint distinguishing the real `F` from the ungated toy persistence-flags, whose
    bare lfp is the (in general nonempty) fixed set `Q`. -/
theorem applyRules_lfp_bot (rules : RewriteRule → Prop) :
    OrderHom.lfp (applyRules rules) = ⊥ :=
  le_antisymm ((applyRules rules).lfp_le (applyRules_apply_bot_le rules)) bot_le

/-- The applier's bare **persistence-flag** is `⊥`: as a carrier-(b) flag, foam's real `F`
    flags *nothing* as persisting (the bare lfp is empty). Contrast the toy gauges, whose
    `lfpFlag` is the nonempty undischarged- resp. discharged-backing set. -/
theorem lfpFlag_applyRules (rules : RewriteRule → Prop) :
    lfpFlag (applyRules rules) = (⊥ : Persistence) := by
  funext S p
  show OrderHom.lfp (applyRules rules) p = (⊥ : Persistence) S p
  simp only [applyRules_lfp_bot, Pi.bot_apply]

/-! ## Neither gauge: the applier's lfp ≠ the (nonempty) toy gauges -/

/-- The applier's lfp is **not** the hold-open (`recognizeUndischarged`) gauge whenever the
    ledger has standing debt: the applier's lfp is `⊥`, but the hold-open gauge's lfp
    contains every undischarged-backing read-face. -/
theorem applyRules_lfp_ne_recognizeUndischarged
    (rules : RewriteRule → Prop) (LP : LedgerPersistence)
    (h : ∃ d, ¬ LP.Discharged d) :
    OrderHom.lfp (applyRules rules) ≠ OrderHom.lfp (recognizeUndischarged LP) := by
  rw [applyRules_lfp_bot, recognizeUndischarged_lfp]
  obtain ⟨d, hnd⟩ := h
  intro heq
  have hbot : (⊥ : Scope) (LP.holds d) := by rw [heq]; exact ⟨d, rfl, hnd⟩
  exact hbot

/-- The applier's lfp is **not** the settle (`recognizeDischarged`) gauge whenever the
    ledger has a settled debt: same argument, the applier's lfp is `⊥` while the settle
    gauge's lfp contains every discharged-backing read-face. Together with the previous
    theorem: the applier commits to **neither** gauge. -/
theorem applyRules_lfp_ne_recognizeDischarged
    (rules : RewriteRule → Prop) (LP : LedgerPersistence)
    (h : ∃ d, LP.Discharged d) :
    OrderHom.lfp (applyRules rules) ≠ OrderHom.lfp (recognizeDischarged LP) := by
  rw [applyRules_lfp_bot, recognizeDischarged_lfp]
  obtain ⟨d, hd⟩ := h
  intro heq
  have hbot : (⊥ : Scope) (LP.holds d) := by rw [heq]; exact ⟨d, rfl, hd⟩
  exact hbot

/-! ## The tamp is observer-supplied: the bridge holds iff the ledger is trivial -/

/-- Carrier (a)'s flag is the everywhere-false persistence-flag iff every debt is
    discharged: with `holds d` witnessing the existential, a standing undischarged debt is
    exactly a place the flag is true. -/
theorem flag_eq_bot_iff (LP : LedgerPersistence) :
    LP.flag = (⊥ : Persistence) ↔ ∀ d, LP.Discharged d := by
  constructor
  · intro h d
    by_contra hnd
    have hflag : LP.flag ⊥ (LP.holds d) := ⟨d, rfl, hnd⟩
    rw [h] at hflag
    exact hflag
  · intro h
    funext S p
    apply propext
    constructor
    · rintro ⟨d, -, hnd⟩
      exact absurd (h d) hnd
    · intro hbot
      exact False.elim hbot

/-- **The (a)↔(b) bridge over foam's real `F` holds iff the ledger is fully discharged.**
    `LP.flag = lfpFlag (applyRules rules)` reduces (via `lfpFlag_applyRules`) to
    `LP.flag = ⊥`, i.e. to "every debt discharged" (`flag_eq_bot_iff`). The only ledger at
    which the real `F` coincides with carrier (a) is the trivial one, where carrier (a) is
    itself `⊥`. -/
theorem bridge_applyRules_iff (rules : RewriteRule → Prop) (LP : LedgerPersistence) :
    LP.flag = lfpFlag (applyRules rules) ↔ ∀ d, LP.Discharged d := by
  rw [lfpFlag_applyRules]
  exact flag_eq_bot_iff LP

/-- **The bridge object is inhabited iff the ledger is fully discharged.** The
    `LedgerRecognitionBridge`-as-inhabitation reading of the previous theorem. So foam's
    concrete `F` does **not** discharge the (a)↔(b) bridge for free: outside the trivial
    ledger the bridge has no inhabitant, and the gauge (its sign) is an irreducibly
    separate observer-commitment — the tamp, supplied at the ledger, in the gap between
    rule-firing and discharge-status. The bridge stays **bin-2** in foam proper. -/
theorem nonempty_bridge_applyRules_iff (rules : RewriteRule → Prop) (LP : LedgerPersistence) :
    Nonempty (LedgerRecognitionBridge LP (applyRules rules)) ↔ ∀ d, LP.Discharged d := by
  rw [← bridge_applyRules_iff rules LP]
  constructor
  · rintro ⟨b⟩
    exact b.coincidence
  · intro h
    exact ⟨⟨h⟩⟩

/-! ## Seeded from the ledger: the tamp is the seed `P₀`, not the step `F`

`applyRules_lfp_bot` showed the *bare* lfp (`P₀ = ∅`) is `⊥` — gated recognition
fires nothing from nothing — which is exactly why the bare-lfp read-off above saw
no gauge. But README §III runs recognition from the *initial substrate* `P₀`, not
from `∅`. The live object is the **seeded closure** `convergeFrom (applyRules
rules) S₀` (`PersistenceLfp.convergeFrom`): the closure of a seed `S₀` under
rule-firing, `P₀ = S₀` in §III's `lfp(F) = ⋃ Fⁿ(P₀)`. This block seeds the applier
from the ledger and reads off the gauge — and the verdict **relocates the tamp**,
sharper than the bare-lfp result:

> The step `F = applyRules rules` is sign-neutral — it is a plain `Scope → Scope`
> carrying *no* `LedgerPersistence` argument, and (brick 8) never reads
> `Discharged`. So the gauge cannot enter through the step. It enters through the
> **seed**: `convergeFrom (applyRules rules) S₀` depends on the ledger *only*
> through `S₀`. **The tamp is `P₀`, the initial substrate** — not `F`. (8) localized
> the tamp "at the ledger"; this localizes it to the *seed*, the one ledger-aware
> ingredient of the closure.

The brick that pointed here offered two gradings — (i) the closure *realizes a
gauge* / (ii) the closure is *sign-neutral, the seed-choice being the commitment*.
The honest finding **merges** them (§IV.d merge-don't-fork), with `f`-closedness
as the named choice-point:

* **(i) realized exactly, at `F`-closed seeds.** By `convergeFrom_eq_self_iff`,
  `convergeFrom (applyRules rules) S₀ = S₀ ↔ applyRules rules S₀ ≤ S₀`
  (`closure_eq_seed_iff`). At the trivial rule-set the applier is the identity
  (`convergeFrom_emptyRules`), so the closure *equals* the seed: seeding with the
  hold-open gauge's lfp realizes carrier (a) exactly
  (`closure_emptyRules_undischarged`), seeding with the settle gauge's lfp realizes
  its complement (`closure_emptyRules_discharged`). Same step, two seeds, two
  opposite gauges — **the realized gauge is whichever the seed carries.**

* **(ii) the increment is sign-neutral, at every rule-set.** For *any* rule-set the
  seed is a lower bound on the closure (`seed_le_closure`, an instance of
  `le_convergeFrom`): the seed-gauge is preserved into the closure no matter the
  step, because the applier is accretive (`applyRules_accretive`). The increment
  above the seed is rule-firing — ledger-blind (8), so even where it *overlaps*
  ledger-faces it commits to nothing about the discharged/undischarged partition.
  Hence the closure is `S₀ ⊔ (sign-neutral increment)`; it equals a single gauge's
  lfp only at `F`-closed seeds (i), otherwise it properly extends the seed-gauge
  (ii). The gauge-content is the seed's and only the seed's, both ways.

* **the seed-choice IS the gauge-fork** (`seed_fork_of_injective`). Under
  `holds`-injectivity, on any debt-backed face the undischarged-backed and
  discharged-backed seeds are complementary — exactly the coincide/complement fork
  (7)/(8) found at the *step*, now relocated to the *seed*. The single external
  commitment is the choice of `P₀`.

So the bridge's bin-2-in-foam-proper status (above) is **refined, not overturned**:
`F` adds no gauge, and the tamp is the initial substrate `P₀` — README §III's seed
read as §IV.a/§VIII's single external commitment / gauge-fixing. -/

/-- The **empty rule-set**: no rule ever fires. The applier over it is the identity,
    giving the cleanest `F`-closed step for isolating the gauge=seed fact. -/
def emptyRules : RewriteRule → Prop := fun _ => False

/-- Over the empty rule-set the applier is **deflationary** on every scope
    (`applyRules emptyRules S ≤ S`): the firing existential is over `emptyRules r`
    (`= False`), so no rule fires and the only way into `applyRules emptyRules S` is
    to be in `S` already. With `applyRules_accretive` this pins it as the identity. -/
theorem applyRules_emptyRules_le (S : Scope) : applyRules emptyRules S ≤ S := by
  intro p hp
  rcases hp with h | ⟨r, hr, _, _⟩
  · exact h
  · exact False.elim hr

/-- **At the trivial step the seeded closure equals the seed, for every seed.**
    `convergeFrom (applyRules emptyRules) S = S` — `convergeFrom_eq_self_iff` applied
    to the deflationary identity step. The clean witness that *realization is about
    the seed, not the step*: when the step does nothing, the closure **is** the
    seed-gauge. -/
theorem convergeFrom_emptyRules (S : Scope) :
    convergeFrom (applyRules emptyRules) S = S :=
  (convergeFrom_eq_self_iff (applyRules emptyRules) S).mpr (applyRules_emptyRules_le S)

/-- **(i), coincidence side: the trivial-step closure seeded by the hold-open
    gauge's lfp realizes carrier (a) exactly.** The right side `LP.flag ⊥` *is*
    carrier (a) — the undischarged-backing set, `= OrderHom.lfp (recognizeUndischarged
    LP)` by `recognizeUndischarged_lfp` / `flag_eq_lfpFlag_recognizeUndischarged`. So
    the gauge the closure realizes is the seed's: README §V's "a debt is undischarged
    iff its read-face is live in the fixed scope," recovered through the *seed*. -/
theorem closure_emptyRules_undischarged (LP : LedgerPersistence) :
    convergeFrom (applyRules emptyRules) (OrderHom.lfp (recognizeUndischarged LP))
      = LP.flag ⊥ := by
  rw [convergeFrom_emptyRules, recognizeUndischarged_lfp]
  rfl

/-- **(i), complement side: the trivial-step closure seeded by the settle gauge's lfp
    realizes the discharged-backing set** — complementary to carrier (a) on
    debt-backed faces (`seed_fork_of_injective`). Same step as
    `closure_emptyRules_undischarged`, opposite seed, opposite gauge. -/
theorem closure_emptyRules_discharged (LP : LedgerPersistence) :
    convergeFrom (applyRules emptyRules) (OrderHom.lfp (recognizeDischarged LP))
      = fun p => ∃ d, LP.holds d = p ∧ LP.Discharged d := by
  rw [convergeFrom_emptyRules, recognizeDischarged_lfp]

/-- **(ii): the seed is a lower bound on the closure, for every rule-set.** An
    instance of `le_convergeFrom`: carrier (a) (the hold-open gauge,
    `recognizeUndischarged_lfp`) is preserved into the closure of foam's *real*
    gated applier no matter the rule-set, because `applyRules` is accretive. The
    increment above it is rule-firing — ledger-blind — so it carries no gauge: all
    gauge-content is the seed's. Equality holds iff the seed is `F`-closed
    (`closure_eq_seed_iff`). -/
theorem seed_le_closure (rules : RewriteRule → Prop) (LP : LedgerPersistence) :
    OrderHom.lfp (recognizeUndischarged LP)
      ≤ convergeFrom (applyRules rules) (OrderHom.lfp (recognizeUndischarged LP)) :=
  le_convergeFrom _ _

/-- **Realization iff the seed is `F`-closed** — the applier specialization of
    `convergeFrom_eq_self_iff`. The seeded closure equals the seed exactly when no
    rule fires *out of* the seed. This is the gauge-blind fixed-point criterion that
    separates (i) (closure `=` seed-gauge) from (ii) (closure `⊋` seed-gauge); which
    side holds is a property of the rule-set, never of the gauge. -/
theorem closure_eq_seed_iff (rules : RewriteRule → Prop) (S : Scope) :
    convergeFrom (applyRules rules) S = S ↔ applyRules rules S ≤ S :=
  convergeFrom_eq_self_iff (applyRules rules) S

/-- **The seed-choice is the gauge-fork (under `holds`-injectivity).** On any
    debt-backed face the undischarged-backed seed and the discharged-backed seed are
    complementary: `lfp (recognizeDischarged LP) p ↔ ¬ lfp (recognizeUndischarged LP)
    p`. So choosing which ledger-set to seed `applyRules` with **is** the
    coincide/complement gauge-choice (7)/(8) — relocated from the step to the seed.
    The single external commitment is the choice of `P₀`. (Same cover+disjoint
    argument as `lfp_iff_not_flag_of_injective`, stated directly at the two seeds.) -/
theorem seed_fork_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (p : TapePosition) (h : ∃ d, LP.holds d = p) :
    OrderHom.lfp (recognizeDischarged LP) p ↔ ¬ OrderHom.lfp (recognizeUndischarged LP) p := by
  simp only [recognizeDischarged_lfp, recognizeUndischarged_lfp]
  obtain ⟨d, hdp⟩ := h
  constructor
  · rintro ⟨d₁, hd₁, hdis₁⟩ ⟨d₂, hd₂, hndis₂⟩
    exact hndis₂ (hinj (hd₁.trans hd₂.symm) ▸ hdis₁)
  · intro hnu
    by_cases hdis : LP.Discharged d
    · exact ⟨d, hdp, hdis⟩
    · exact absurd ⟨d, hdp, hdis⟩ hnu

/-! ## The gauge-neutral `0`-seed's closure — the all-debt-backed join (this brick)

`seed_fork_of_injective` (above) showed the undischarged- vs discharged-backed seeds are
the `±` signs of the seed-gauge. `PersistenceLfp.lean` then typed the third, distinguished
seed — the **all-debt-backed** `seedBacked LP` — and proved it the *join* of the fork
(`seedBacked_eq_join`), hence the **gauge-neutral** `0` of a `{+, −, 0}` seed-triple
(`SeedSign`). This block reads that `0`-seed's closure over foam's real gated applier.

Two facts:

* **At the trivial step the `0`-seed's closure is the join of the `±`-fork closures**
  (`closure_emptyRules_backed_eq_join`) — closure commutes with the fork-join when the
  applier is the identity, so the seed-triple's join-structure passes through unchanged.
* **For *any* rule-set the `0`-seed's closure dominates both `±`-fork closures**
  (`closure_backed_ge_undischarged` / `_discharged`, via `convergeFrom_mono_seed`): the
  gauge-neutral seed carries *both* signs through foam's real recognition, not only at the
  trivial step. And the containment is **proper** at the trivial step whenever the ledger
  carries both kinds of debt (`closure_emptyRules_backed_ne_undischarged_of_injective` /
  `_discharged`) — so the `{+, −, 0}` triple is genuinely three distinct closures there.

The remainder (next brick): the join `0 = + ⊔ −` plus the fork-disjointness `+ ⊓ − = ⊥`
(`PersistenceLfp.not_lfp_and_flag_of_injective`, under injectivity) make `{⊥, +, −, 0}` a
4-element Boolean algebra — `−` is the *local complement* of `+` within the `0`-scope, the
README §IV.a HalfType (complementation-within-a-scope) read on the seed-gauge. -/

/-- **The `0`-seed's trivial-step closure is itself** — the `seedBacked` row of
    `convergeFrom_emptyRules`, beside `closure_emptyRules_undischarged` / `_discharged`. -/
theorem closure_emptyRules_backed (LP : LedgerPersistence) :
    convergeFrom (applyRules emptyRules) (seedBacked LP) = seedBacked LP :=
  convergeFrom_emptyRules (seedBacked LP)

/-- **At the trivial step the gauge-neutral `0`-seed's closure is the join of the two
    `±`-fork closures.** Both sides are `seedBacked LP` (`convergeFrom_emptyRules` ×3 +
    `seedBacked_eq_join`): when the step is the identity, the seed-triple's `0 = + ⊔ −`
    structure rides through the closure unchanged. -/
theorem closure_emptyRules_backed_eq_join (LP : LedgerPersistence) :
    convergeFrom (applyRules emptyRules) (seedBacked LP)
      = convergeFrom (applyRules emptyRules) (OrderHom.lfp (recognizeUndischarged LP))
        ⊔ convergeFrom (applyRules emptyRules) (OrderHom.lfp (recognizeDischarged LP)) := by
  rw [convergeFrom_emptyRules, convergeFrom_emptyRules, convergeFrom_emptyRules,
    seedBacked_eq_join]

/-- **The `0`-seed's closure dominates the `+`-fork's, over any rule-set** (foam's real
    gated `F`, not only the trivial step). `+`-seed `≤` `0`-seed (`le_sup_left` through
    `seedBacked_eq_join`) and `convergeFrom` is monotone in its seed
    (`convergeFrom_mono_seed`). -/
theorem closure_backed_ge_undischarged (rules : RewriteRule → Prop) (LP : LedgerPersistence) :
    convergeFrom (applyRules rules) (OrderHom.lfp (recognizeUndischarged LP))
      ≤ convergeFrom (applyRules rules) (seedBacked LP) :=
  convergeFrom_mono_seed (applyRules rules) (by rw [seedBacked_eq_join]; exact le_sup_left)

/-- **The `0`-seed's closure dominates the `−`-fork's, over any rule-set.** Symmetric to
    `closure_backed_ge_undischarged`. So the gauge-neutral seed's closure ⊇ *both* fork
    closures: it carries both signs through foam's real recognition. -/
theorem closure_backed_ge_discharged (rules : RewriteRule → Prop) (LP : LedgerPersistence) :
    convergeFrom (applyRules rules) (OrderHom.lfp (recognizeDischarged LP))
      ≤ convergeFrom (applyRules rules) (seedBacked LP) :=
  convergeFrom_mono_seed (applyRules rules) (by rw [seedBacked_eq_join]; exact le_sup_right)

/-- **Proper containment, `+` side: the `0`-seed's trivial-step closure is *distinct* from
    the `+`-fork's** when the ledger has a discharged debt (under injectivity). With
    `closure_backed_ge_undischarged` (`⊇`), this is proper containment — the `{+, −, 0}`
    triple is three distinct closures at the trivial step. -/
theorem closure_emptyRules_backed_ne_undischarged_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (h : ∃ d, LP.Discharged d) :
    convergeFrom (applyRules emptyRules) (seedBacked LP)
      ≠ convergeFrom (applyRules emptyRules) (OrderHom.lfp (recognizeUndischarged LP)) := by
  rw [convergeFrom_emptyRules, convergeFrom_emptyRules]
  exact seedBacked_ne_undischarged_of_injective LP hinj h

/-- **Proper containment, `−` side.** Symmetric: the `0`-seed's trivial-step closure is
    distinct from the `−`-fork's when the ledger has an undischarged debt. -/
theorem closure_emptyRules_backed_ne_discharged_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (h : ∃ d, ¬ LP.Discharged d) :
    convergeFrom (applyRules emptyRules) (seedBacked LP)
      ≠ convergeFrom (applyRules emptyRules) (OrderHom.lfp (recognizeDischarged LP)) := by
  rw [convergeFrom_emptyRules, convergeFrom_emptyRules]
  exact seedBacked_ne_discharged_of_injective LP hinj h

end Foam
