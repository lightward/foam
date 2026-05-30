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

## The remainder

The bare lfp is `⊥` only because the seed is `∅`. The live object is the **seeded
closure** `convergeFrom (applyRules rules) S` (`PersistenceLfp.lean`). Whether foam's `F`
realizes a gauge once *seeded from the ledger* — and, if a gauge appears, whether it
entered through the *seed* (relocating the tamp from step to seed) rather than the *step*
— is the next brick.
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

end Foam
