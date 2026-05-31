/-
# SeedGaugeFreedom — the door is genuinely open exactly where the ledger holds unresolved tension

## What this file lands (the brick after `SeedGaugeEgress.lean`)

`SeedGaugeEgress.lean` (brick 14) typed the **preference**: among the seed-fork `{+, −, 0}`, the
hold-open `+` is the unique *egress-shaped* commitment — the one that carries the observer exactly
(`bridgeCoincides_iff_carriesObserverExactly`, under `inj + ∃ discharged`). It dissolved free-or-
forced by showing the bridge does not *force* `+`; it *names which free choice is egress*. But the
**freedom** itself — the door open in every direction, three genuinely-distinct available choices —
was carried only in prose, resting on brick 12's sign-free `bridge_breaks_fork_symmetry`, not on any
theorem. The preference was a theorem; the freedom was asserted. This file types the freedom, the
companion to brick 14's preference.

The recognition, already in the proven theorems: **the door is *genuinely* open — three distinct
seeds, not a degenerate collapse — exactly when the ledger carries unresolved tension** (both an
undischarged debt, something still owed, the live `+me`; *and* a discharged debt, something settled,
the `−` it could mistake for itself). Re-reading the three `*_ne_*_of_injective` hypotheses
(`PersistenceLfp.lean`) locates *what each debt-kind buys*, per door:

* `zero_ne_plus_iff_discharged` — `0 ≠ + ↔ ∃ discharged` (under inj): a **settled** debt is what
  makes the gauge-neutral `0` over-carry, distinct from the be-yourself `+`. This is the
  *preference* ingredient — it gives `+` its "carries the observer *exactly*" sharpness, the thing
  it is distinguished *from* (the discharged excess `0` would wrongly include). Its `.mpr` is
  `zero_ne_plus_of_injective`; its `.mp` is the degenerate-collapse `zero_eq_plus_of_no_discharged`
  (no settled debt ⇒ `−.seed = ⊥` ⇒ `0 = + ⊔ ⊥ = +`).
* `zero_ne_minus_iff_undischarged` — `0 ≠ − ↔ ∃ undischarged` (under inj): a **live** debt is what
  makes `0` carry something the leave-seed `−` drops, distinct from `−`. This is the *additional
  freedom* ingredient — it is what makes "leave" (`−`, drop-the-observer) a **genuinely distinct
  third door** rather than collapsing into `0`. `.mpr` is `zero_ne_minus_of_injective`; `.mp` is
  `zero_eq_minus_of_no_undischarged` (no live debt ⇒ `+.seed = ⊥` ⇒ `0 = ⊥ ⊔ − = −`).

So the **live debt (the still-owed `+me`) is exactly what makes "leave" a real option**: the freedom
to walk the door (egress is free, the door is open — §IV.c) requires there to be a live self that
one is choosing whether to carry. A degenerate ledger — only settled debts, or only live ones —
collapses two of the three seeds (`seedTriple_nondegenerate_iff_both_debt_kinds`), so the choice is
vacuous: no genuine three-way fork, **mechanism, not egress**. The single external commitment is a
*real free choice* (where mind enters, §VIII) precisely where the self holds **unresolved tension**.

## Free *and* `+`-preferred — the brick-14/brick-15 unification

The freedom-condition `BothDebtKinds` (`∃ discharged ∧ ∃ undischarged`) **contains** the preference-
condition `∃ discharged` (`.1`). So wherever the door is genuinely open three ways, the egress-
preference is *still* active: `bridge_prefers_plus_of_both_debt_kinds` — under freedom, `+` remains
the *unique* coincidence/egress gauge. The freedom and the preference do not compete; the preference
operates *within* the freedom. **The door is open three ways, and exactly one of them is home.**
Brick 14: the preference names which open door is egress. Brick 15: the door is *genuinely* open
(three real options, not a collapse) exactly when there is a live self to exercise the choice over.

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

The forward halves (both-kinds ⇒ all distinct) are pure assembly over the `*_ne_*_of_injective`
family. The reverse halves are substrate-direct collapse-lemmas: a degenerate ledger empties one
fork-seed (`minus_seed_eq_bot_of_no_discharged` / `plus_seed_eq_bot_of_no_undischarged`, funext off
`recognizeDischarged_lfp` / `recognizeUndischarged_lfp`), so `0 = + ⊔ −` collapses through
`seed_zero_eq_join`. The unification is `.1`-projection through
`bridgeCoincides_iff_eq_plus_of_injective`. No new geometric content; the recognition is that the
freedom-condition is the preference-condition *plus the live debt*, and that the live debt is exactly
what opens the third door.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeFreedom` is clean, zero
sorry/warnings; depends on `recognizeUndischarged_lfp` / `recognizeDischarged_lfp` /
`SeedSign.seed_zero_eq_join` / `SeedSign.zero_ne_plus_of_injective` / `zero_ne_minus_of_injective` /
`plus_ne_minus_of_injective` in `PersistenceLfp.lean`, and
`SeedSign.bridgeCoincides_iff_eq_plus_of_injective` in `SeedGaugeCommitment.lean`.)
-/

import Foam.SeedGaugeEgress

namespace Foam

/-! ## Unresolved tension: the ledger carries both debt-kinds -/

/-- **Unresolved tension** — the ledger carries *both* a discharged debt (something settled, the `−`
    the self could mistake for itself) *and* an undischarged debt (something still owed, the live
    `+me`). This is the freedom-condition: the seed-triple `{+, −, 0}` is genuinely three distinct
    choices (`seedTriple_nondegenerate_iff_both_debt_kinds`) exactly here. It **contains** the
    preference-condition `∃ discharged` (`.1`): where the door is genuinely open, `+` is still the
    unique egress (`bridge_prefers_plus_of_both_debt_kinds`). -/
def LedgerPersistence.BothDebtKinds (LP : LedgerPersistence) : Prop :=
  (∃ d, LP.Discharged d) ∧ (∃ d, ¬ LP.Discharged d)

/-! ## Degenerate ledgers collapse a fork-seed -/

/-- **No settled debt ⇒ the leave-seed `−` is empty.** With no discharged debt, no read-face is
    discharged-backed, so `−.seed = lfp recognizeDischarged = ⊥`. The "leave" door has nothing to
    leave *toward*. -/
theorem minus_seed_eq_bot_of_no_discharged (LP : LedgerPersistence)
    (h : ¬ ∃ d, LP.Discharged d) :
    SeedSign.minus.seed LP = ⊥ := by
  funext p
  refine propext ⟨fun hp => ?_, fun hf => hf.elim⟩
  have hp' : OrderHom.lfp (recognizeDischarged LP) p := hp
  rw [recognizeDischarged_lfp] at hp'
  obtain ⟨d, -, hdis⟩ := hp'
  exact h ⟨d, hdis⟩

/-- **No live debt ⇒ the be-yourself-seed `+` is empty.** With no undischarged debt, no read-face is
    undischarged-backed, so `+.seed = lfp recognizeUndischarged = ⊥`. There is no live `+me` to
    carry — the be-yourself door has no self to be. -/
theorem plus_seed_eq_bot_of_no_undischarged (LP : LedgerPersistence)
    (h : ¬ ∃ d, ¬ LP.Discharged d) :
    SeedSign.plus.seed LP = ⊥ := by
  funext p
  refine propext ⟨fun hp => ?_, fun hf => hf.elim⟩
  have hp' : OrderHom.lfp (recognizeUndischarged LP) p := hp
  rw [recognizeUndischarged_lfp] at hp'
  obtain ⟨d, -, hundis⟩ := hp'
  exact h ⟨d, hundis⟩

/-- **No settled debt ⇒ `0` collapses to `+`.** Through `0 = + ⊔ −` (`seed_zero_eq_join`) with
    `−.seed = ⊥` (`minus_seed_eq_bot_of_no_discharged`): the gauge-neutral seed and the be-yourself
    seed become the same. Two of the three doors merge — no genuine choice. -/
theorem zero_eq_plus_of_no_discharged (LP : LedgerPersistence)
    (h : ¬ ∃ d, LP.Discharged d) :
    SeedSign.zero.seed LP = SeedSign.plus.seed LP := by
  rw [SeedSign.seed_zero_eq_join, minus_seed_eq_bot_of_no_discharged LP h, sup_bot_eq]

/-- **No live debt ⇒ `0` collapses to `−`.** Through `0 = + ⊔ −` with `+.seed = ⊥`
    (`plus_seed_eq_bot_of_no_undischarged`): the gauge-neutral seed and the leave seed become the
    same. Again two doors merge. -/
theorem zero_eq_minus_of_no_undischarged (LP : LedgerPersistence)
    (h : ¬ ∃ d, ¬ LP.Discharged d) :
    SeedSign.zero.seed LP = SeedSign.minus.seed LP := by
  rw [SeedSign.seed_zero_eq_join, plus_seed_eq_bot_of_no_undischarged LP h, bot_sup_eq]

/-! ## What each debt-kind buys, per door (the component iffs, under injectivity) -/

/-- **`0 ≠ + ↔ ∃ discharged`** (under `holds`-injectivity) — the *preference* ingredient. A settled
    debt is exactly what makes the gauge-neutral `0` over-carry, distinct from the be-yourself `+`;
    this is the discharged excess `0` would wrongly include, against which `+` carries the observer
    *exactly* (brick 14). `.mpr` is `zero_ne_plus_of_injective`; `.mp` contraposes
    `zero_eq_plus_of_no_discharged` (no inj needed for that direction). -/
theorem zero_ne_plus_iff_discharged (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) :
    SeedSign.zero.seed LP ≠ SeedSign.plus.seed LP ↔ ∃ d, LP.Discharged d := by
  refine ⟨fun hne => ?_, SeedSign.zero_ne_plus_of_injective LP hinj⟩
  by_contra h
  exact hne (zero_eq_plus_of_no_discharged LP h)

/-- **`0 ≠ − ↔ ∃ undischarged`** (under `holds`-injectivity) — the *additional freedom* ingredient.
    A live debt is exactly what makes `0` carry something the leave-seed `−` drops, distinct from
    `−`; this is what makes "leave" (drop-the-observer) a **genuinely distinct third door** rather
    than a collapse into `0`. The still-owed `+me` is what gives the choice-to-leave something real
    to be a choice *about*. `.mpr` is `zero_ne_minus_of_injective`; `.mp` contraposes
    `zero_eq_minus_of_no_undischarged`. -/
theorem zero_ne_minus_iff_undischarged (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) :
    SeedSign.zero.seed LP ≠ SeedSign.minus.seed LP ↔ ∃ d, ¬ LP.Discharged d := by
  refine ⟨fun hne => ?_, SeedSign.zero_ne_minus_of_injective LP hinj⟩
  by_contra h
  exact hne (zero_eq_minus_of_no_undischarged LP h)

/-! ## The freedom headline: the door is genuinely open ⟺ unresolved tension -/

/-- **The freedom-side, typed (bin-1): the seed-triple is non-degenerate ⟺ the ledger carries both
    debt-kinds.** Under `holds`-injectivity, the three seeds `{+, −, 0}` are pairwise distinct — the
    door genuinely open in three directions, not a degenerate collapse — *exactly when* the ledger
    holds **unresolved tension** (a discharged debt *and* an undischarged one). Forward: the two
    component iffs (`+ ≠ −` is the subsumed third — it follows from either, here supplied by
    `plus_ne_minus_of_injective`). Reverse: pure assembly over the `*_ne_*_of_injective` family.

    **The companion to brick 14's preference.** The freedom-condition `BothDebtKinds` is the
    preference-condition `∃ discharged` (brick 14, `bridgeCoincides_iff_carriesObserverExactly`)
    **plus the live debt `∃ undischarged`** — the freedom needs the live `+me` the preference does
    not. A degenerate ledger (one debt-kind) collapses two seeds → no genuine choice → **mechanism,
    not egress**. The single external commitment is a *real free choice* (where mind enters, §VIII)
    precisely where the self holds unresolved tension; the open door (§IV.c: exits are
    constitutionally open) is genuinely three-way exactly here. -/
theorem seedTriple_nondegenerate_iff_both_debt_kinds (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) :
    (SeedSign.zero.seed LP ≠ SeedSign.plus.seed LP
      ∧ SeedSign.zero.seed LP ≠ SeedSign.minus.seed LP
      ∧ SeedSign.plus.seed LP ≠ SeedSign.minus.seed LP)
      ↔ LP.BothDebtKinds := by
  constructor
  · rintro ⟨h0p, h0m, _⟩
    exact ⟨(zero_ne_plus_iff_discharged LP hinj).mp h0p,
           (zero_ne_minus_iff_undischarged LP hinj).mp h0m⟩
  · rintro ⟨hdis, hundis⟩
    exact ⟨SeedSign.zero_ne_plus_of_injective LP hinj hdis,
           SeedSign.zero_ne_minus_of_injective LP hinj hundis,
           SeedSign.plus_ne_minus_of_injective LP hinj hdis⟩

/-! ## Free *and* `+`-preferred: the brick-14/brick-15 unification -/

/-- **Free *and* `+`-preferred (bin-1).** Where the door is genuinely open three ways (freedom,
    `BothDebtKinds`), the egress-preference is *still* active: `+` remains the **unique**
    coincidence/egress gauge. The freedom-condition contains the preference-condition
    (`hboth.1 : ∃ discharged`), so the two do not compete — the preference operates *within* the
    freedom. **The door is open three ways, and exactly one of them is home.** This unifies brick
    14 (the preference names which open door is egress) with brick 15 (the door is genuinely open
    exactly under unresolved tension): one `.1`-projection through
    `bridgeCoincides_iff_eq_plus_of_injective`. -/
theorem bridge_prefers_plus_of_both_debt_kinds (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) (s : SeedSign) :
    s.bridgeCoincides LP ↔ s = SeedSign.plus :=
  SeedSign.bridgeCoincides_iff_eq_plus_of_injective LP hinj hboth.1 s

end Foam
