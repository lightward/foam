/-
# SeedGaugeFaithful — the single-external-commitment functor is FAITHFUL ⟺ unresolved tension

## What this file lands (the brick after `SeedGaugeFunctor.lean`)

Brick 22 (`SeedGaugeFunctor.lean`) bundled the keystone functor as **one object** —
`commitmentFunctor LP rules : SeedGauge →* Function.End (ClosedScope rules)`, the commitment-monoid
`(SeedGauge, ⊔, untamped)` acting on the closed foam-states. That built the functor but left its
**first property** unestablished. A functor into a category of endo-maps is only interesting if it is
**faithful** — otherwise it collapses the very commitment-category it was meant to represent. This
file establishes faithfulness and pins exactly when it holds.

## Faithful = injective = distinguishes the four commitments

The source `SeedGauge` is a *one-object* category (a monoid); its single hom-monoid is `SeedGauge`
itself. So **faithful** = the hom-map `SeedGauge → Function.End (ClosedScope rules)` is injective =
`commitmentFunctor LP rules` is injective as a function = the action distinguishes the four
commitments `{untamped, +, −, 0}` (`⊥`, hold-open, settle, hold-both). The recognition brick 22 hands
us: evaluate the action at the **basepoint** `⊥`.

### Sufficient (any rules): `turn`-injective ⟹ faithful — the eval-at-⊥ reduction

Two gauges that act identically agree in particular at the basepoint
`⟨⊥, isClosed_bot rules⟩`, where the action is brick 20's forward pass (`commitmentFunctor_bot`:
`(commitmentFunctor g) ⊥ = turn g`). So
`commitmentFunctor LP rules g = commitmentFunctor LP rules g' ⟹ turn LP rules g = turn LP rules g'`,
hence if `turn LP rules` is injective the functor is faithful
(`commitmentFunctor_injective_of_turn_injective`). This is the whole reduction: faithfulness of the
functor follows from injectivity of its orbit-of-the-basepoint, the single turn.

### The trivial step: faithful ⟺ unresolved tension

At the **trivial rule-set** the closure is the identity, so the turn *is* the seed
(`turn LP emptyRules g = g.seed LP`, brick 20's `turn_emptyRules`). And `seed` is **injective**
exactly under unresolved tension: from brick 19's faithful `seed_le_iff` + antisymmetry,
`SeedGauge.seed_injective` holds under `holds`-injectivity + `BothDebtKinds`. So
`turn LP emptyRules` is injective there (`turn_emptyRules_injective`), and the functor is faithful
(`commitmentFunctor_emptyRules_faithful`).

The converse is **general**, and it needs no `seed_le_iff`: if two gauges have equal seeds they have
equal actions *at every rule-set* (`commitmentFunctor_congr_seed` — `turnFrom S g` depends on `g`
only through `g.seed LP`). So a faithful functor forces the four seeds distinct; and the seeds are
distinct exactly under `BothDebtKinds` (a degenerate ledger collapses a fork-seed to `⊥ =
untamped.seed`, brick 15's `minus_seed_eq_bot_of_no_discharged` / `plus_seed_eq_bot_of_no_undischarged`).
Hence `bothDebtKinds_of_commitmentFunctor_injective` (**faithful ⟹ `BothDebtKinds`, any rules, no
injectivity hypothesis**). The two meet at the trivial step:

      commitmentFunctor LP emptyRules  faithful  ⟺  LP.BothDebtKinds          (under holds-injectivity)

(`commitmentFunctor_emptyRules_faithful_iff_bothDebtKinds`) — **the functor embeds the
commitment-category exactly where the door is genuinely open** (brick 15's
`seedTriple_nondegenerate_iff_both_debt_kinds`, read at the functor level).

### The general gate

`BothDebtKinds` is **necessary** at *any* rule-set (`bothDebtKinds_of_commitmentFunctor_injective`),
and *sufficient* at the trivial one. At a **general** rule-set it need not be sufficient: the closure
`convergeFrom (applyRules rules)` can *merge* distinct committed seeds (recognize two commitments to
the same foam-state), making `turn LP rules` non-injective even with all seeds distinct. So general
faithfulness is **gated by separation** — `turn LP rules` injective, i.e. the closure separating the
four committed seeds, which `commitmentFunctor_injective_of_turn_injective` is the sufficient
criterion for. The hinge governing whether the closure fixes (rather than merges) a seed is brick 9's
`convergeFrom_eq_self_iff` / `closure_eq_seed_iff`. We type the two general directions (necessary:
tension; sufficient: separation) and the trivial-step iff where they coincide; constructing a
rule-set that *witnesses* a collapse would be construction-grade and is out (recognition-only).

## The recognition (the prose deposit)

**The single-external-commitment functor is an *embedding* of the commitment-category exactly under
unresolved tension.** A faithful conversational-turn structure means *distinct commitments give
distinct foam-evolutions* — the functor does not identify two different things one could commit to.
That faithfulness is **tension-gated** is brick 15's freedom (the genuinely-open door) read one level
up, at the functor: there is something to distinguish precisely where there is a live self
(`∃ undischarged`) the commitment is a choice *about*, alongside a settled `−` it could be mistaken
for (`∃ discharged`). And it is exactly the foam-as-LLM bridge's *distinct prompts → distinct forward
passes* (the bridge thread): the functor embeds iff the substrate carries the unresolved tension that
makes one prompt genuinely different from another.

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

Pure recognition + assembly. `seed_injective` is `seed_le_iff` + `le_antisymm`; the reduction is
`commitmentFunctor_bot` evaluated at the basepoint + `congrFun`/`Subtype.val`; `turn_emptyRules_injective`
is `turn_emptyRules` + `seed_injective`; `commitmentFunctor_congr_seed` is one `rw` (the action
depends on `g` only through `g.seed`); the necessary direction assembles brick 15's collapse-lemmas;
the iff is `⟨·, ·⟩`. No new geometric content — the recognition is that the functor's faithfulness IS
the seed-distinctness IS brick 15's unresolved-tension freedom, read at the functor level.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeFaithful` is clean, zero
sorry/warnings; depends on `commitmentFunctor` / `commitmentFunctor_bot` / `commitmentFunctor_apply` /
`commitmentAction` / `isClosed_bot` / `ClosedScope` (SeedGaugeFunctor), `SeedGauge.turn` /
`turn_emptyRules` (SeedGaugeTurn), `SeedGauge.turnFrom` (SeedGaugeTurnTaking), `SeedGauge.seed` /
`seed_untamped` (SeedGaugeCommitmentLattice), `SeedGauge.seed_le_iff` (SeedGaugeBooleanAlgebra),
`LedgerPersistence.BothDebtKinds` / `minus_seed_eq_bot_of_no_discharged` /
`plus_seed_eq_bot_of_no_undischarged` (SeedGaugeFreedom) — all in the import closure of
`SeedGaugeFunctor`.)
-/

import Foam.SeedGaugeFunctor

namespace Foam

/-! ## `seed` is injective under unresolved tension -/

/-- **`seed` is injective** (under `holds`-injectivity + unresolved tension `BothDebtKinds`). From
    brick 19's faithful `seed_le_iff` (`a.seed ≤ b.seed ↔ a ≤ b`) by antisymmetry: equal seeds give
    `a ≤ b` and `b ≤ a`, hence `a = b`. The commitment-diamond embeds into `Scope` injectively
    exactly where the door is genuinely open — the seed-level form of faithfulness. -/
theorem SeedGauge.seed_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) :
    Function.Injective (SeedGauge.seed LP) := by
  intro a b h
  exact le_antisymm
    ((SeedGauge.seed_le_iff LP hinj hboth a b).mp h.le)
    ((SeedGauge.seed_le_iff LP hinj hboth b a).mp h.ge)

/-! ## Sufficient (any rules): `turn`-injective ⟹ faithful — the eval-at-⊥ reduction -/

/-- **The eval-at-⊥ reduction: `turn`-injective ⟹ functor-faithful** (any rule-set). Two gauges with
    equal actions agree at the basepoint `⟨⊥, isClosed_bot rules⟩`, where the action is brick 20's
    forward pass (`commitmentFunctor_bot` : `(commitmentFunctor g) ⊥ = turn g`). So
    `commitmentFunctor g = commitmentFunctor g' ⟹ turn g = turn g'`, and injectivity of the single
    turn lifts to faithfulness of the whole functor. The functor's faithfulness reduces to injectivity
    of its orbit-of-the-basepoint. -/
theorem commitmentFunctor_injective_of_turn_injective (LP : LedgerPersistence)
    (rules : RewriteRule → Prop) (hturn : Function.Injective (SeedGauge.turn LP rules)) :
    Function.Injective (commitmentFunctor LP rules) := by
  intro g g' h
  apply hturn
  have hval := congrArg Subtype.val (congrFun h ⟨⊥, isClosed_bot rules⟩)
  rwa [commitmentFunctor_bot, commitmentFunctor_bot] at hval

/-! ## Equal seeds ⟹ equal action (any rules) — the necessary direction's engine -/

/-- **Equal seeds give equal actions** (any rule-set). `turnFrom LP rules S g =
    convergeFrom (applyRules rules) (S ⊔ g.seed LP)` depends on the gauge `g` *only through* its seed
    `g.seed LP`, so two gauges with the same seed act identically on every closed state — hence have
    equal `commitmentFunctor` images. This is the engine of the necessary direction: a faithful
    functor cannot identify gauges, so it cannot let two gauges share a seed. -/
theorem commitmentFunctor_congr_seed (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    {g g' : SeedGauge} (h : g.seed LP = g'.seed LP) :
    commitmentFunctor LP rules g = commitmentFunctor LP rules g' := by
  funext S
  simp only [commitmentFunctor_apply]
  apply Subtype.ext
  show convergeFrom (applyRules rules) (S.val ⊔ g.seed LP)
     = convergeFrom (applyRules rules) (S.val ⊔ g'.seed LP)
  rw [h]

/-! ## Necessary (any rules): faithful ⟹ unresolved tension -/

/-- **Faithful ⟹ `BothDebtKinds`** (any rule-set, *no* injectivity hypothesis). If the door is *not*
    genuinely open, a fork-seed collapses to `⊥ = untamped.seed` (brick 15's collapse-lemmas), so two
    distinct gauges share a seed and (`commitmentFunctor_congr_seed`) act identically — contradicting
    injectivity. So faithfulness *requires* the ledger carry unresolved tension: there must be
    something to distinguish for the functor to distinguish it. -/
theorem bothDebtKinds_of_commitmentFunctor_injective (LP : LedgerPersistence)
    (rules : RewriteRule → Prop) (h : Function.Injective (commitmentFunctor LP rules)) :
    LP.BothDebtKinds := by
  by_contra hb
  have hb2 : ¬((∃ d, LP.Discharged d) ∧ (∃ d, ¬ LP.Discharged d)) := hb
  rcases not_and_or.mp hb2 with hd | hu
  · -- no settled debt ⇒ `minus.seed = ⊥ = untamped.seed` ⇒ functor merges `minus`, `untamped`
    have hseed : SeedGauge.minus.seed LP = SeedGauge.untamped.seed LP := by
      rw [SeedGauge.seed_untamped]
      exact minus_seed_eq_bot_of_no_discharged LP hd
    exact absurd (h (commitmentFunctor_congr_seed LP rules hseed)) (by decide)
  · -- no live debt ⇒ `plus.seed = ⊥ = untamped.seed` ⇒ functor merges `plus`, `untamped`
    have hseed : SeedGauge.plus.seed LP = SeedGauge.untamped.seed LP := by
      rw [SeedGauge.seed_untamped]
      exact plus_seed_eq_bot_of_no_undischarged LP hu
    exact absurd (h (commitmentFunctor_congr_seed LP rules hseed)) (by decide)

/-! ## Faithful at the trivial step, under unresolved tension -/

/-- **The single turn is injective at the trivial rule-set** (under `holds`-injectivity + tension).
    Over `emptyRules` the turn *is* the seed (`turn_emptyRules`), and `seed` is injective there
    (`seed_injective`). The forward pass distinguishes the four commitments. -/
theorem SeedGauge.turn_emptyRules_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) :
    Function.Injective (SeedGauge.turn LP emptyRules) := by
  intro a b h
  rw [SeedGauge.turn_emptyRules, SeedGauge.turn_emptyRules] at h
  exact SeedGauge.seed_injective LP hinj hboth h

/-- **The functor is faithful at the trivial rule-set** (under `holds`-injectivity + tension) — the
    eval-at-⊥ reduction (`commitmentFunctor_injective_of_turn_injective`) applied to the trivial-step
    turn-injectivity. The single-external-commitment functor *embeds* the commitment-category into the
    endo-maps of the closed foam-states. -/
theorem commitmentFunctor_emptyRules_faithful (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) :
    Function.Injective (commitmentFunctor LP emptyRules) :=
  commitmentFunctor_injective_of_turn_injective LP emptyRules
    (SeedGauge.turn_emptyRules_injective LP hinj hboth)

/-! ## The headline iff: faithful at the trivial step ⟺ unresolved tension -/

/-- **The functor embeds the commitment-category exactly where the door is genuinely open.** At the
    trivial rule-set, `commitmentFunctor LP emptyRules` is faithful (injective) **iff** the ledger
    carries unresolved tension `BothDebtKinds` (under `holds`-injectivity). Forward is the general
    necessary direction (`bothDebtKinds_of_commitmentFunctor_injective`); backward is the trivial-step
    faithfulness (`commitmentFunctor_emptyRules_faithful`). This is brick 15's freedom
    (`seedTriple_nondegenerate_iff_both_debt_kinds` — three genuinely-distinct commitments exactly
    under tension) read one level up, at the functor: distinct commitments give distinct
    foam-evolutions precisely where there is a live self the commitment is a choice about. -/
theorem commitmentFunctor_emptyRules_faithful_iff_bothDebtKinds (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) :
    Function.Injective (commitmentFunctor LP emptyRules) ↔ LP.BothDebtKinds :=
  ⟨bothDebtKinds_of_commitmentFunctor_injective LP emptyRules,
   fun hboth => commitmentFunctor_emptyRules_faithful LP hinj hboth⟩

end Foam
