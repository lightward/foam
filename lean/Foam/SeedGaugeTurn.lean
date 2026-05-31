/-
# SeedGaugeTurn — the single-external-commitment functor's *action*: the conversational turn

## What this file lands (the brick after `SeedGaugeBooleanAlgebra.lean`)

Bricks 18–19 built the functor's **source+target** and made it a **category**.
`SeedGauge = {untamped, +, −, 0}` is one 4-element type (brick 18 — `untamped = ⊥` the
basepoint/unit, `commit` the based-steps `untamped → s`), carrying its native diamond
`BooleanAlgebra` (brick 19 — `signOrderIso : SeedGauge ≃o Bool × Bool`, the native order = the
seed-image order, `seed` a **full-faithful** monotone realization into `Scope` via `seed_mono` /
`seed_le_iff`, composition = refinement `untamped ≤ plus ≤ zero`). What stayed untyped is the
functor's **action** — and the keystone (README §VIII / the bridge thread) says the
single-external-commitment functor *is a conversational turn*: one external commitment → a new foam
that retains the prior morphisms and knows one more thing (the forward pass). This file types that
turn.

## The turn = commit-then-recognize

The recognition brick 19 hands us: a turn **factors**. Pick a gauge `g : SeedGauge` — the external
commitment, brick 18's `commit` (gauge-fixing, §VII). Realize it as a seed `g.seed LP : Scope` —
brick 19's realization. Then run recognition from that seed: brick 9's **seeded closure**
`convergeFrom (applyRules rules) (g.seed LP)` — foam's gated `F` (the rewrite-rule applier) run to
its least fixed point above the seed (README §III's `lfp(F) = ⋃ Fⁿ(P₀)` with `P₀ = g.seed LP`). So

      turn LP rules g  :=  convergeFrom (applyRules rules) (g.seed LP)        -- commit, then recognize

is a map `SeedGauge → Scope`: from a commitment to the recognized foam-state it produces.

## Monotone = functorial — the functor's action, composition = refinement preserved

`turn LP rules` is the composition of two **already-landed** monotone maps: brick 19's `seed_mono`
(`g ≤ g' → g.seed ≤ g'.seed`) followed by brick 10's `convergeFrom_mono_seed`
(`S ≤ T → convergeFrom f S ≤ convergeFrom f T`). So it is **monotone** (`turn_monotone`), and we
bundle it as `turnHom LP rules : SeedGauge →o Scope`. Both `SeedGauge` (brick 19) and `Scope` (the
pointwise-implication order on `TapePosition → Prop`) are **thin categories** (posets); a monotone
map between thin categories *is a functor*. So `turnHom` is the single-external-commitment functor's
**action**, and monotonicity *is* functoriality — **composition = refinement is preserved**: brick
19's refinement-path `untamped ≤ plus ≤ zero` (`commit_zero_via_plus`) maps to
`turn untamped ≤ turn plus ≤ turn zero` (`turn_commit_zero_via_plus`), its composite the single
commitment `turn untamped ≤ turn zero` (`turn_untamped_le_zero`) by `le_trans`.

## The un-tamped input is the unit — `turn untamped = ⊥`

`turn LP rules untamped = ⊥` (`turn_untamped`): `untamped.seed = ⊥` (brick 18's `seed_untamped`),
`convergeFrom f ⊥ = lfp f` (brick 9's `convergeFrom_bot`), and `lfp (applyRules rules) = ⊥` (brick
9's `applyRules_lfp_bot` — gated recognition fires nothing from nothing). So the **un-tamped ground
recognizes to nothing**: no commitment, nothing recognized — the turn's fixed unit. Categorically
the functor **preserves the initial object** (`untamped = ⊥` in `SeedGauge` ↦ `⊥` in `Scope`,
`turn_untamped_le` the arrow from it to every turn).

## The commitment survives the action — the gauge-fork, one level out

The action does **not** collapse the gauge-distinction (the `±`/`0` fork, bricks 7–19). At the
trivial rule-set the closure is the identity (brick 9's `convergeFrom_emptyRules`), so
`turn LP emptyRules g = g.seed LP` (`turn_emptyRules`) — the turn *is* the seed, and brick 19's
full-faithful `seed_le_iff` transfers verbatim: `turn LP emptyRules` is an **order-embedding**
(`turn_emptyRules_le_iff`, under `holds`-injectivity + unresolved tension). At *any* rule-set the
seed is a **lower bound** on the turn (`seed_le_turn`, brick 9's `le_convergeFrom`): recognition only
ever adds to the committed seed, never discards it. So the seed-located tamp (brick 9 — the
commitment is the seed `P₀`) is here read **one level out, at the turn**: the turn carries the
commitment's gauge into the foam-state it produces.

## Generation and uncertainty in one act (§VII)

`turn` performs §VII's von-Neumann→Shannon fusion in a single map: `commit` (gauge-fixing — choosing
`g` among `{untamped, +, −, 0}`, where the uncertainty enters) fused with `convergeFrom` (the
recognition the commitment seeds — the generation). The geometry-only / pre-commitment state is
`untamped` (uncertainty-free, recognizing to `⊥`); committing introduces the gauge and the closure
generates the foam-state from it.

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

Pure recognition + assembly. `turn` is a composition of two previously-landed monotone maps
(`seed_mono`, `convergeFrom_mono_seed`); `turn_untamped` rewrites three landed equations
(`seed_untamped`, `convergeFrom_bot`, `applyRules_lfp_bot`); the fork-survival lemmas assemble
`convergeFrom_emptyRules` / `seed_le_iff` / `le_convergeFrom`. No new geometric content — the
recognition is that the conversational turn = the forward pass *is* this monotone `commit`-then-
recognize map, and that it preserves composition (= refinement), the initial object, and the
commitment's gauge.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeTurn` is clean, zero
sorry/warnings; depends on `SeedGauge.seed` / `seed_untamped` (SeedGaugeCommitmentLattice),
`seed_mono` / `seed_le_iff` / `untamped_le_plus` / `plus_le_zero` / `untamped_le_zero`
(SeedGaugeBooleanAlgebra), `convergeFrom` / `convergeFrom_bot` / `convergeFrom_mono_seed` /
`le_convergeFrom` (PersistenceLfp), `applyRules` / `applyRules_lfp_bot` / `emptyRules` /
`convergeFrom_emptyRules` (RecognitionApplier).)
-/

import Foam.SeedGaugeBooleanAlgebra
import Foam.RecognitionApplier

namespace Foam

/-! ## The turn — commit-then-recognize -/

/-- **The conversational turn / forward pass** — the single-external-commitment functor's action.
    A turn factors as **commit then recognize**: commit a gauge `g : SeedGauge` (brick 18, the
    external commitment / gauge-fixing), realize it as a seed `g.seed LP : Scope` (brick 19), and
    run recognition from that seed — brick 9's seeded closure `convergeFrom (applyRules rules)`
    (foam's gated `F` run to its lfp above the seed, README §III's `lfp(F) = ⋃ Fⁿ(P₀)` with
    `P₀ = g.seed LP`). The result is the new foam-state the commitment produces: it retains
    everything recognition derives from the committed seed. -/
def SeedGauge.turn (LP : LedgerPersistence) (rules : RewriteRule → Prop) : SeedGauge → Scope :=
  fun g => convergeFrom (applyRules rules) (g.seed LP)

/-! ## Monotone = functorial -/

/-- **The turn is monotone** — the composition of brick 19's `seed_mono` (`g ≤ g' → g.seed ≤ g'.seed`)
    with brick 10's `convergeFrom_mono_seed` (`S ≤ T → convergeFrom f S ≤ convergeFrom f T`). Since
    `SeedGauge` and `Scope` are both thin categories (posets), this monotone map *is a functor*
    between them — the functor's action. -/
theorem SeedGauge.turn_monotone (LP : LedgerPersistence) (rules : RewriteRule → Prop) :
    Monotone (SeedGauge.turn LP rules) := by
  intro a b hab
  show convergeFrom (applyRules rules) (a.seed LP) ≤ convergeFrom (applyRules rules) (b.seed LP)
  exact convergeFrom_mono_seed (applyRules rules) (SeedGauge.seed_mono LP hab)

/-- **The single-external-commitment functor's action, bundled** — `turnHom : SeedGauge →o Scope`.
    An `OrderHom` between two preorders *is* a functor between the corresponding thin categories;
    monotonicity *is* functoriality. This is the typed conversational turn / forward pass: a functor
    from the commitment-diamond (brick 19) into the `Scope`-lattice. -/
def SeedGauge.turnHom (LP : LedgerPersistence) (rules : RewriteRule → Prop) : SeedGauge →o Scope where
  toFun := SeedGauge.turn LP rules
  monotone' := SeedGauge.turn_monotone LP rules

/-! ## The un-tamped input is the unit — `turn untamped = ⊥` -/

/-- **The un-tamped ground recognizes to nothing** — `turn LP rules untamped = ⊥`. The basepoint
    `untamped` (`= ⊥` in `SeedGauge`, brick 18) seeds to `⊥` (`seed_untamped`); `convergeFrom f ⊥`
    is the bare lfp (`convergeFrom_bot`); and foam's gated applier's bare lfp is `⊥`
    (`applyRules_lfp_bot` — gated recognition fires nothing from nothing). So no commitment yields
    nothing recognized: the turn's fixed unit, and the functor preserving the initial object. -/
@[simp] theorem SeedGauge.turn_untamped (LP : LedgerPersistence) (rules : RewriteRule → Prop) :
    SeedGauge.turn LP rules SeedGauge.untamped = ⊥ := by
  show convergeFrom (applyRules rules) (SeedGauge.untamped.seed LP) = ⊥
  rw [seed_untamped, convergeFrom_bot, applyRules_lfp_bot]

/-- **The functor preserves the initial object** — the arrow `untamped → g` (brick 18/19) maps to
    `turn untamped ≤ turn g`. Since `turn untamped = ⊥`, this is `bot_le`: the un-tamped ground's
    recognized state (`⊥`) sits below every turn's. -/
theorem SeedGauge.turn_untamped_le (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (g : SeedGauge) :
    SeedGauge.turn LP rules SeedGauge.untamped ≤ SeedGauge.turn LP rules g := by
  rw [turn_untamped]; exact bot_le

/-! ## Composition = refinement, preserved through the action -/

/-- **The action preserves brick 19's refinement-path.** Brick 19's `commit_zero_via_plus`
    (`untamped ≤ plus ≤ zero` — *commit to `+`, then refine to hold both `0`*) maps under the functor
    to `turn untamped ≤ turn plus ≤ turn zero` (each step `turn_monotone` of a native `SeedGauge`
    arrow). Composition = refinement is carried into the recognized foam-states. -/
theorem SeedGauge.turn_commit_zero_via_plus (LP : LedgerPersistence) (rules : RewriteRule → Prop) :
    SeedGauge.turn LP rules SeedGauge.untamped ≤ SeedGauge.turn LP rules SeedGauge.plus ∧
      SeedGauge.turn LP rules SeedGauge.plus ≤ SeedGauge.turn LP rules SeedGauge.zero :=
  ⟨SeedGauge.turn_monotone LP rules SeedGauge.untamped_le_plus,
   SeedGauge.turn_monotone LP rules SeedGauge.plus_le_zero⟩

/-- **The composite refinement is the direct commitment** — `turn untamped ≤ turn zero`, the functor
    image of brick 19's `untamped_le_zero` (`= le_trans untamped_le_plus plus_le_zero`). The
    composite of *commit `+`, then refine to `0`* is the single commitment *commit `0`*, carried
    through the turn. -/
theorem SeedGauge.turn_untamped_le_zero (LP : LedgerPersistence) (rules : RewriteRule → Prop) :
    SeedGauge.turn LP rules SeedGauge.untamped ≤ SeedGauge.turn LP rules SeedGauge.zero :=
  SeedGauge.turn_monotone LP rules SeedGauge.untamped_le_zero

/-! ## The commitment survives the action — the gauge-fork, one level out -/

/-- **At the trivial step the turn IS the seed** — `turn LP emptyRules g = g.seed LP`. Over the empty
    rule-set the seeded closure is the identity (brick 9's `convergeFrom_emptyRules`), so the turn
    recognizes nothing beyond the committed seed. The clean witness that the action's gauge-content
    is the seed's. -/
theorem SeedGauge.turn_emptyRules (LP : LedgerPersistence) (g : SeedGauge) :
    SeedGauge.turn LP emptyRules g = g.seed LP := by
  show convergeFrom (applyRules emptyRules) (g.seed LP) = g.seed LP
  exact convergeFrom_emptyRules (g.seed LP)

/-- **At the trivial step the action is an order-embedding** — `turn LP emptyRules a ≤
    turn LP emptyRules b ↔ a ≤ b` (under `holds`-injectivity + unresolved tension `BothDebtKinds`).
    Brick 19's full-faithful `seed_le_iff` transferred verbatim through `turn_emptyRules`: the turn
    **does not collapse the gauge-distinction** — the whole commitment-diamond embeds into the
    recognized foam-states. -/
theorem SeedGauge.turn_emptyRules_le_iff (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hboth : LP.BothDebtKinds) (a b : SeedGauge) :
    SeedGauge.turn LP emptyRules a ≤ SeedGauge.turn LP emptyRules b ↔ a ≤ b := by
  simp only [SeedGauge.turn_emptyRules]
  exact SeedGauge.seed_le_iff LP hinj hboth a b

/-- **The committed seed is a lower bound on the turn, for every rule-set** — `g.seed LP ≤
    turn LP rules g` (brick 9's `le_convergeFrom`). Recognition only ever *adds* to the committed
    seed; it never discards it. So the seed-located tamp (brick 9) is carried one level out, into the
    turn: whatever gauge the commitment fixes survives — as a lower bound — into the foam-state. -/
theorem SeedGauge.seed_le_turn (LP : LedgerPersistence) (rules : RewriteRule → Prop) (g : SeedGauge) :
    g.seed LP ≤ SeedGauge.turn LP rules g := by
  show g.seed LP ≤ convergeFrom (applyRules rules) (g.seed LP)
  exact le_convergeFrom (applyRules rules) (g.seed LP)

end Foam
