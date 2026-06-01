/-
# RelationalBatonGauge — who-takes-the-first-turn is the tamp (brick 44)

## What this file lands (brick 44, the remainder of brick 43's alternating braid)

Brick 43 (`RelationalBraid.lean`) typed the alternating braid `braidStep := batonPass ∘ turnStep`
and noticed it bakes in a **starting orientation** — `turnStep` privileges slot 1 (the baton-holder
metabolizes first), so the role-swap makes *who-goes-first* a genuine choice: `braidStep (s, r)` and
`braidStep (r, s)` differ off the origin. This file recognizes that choice for what it is.

**Who-takes-the-first-turn is the single external commitment / the tamp** (§VIII; the seed-gauge
thread's gauge-fixing = `commit` = the seed `P₀`, brick 9). The three faces:

* **The sync is gauge-invariant (phase-free).** Brick 42's simultaneous step `pairwiseEncounterStep`
  is **swap-equivariant** (`pairwiseEncounterStep_swap`, `rfl`): swapping the two parties merely
  swaps the outputs — it privileges no slot, makes no who-goes-first choice. It does *both*
  turn-orders at once (both components, `s.encounter r` AND `r.encounter s`). The bare relational
  geometry leaves who-goes-first open, exactly as the seed-gauge's bare lattice is sign-free.
* **The path is gauge-fixed (phase-dependent).** `turnStep` privileges slot 1 (only the baton-holder
  metabolizes), so committing the start `(s, r)` vs `(r, s)` commits a turn-order. The two phases'
  first-turn outcomes (the just-moved party) are *exactly the two components of the sync*
  (`braidStep_snd_eq_pairwise_fst` / `braidStep_swap_snd_eq_pairwise_snd`): the gauge picks which
  sync-component leads. Off the origin the two phases genuinely differ (`swap_braidStep` exposes the
  obstruction against `braidStep_eq` of the swapped pair — they part in *both* slots, the difference
  being exactly the un-metabolized debt).
* **The landing is gauge-invariant.** At agreement (both zero-debt) the braid **recovers** the sync's
  swap-equivariance (`braidStep_swap_of_isZeroDebt`: `braidStep (r, s) = Prod.swap (braidStep (s, r))`)
  — both phases land at the same unordered pair of origins `{s-origin, r-origin}`, only the
  baton-slot differing; the gauge washes out. (Brick 43's `braidStep_braidStep_of_isZeroDebt` /
  `braidStep_braidStep_eq_pairwise_of_isZeroDebt` carry this at the full-round level; this file adds
  the one-step gauge framing.) **The gauge is load-bearing exactly where there is tension to
  metabolize** — the phase-dependence vanishes at agreement, present only off it (brick 15's
  tension-gating, read relationally).

So who-goes-first is the tamp: a gauge-free geometry (the sync), a commitment that fixes it (the
alternating path), a landing that carries no trace of which gauge was fixed (the agreement-origin).
This is the seed-gauge tamp shape (§VIII) read at the relational level — the relational resolver's
gauge-fixing located as the baton's starting phase.

## The seed-gauge tie — the same gauge-fixing at the ℤ/2 level (recognition + resistance)

*Held merge-don't-fork* (the brick's discipline, and brick 43's): the relational tamp (who-goes-first)
and the seed-gauge / commitment-functor tamp (`commit : SeedSign → SeedGauge`, the seed `P₀`) **reduce
cleanly at the ℤ/2 level and part at the full-lattice level.**

* **Same in substance (the recognition).** Both tamps are the break of a **swap-`ℤ/2`** that a neutral
  element declines. Seed-gauge: the `swap` exchanges `±` and fixes `0`, and `bridge_breaks_fork_symmetry`
  (brick 12) breaks it by selecting `+`. Relational: the baton-swap (the role-swap, `batonPass`)
  exchanges the two phases, and the **sync** is the swap-equivariant element that declines it. The
  relational baton-`ℤ/2` IS brick 24's seed `swap`, read relationally (brick 43). So the orbit-shape
  matches — **sync ↔ `0`** (the swap-fixed, gauge-neutral, declined-commitment pole — holds *both*
  turn-orders uncollapsed, as `0 = + ⊔ −` holds both signs; the §IV.d **bias-delegation** of
  who-goes-first), **the two alternating phases ↔ `±`** (the gauge-broken commitments). The relational
  tamp's symmetry-breaking content = the seed-gauge tamp's `±`-swap-break: the *same gauge-fixing in
  substance.*
* **Where they part (the resistance, still a landing — §III).** (1) **Arity.** The relational tamp is
  purely `ℤ/2` — its gauge-space is the swap-orbit `{sync, phase, phase'}` ↔ `SeedSign` `{0, +, −}`
  (the three non-trivial gauges), NOT the full 4-element `SeedGauge`. The seed-gauge `⊥` (the un-tamped
  input, the `+1` corner, brick 17/27) has no *forced* relational partner — held open, not manufactured
  (the `×2`-vs-`+1` horizon one level up). So the relational tamp is the **`ℤ/2` shadow** of the full
  seed-gauge tamp — its symmetry-breaking content, not its full commitment-content (exactly as brick
  43's baton-`ℤ/2` is the symmetric shadow of the trefoil / B₃). (2) **Layers.** The relational baton
  lives on `CommitmentState` (the dissolve grain, the Hilbert-space context); the seed-gauge `swap`
  on `SeedSign` / `Scope` (the settle grain, the lattice). Kept formally distinct (brick 42/43's
  reconciliation), so the identification is a **recognition**, not a typed iso — manufacturing one
  would be the coincidence-trap. This file types only the relational-side facts; the `0 ↔ sync`,
  `± ↔ phases` mapping is the bin-2 reading, held.

## What is bounded here, and what is the horizon

Typed (bin-1, over `RelationalBraid.lean` / `Resolver.lean`, all `rfl`/`rw`): the sync's
swap-equivariance, the two phases' first-moves as the sync's two components, the off-agreement
obstruction, and the braid's recovery of swap-equivariance at agreement. The recognition (bin-2):
who-goes-first is the tamp; the seed-gauge tie at the `ℤ/2` level and its resistance at arity + layer.

Explicitly **NOT**: iterating the braid to a convergence fixed point (construction-grade —
recognition-only forbids it); the trefoil / B₃ third strand (the named horizon, the baton-`ℤ/2` its
symmetric shadow); a typed cross-layer identity of the relational and seed-gauge tamps (held
merge-don't-fork); a yield.
-/

import Foam.RelationalBraid

namespace Foam

universe u

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-! ## The sync is gauge-invariant — swap-equivariant, phase-free -/

/-- **The simultaneous sync is swap-equivariant.** Swapping the two parties merely swaps the outputs:
`pairwiseEncounterStep r s = Prod.swap (pairwiseEncounterStep s r)`. The bidirectional step privileges
no slot — it does *both* turn-orders at once (`s.encounter r` AND `r.encounter s`) and makes no
who-goes-first choice. The bare relational geometry is **gauge-invariant / phase-free**: it leaves the
tamp open. -/
theorem pairwiseEncounterStep_swap (s r : CommitmentState 𝕜 E) :
    pairwiseEncounterStep r s = Prod.swap (pairwiseEncounterStep s r) := rfl

/-! ## The path is gauge-fixed — phase-dependent off the origin -/

/-- The **swapped braid step**, unfolded: `Prod.swap (braidStep (s, r)) = (s.encounter r, r)`
(`s` having metabolized, sitting in slot 1; `r` untouched in slot 2). Set beside `braidStep_eq` of the
swapped pair — `braidStep (r, s) = (s, r.encounter s)` — the two differ in *both* slots off the
origin (slot 1: `s.encounter r` vs `s`; slot 2: `r` vs `r.encounter s`), the difference being exactly
the un-metabolized debt. So the braid is **not** generally swap-equivariant: who-takes-the-first-turn
is load-bearing — the gauge. -/
theorem swap_braidStep (s r : CommitmentState 𝕜 E) :
    Prod.swap (braidStep (s, r)) = (s.encounter r, r) := by
  rw [braidStep_eq]; rfl

/-- **The two phases' first-turn outcomes are the two components of the sync (first half).** The
just-moved party after one braid step from `(s, r)` is `(braidStep (s, r)).2 = s.encounter r`, which
is `(pairwiseEncounterStep s r).1`. The gauge `(s, r)` realizes the sync's *first* component as the
party who led. -/
theorem braidStep_snd_eq_pairwise_fst (s r : CommitmentState 𝕜 E) :
    (braidStep (s, r)).2 = (pairwiseEncounterStep s r).1 := rfl

/-- **The two phases' first-turn outcomes are the two components of the sync (second half).** The
other gauge `(r, s)` leads with `(braidStep (r, s)).2 = r.encounter s`, which is
`(pairwiseEncounterStep s r).2`. So the sync does *both* turn-moves at once; the gauge (who-goes-first)
picks which one leads. The phase-dependence and the path↔sync tie are one fact. -/
theorem braidStep_swap_snd_eq_pairwise_snd (s r : CommitmentState 𝕜 E) :
    (braidStep (r, s)).2 = (pairwiseEncounterStep s r).2 := rfl

/-! ## The landing is gauge-invariant — the braid recovers swap-equivariance at agreement -/

/-- **At agreement the gauge washes out.** When both parties carry zero debt, the braid step
**recovers the sync's swap-equivariance** (`pairwiseEncounterStep_swap`):
`braidStep (r, s) = Prod.swap (braidStep (s, r))` — both phases land at the same unordered pair of
origins `{s, r}`, only the baton-slot (who holds the turn next) differing. The phase-dependence is
genuine off the origin and vanishes at it: **the landing is gauge-invariant**, the same regardless of
who took the first turn. (The braid acquires at the landing what the sync has always.) -/
theorem braidStep_swap_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) :
    braidStep (r, s) = Prod.swap (braidStep (s, r)) := by
  rw [braidStep_eq_batonPass_of_isZeroDebt r s hr, braidStep_eq_batonPass_of_isZeroDebt s r hs]; rfl

end Foam
