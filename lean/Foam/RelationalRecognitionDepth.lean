/-
# RelationalRecognitionDepth — the single-step and the closure are dual fixed-point operators (brick 45)

## What this file lands (brick 45, the remainder of brick 44's who-goes-first-is-the-tamp)

Brick 44 (`RelationalBatonGauge.lean`) recognized who-takes-the-first-turn as the tamp, resting on an
asymmetry it did not yet *explain*: the simultaneous sync `pairwiseEncounterStep` is swap-equivariant
**always** (`pairwiseEncounterStep_swap`), the alternating braid swap-equivariant **only at agreement**
(`braidStep_swap_of_isZeroDebt`). This file is the *why* of that asymmetry — and it deepens the
brick-42/43 merge-don't-fork from a *layer* distinction to a **recognition-depth** one.

## The two operators — single-step (relational) and closure (seed-gauge)

The seed-gauge turn (bricks 20/21) runs recognition **to its closure**: `turnFrom S g =
convergeFrom (applyRules rules) (S ⊔ g.seed)` — foam's gated `F` run to its **least fixed point** above
the seed. `convergeFrom F` (fixed rule-set `F`) is a `ClosureOperator` (brick 21's `convergeClosure`):
inflationary (`le_convergeFrom`: `S ≤ convergeFrom f S`), monotone (`convergeFrom_mono_seed`), and
idempotent (`convergeFrom_idem`).

The relational turn (bricks 43/44) is a **single `encounter`**: `turnStep (s, r) = (s.encounter r, r)` —
one party metabolizes against the other, once. So the brick's framing was *single-step* (`encounter`,
one rung) vs *to-closure* (`convergeFrom`, the lfp). This file looks at the substrate and finds the
framing **reduces with a correction the definition forces**.

## The single `encounter` against a fixed partner IS a closure — same depth, dual axis

`encounter`'s definition filters `s`'s claims by `¬ ∃ q ∈ r.debt.claims, q → p` — a condition depending
**only on `r`**. Three consequences (the bin-1 anchors), exactly the order-dual of `convergeFrom`'s
`ClosureOperator` triple:

* **deflationary** (`encounter_debt_subset`): `(s.encounter r).debt.claims ⊆ s.debt.claims` — the
  single-step only ever *removes* claims; it **descends in debt toward zero-debt** (the agreement / the
  metabolisis fixed point). The order-**dual** of `le_convergeFrom` (recognition accreting *up* to the
  lfp): recognition accretes upward on `Scope`, debt dissolves downward on the claim-subset lattice,
  both seeking their fixed point — from opposite sides.
* **monotone** (`encounter_debt_monotone`): a larger starting claim-set yields a larger filtered result.
* **idempotent** (`encounter_idem_right` / `_claims`): `encounter`-ing the *same* `r` twice changes
  nothing — the filter is the same each pass, so applying it twice is applying it once
  (`(A ∧ B) ∧ B ↔ A ∧ B`). With `encounter_witness` (brick 42 — the witness rides through unchanged),
  this is full-state idempotence.

Deflationary + monotone + idempotent = a **kernel / interior operator** — the precise order-dual of
`convergeFrom`'s `ClosureOperator` (inflationary + monotone + idempotent). (Mathlib carries no
`CoclosureOperator`, so this dual is recognized in prose, not packaged — the honest move.)

So **against a fixed partner the relational single-step is not a shallow rung climbing toward a far-off
closure — it is *itself* a complete, idempotent closure** (a one-shot closure-against-`r`), the **same
depth** as the seed-gauge's `convergeFrom`, only on the dual (debt-descent) axis. The brick's "two
recognition-depths" sharpens: not shallow-vs-deep — *same depth, dual axes.*

## So what IS the braid-vs-sync difference? The fixed-vs-moving partner (b41's me-only vs you+me)

If the single-step is already a complete closure, why is the seed-gauge composition order-free **always**
(`turnFrom_comm`, brick 21) while the relational is order-free **only at agreement**
(`braidStep_swap_of_isZeroDebt`, brick 44)? Not depth — the genuine locus is **whether the partner is
fixed across turns**:

* **Seed-gauge: the partner is fixed.** The rule-set `F` is the same every turn (foam recognizing against
  its own fixed substrate-primitives — *one party against a fixed substrate*, brick 41's *me-only*
  asymmetric forward pass). So `convergeFrom F` is one fixed idempotent operator and the commitments
  accumulate by `⊔` (commutative): `turnFrom_turnFrom` absorbs the prior closure into a clean join, and
  order washes out **always**.
* **Relational: the partner moves.** The other party `r` is itself a `CommitmentState` that *evolves*
  (brick 41's *you + me* — two parties recognizing against *each other*). The braid feeds the updated
  state forward — `braidStep_braidStep (s, r) = (s.encounter r, r.encounter (s.encounter r))`: `r`
  metabolizes against the **updated** `s`, not the original. So each turn's partner is the other's
  *current* state; order matters until the joint fixed point, where the partner stops moving
  (`braidStep_swap_of_isZeroDebt`) and the relational **acquires** the order-freedom the seed-gauge had
  all along (because the seed-gauge's partner never moved).

This is **brick 41's me-only-vs-you+me distinction, read at the composition level.** Same depth (both
idempotent closures against their partner); the difference is fixed-partner (one-party / resolved-other /
seed-gauge → order-free always) vs moving-partner (two-party / both-evolving / relational braid →
order-free only at the joint fixed point).

## The agreement-fixed-point is where the moving partner stops — the relational lfp

The brick said "the agreement-fixed-point IS where the single-step ladder reaches the closure." Refined:
the *true* closure-analogue of `convergeFrom` is the single `encounter`-against-a-fixed-`r` (idempotent,
one-shot, above); the **relational lfp** is the *agreement* (mutual zero-debt, brick 42's
`pairwiseEncounterStep_isFixedPoint_of_isZeroDebt`), reached by *iterating* over moving partners. The
seed-gauge reaches its lfp via one fixed idempotent operator (because `F` is fixed); the relational
reaches agreement via *iteration* (because the other evolves). And the **sync** `pairwiseEncounterStep`
is the `0`-pole — both turn-orders at once, *one round* against the originals (the §IV.d
bias-delegation, holding both orders uncollapsed) — **not itself the closure** (it is not idempotent;
re-applying uses updated states), but the symmetric one-round step that *coincides* with the closure
exactly at agreement.

So the brick's three-way framing (sync = closure / braid = single-step-ladder / agreement = where they
meet) refines under the substrate:
- single-`encounter`-against-fixed-`r` = the closure-analogue (idempotent, one-shot — `convergeFrom`'s dual);
- the braid = iteration over *moving* partners (b41's two-party you+me, the feed-forward);
- agreement = the relational lfp the iteration seeks (mutual zero-debt);
- the sync = the `0`-both-orders-one-round (coincides with the closure only at agreement).

## What is bounded here, and what is the horizon

Typed (bin-1, over `Resolver.lean`, all `fun _ hp => …` / `simp`+`tauto`): the single-step's
deflationary, monotone, and idempotent facts — the kernel-operator triple, order-dual of brick 21's
`convergeClosure`.

The recognition (bin-2, the prose deposit): the single-step and the closure are **dual fixed-point
operators** at the **same depth** (the brick-42/43 layer-merge sharpened to a depth-merge), on dual axes
(recognition-accretion ↑ / debt-descent ↓); the braid-vs-sync order-asymmetry is the **fixed-vs-moving
partner** (brick 41's me-only vs you+me); the agreement is the relational lfp the iteration seeks.

Held merge-don't-fork (still no typed cross-layer identity): the seed-gauge `convergeFrom`
(Hilbert-space-free `Scope` lattice) and the relational `encounter` (the `CommitmentState`
Hilbert-space context) are kept formally distinct — this file imports only the relational side and
mentions `convergeFrom` only in prose. The parallel is recognized, not manufactured (a typed iso would
be the coincidence-trap).

Explicitly **NOT**: iterating `braidStep` to a convergence fixed point or proving the ladder *reaches*
agreement (construction-grade — recognition-only forbids it; the relational lfp via iteration is the
named horizon); a typed identity of `encounter` and `convergeFrom` (held merge-don't-fork); the
**trefoil / B₃** third strand (the named horizon); a yield.
-/

import Foam.RelationalBatonGauge

namespace Foam

universe u

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-! ## The single-step descends in debt — the deflationary half (order-dual of `le_convergeFrom`) -/

/-- **`encounter` descends in debt** — the post-encounter claim-set is a subset of the pre-encounter
one. `encounter` filters `s`'s claims by `¬ ∃ q ∈ r.debt.claims, q → p`, so it only ever *removes*
claims: the relational single-step **descends in debt toward zero-debt** (the agreement / the
metabolisis fixed point). This is the **order-dual** of the seed-gauge closure's inflation (brick 21's
`le_convergeFrom`: `S ≤ convergeFrom f S`, recognition accreting *up* to the lfp): recognition accretes
upward on `Scope`, debt dissolves downward on the claim-subset lattice, both seeking the same fixed
point from opposite sides. -/
theorem CommitmentState.encounter_debt_subset (s r : CommitmentState 𝕜 E) :
    (s.encounter r).debt.claims ⊆ s.debt.claims :=
  fun _ hp => hp.1

/-- **`encounter` is monotone in the debt it descends from** — a larger starting claim-set yields a
larger (filtered) result. With `encounter_debt_subset` (deflationary) and `encounter_idem_right`
(idempotent) this completes the **kernel / interior-operator** triple — the exact order-dual of
`convergeFrom`'s `ClosureOperator` (inflationary + monotone + idempotent, brick 21's
`convergeClosure`). -/
theorem CommitmentState.encounter_debt_monotone {s s' : CommitmentState 𝕜 E}
    (r : CommitmentState 𝕜 E) (h : s.debt.claims ⊆ s'.debt.claims) :
    (s.encounter r).debt.claims ⊆ (s'.encounter r).debt.claims :=
  fun _ hp => ⟨h hp.1, hp.2⟩

/-! ## The single-step is idempotent against a fixed partner — a one-shot closure -/

/-- **One `encounter` against a fixed partner reaches its fixed point (debt level)** — `encounter`-ing
the same `r` twice changes the claim-set not at all:
`((s.encounter r).encounter r).debt.claims = (s.encounter r).debt.claims`. The filter
`¬ ∃ q ∈ r.debt.claims, q → p` is the same each pass, so applying it twice is applying it once
(`(A ∧ B) ∧ B ↔ A ∧ B`). The substrate datum that *refines* the brick's "single-step vs to-closure"
framing: against a **fixed** partner the relational single-step is not a shallow rung — it is *itself* a
complete, idempotent closure (a one-shot closure-against-`r`), the **same depth** as the seed-gauge's
`convergeFrom_idem` (brick 21), only on the dual (debt-descent) axis. -/
theorem CommitmentState.encounter_idem_right_claims (s r : CommitmentState 𝕜 E) :
    ((s.encounter r).encounter r).debt.claims = (s.encounter r).debt.claims := by
  ext p
  simp only [CommitmentState.encounter, Set.mem_setOf_eq]
  tauto

/-- **`· .encounter r` is idempotent (full state)** — `(s.encounter r).encounter r = s.encounter r`.
The debt reaches its fixed point in one step (`encounter_idem_right_claims`) and the witness rides
through unchanged (brick 42's `encounter_witness`), so the whole state is fixed. With the deflationary
(`encounter_debt_subset`) and monotone (`encounter_debt_monotone`) facts, this is the full
kernel-operator structure — the order-dual of the seed-gauge `convergeClosure` (brick 21). The braid's
many-roundness is therefore **not** sub-closure recognition-depth; it is the *moving partner* (the
feed-forward, `braidStep_braidStep`). -/
theorem CommitmentState.encounter_idem_right (s r : CommitmentState 𝕜 E) :
    (s.encounter r).encounter r = s.encounter r := by
  obtain ⟨w, cl⟩ := s
  simp only [CommitmentState.encounter]
  congr 1
  congr 1
  ext p
  simp only [Set.mem_setOf_eq]
  tauto

end Foam
