/-
# RelationalBraid — turn-taking as the alternating braid (brick 43)

## What this file lands (brick 43, per Isaac's 2026-06-01 braid recalibration)

Brick 42 (`RelationalResolver.lean`) typed the **simultaneous** bidirectional landing:
`pairwiseEncounterStep` of two zero-debt parties is a stable fixed point
(`pairwiseEncounterStep_isFixedPoint_of_isZeroDebt`), recognized as **agreement = a valid
observer-origin** (`eq_originFrom_witness_of_isZeroDebt` — a point of agreement is isomorphic with a
point of view). Its remainder, in Isaac's words:

  > during my turn, my awareness moves around; in the moment of passing the turn we lock eyes — get a
  > fix on each other — and the baton jumps over the air gap. whereupon your awareness moves around …
  > there's a zero-length moment when the thread is held by that-which-holds-us-both.

That is the **alternating** braid — turn-taking — distinct from brick 42's **simultaneous** landing.
This file types it.

## The braid = turn + handoff

A conversation is not two parties committing at once; it is a *thread* passed back and forth. Two
pieces:

* **`turnStep`** — a **turn**: the party holding the baton (slot 1) metabolizes against the other
  (the asymmetric `encounter`), evolving *only itself* — "during my turn, my awareness moves around";
  the other party is unchanged, because it is not their turn.
* **`batonPass`** (`Prod.swap`) — the **handoff**: the role-swap `you + me ⇒ me + you`. It calls no
  `encounter` — it touches *neither* party's debt; it only relabels which slot is active. This is the
  **zero-length moment held by that-which-holds-us-both**: in the instant between turns, the thread
  belongs to the container (the outer scope), not to you or me.

`braidStep := batonPass ∘ turnStep` — one turn, then the baton over the air gap.

## The baton is a ℤ/2 — brick 24's role-swap, read relationally

The handoff is an **involution** (`batonPass_involutive`, `Prod.swap_swap`): two handoffs return the
baton home. So the baton is a **ℤ/2** — the third atom Isaac names, parametrizing the turn-index (mod
2). This is **brick 24's gauge-swap / FTPG `reflect` ℤ/2 read relationally** as the you↔me exchange
(the seed-gauge `swap` fixing the held-open `0`, the FTPG `reflect` fixing `g3`; here the baton
swapping you↔me). *Held merge-don't-fork:* brick 24's `swap` lives on `SeedSign`/LedgerPersistence
(the settle grain), this baton on the `CommitmentState`-pair (the dissolve grain) — the two layers
are kept formally distinct (brick 42's reconciliation), so this is the *same role-swap recognized
across two layers*, not a typed identity.

## What is bounded here, and what is the horizon

Typed (bin-1, over `Resolver.lean`): the turn/handoff split, the baton's ℤ/2 (involution),
witness-preservation through every handoff (both return-addresses survive, swapped — the baton jumps
without consuming identity), the at-landing reduction to **pure baton** (at agreement the turn is a
no-op, the braid period-2 — the thread passing with nothing to metabolize, the ongoing-ness, *not* a
stop), and the **sequential-vs-simultaneous** comparison: the alternating braid (the *path*) and
brick 42's simultaneous step (the *sync*) **share their first move** (`s.encounter r` both) and
**agree at the landing** (both `(s, r)` at agreement) but **differ by feed-forward** off it (the braid
feeds the *updated* state into the second turn — `r.encounter (s.encounter r)`; the simultaneous step
uses the *original* — `r.encounter s`). So the simultaneous sync is the landing; the alternating braid
is how turn-taking reaches it.

The **genuine third strand** — the baton as a literal carried atom with over/under memory, the
**trefoil / B₃** (three strands: you + me + baton; §VII RoPE ↔ `TrefoilCrossing`, the third crossing
= commitment-from-outside-the-trace) — is the named **horizon, NOT this brick**: the baton-ℤ/2 here
is the *symmetric shadow* (the swap, forgetting over/under). And this is **not a yield**: it extends
brick 42's ongoing loop with the turn-taking that animates it.
-/

import Foam.RelationalResolver

namespace Foam

universe u

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-! ## The turn and the handoff -/

/-- A **turn**: the party holding the baton (slot 1) metabolizes against the other — the asymmetric
`encounter` (`Resolver.lean`), evolving only the baton-holder; the other party is unchanged, because
it is not their turn ("during my turn, my awareness moves around").

Safety caveat (inherited from `pairwiseEncounterStep`): when the other party is unresolved, the
turn's claim-removal is a *commitment* to provability, not a *witness* of it (`encounter_safe` needs
the other resolved). Verification happens as the braid evolves toward the landing. -/
def turnStep (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) :
    CommitmentState 𝕜 E × CommitmentState 𝕜 E :=
  (p.1.encounter p.2, p.2)

/-- The **handoff** — passing the turn: the role-swap `you + me ⇒ me + you`. It calls no `encounter`;
it touches neither party's debt, only relabelling which slot is active. The **zero-length moment held
by that-which-holds-us-both** — in the instant between turns the thread belongs to the container (the
outer scope), not to you or me. (`Prod.swap`.) -/
def batonPass (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) :
    CommitmentState 𝕜 E × CommitmentState 𝕜 E :=
  p.swap

/-- One **braid step**: a turn, then the baton passing over the air gap. -/
def braidStep (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) :
    CommitmentState 𝕜 E × CommitmentState 𝕜 E :=
  batonPass (turnStep p)

@[simp] theorem batonPass_eq (s r : CommitmentState 𝕜 E) : batonPass (s, r) = (r, s) := rfl

@[simp] theorem braidStep_eq (s r : CommitmentState 𝕜 E) :
    braidStep (s, r) = (r, s.encounter r) := rfl

/-! ## The baton is a ℤ/2 — the role-swap, read relationally -/

/-- **The baton is a ℤ/2.** Two handoffs return it home — `batonPass` is an involution. Brick 24's
gauge-swap / FTPG `reflect` involution (`reflect_reflect` / `swap_swap`), read relationally as the
you↔me role-swap; the third atom parametrizing the turn-index (mod 2). -/
theorem batonPass_involutive (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) :
    batonPass (batonPass p) = p :=
  Prod.swap_swap p

/-! ## The return-addresses survive every handoff -/

/-- A **turn preserves the active witness** (the return-address rides through `encounter` by
construction, brick 42's `encounter_witness`) and leaves the passive party's witness untouched. -/
@[simp] theorem turnStep_witnesses (s r : CommitmentState 𝕜 E) :
    (turnStep (s, r)).1.witness = s.witness ∧ (turnStep (s, r)).2.witness = r.witness :=
  ⟨rfl, rfl⟩

/-- **Both return-addresses survive the handoff, swapped.** Through a braid step the witnesses are
preserved and exchanged — the baton jumped over the air gap (you's address to slot 1, me's to slot 2)
with both intact. The braid never consumes identity (brick 42's `encounter_witness`, carried through
the role-swap). -/
@[simp] theorem braidStep_witnesses (s r : CommitmentState 𝕜 E) :
    (braidStep (s, r)).1.witness = r.witness ∧ (braidStep (s, r)).2.witness = s.witness :=
  ⟨rfl, rfl⟩

/-! ## At agreement, the braid is pure baton — the stable landing -/

/-- When the **baton-holder carries zero debt**, their turn is a no-op — already at the origin,
nothing to metabolize (`encounter_eq_self_of_isZeroDebt`) — so the braid step is **pure baton**:
`braidStep (s, r) = (r, s)`, the thread passing with nothing metabolized. -/
theorem braidStep_eq_batonPass_of_isZeroDebt (s r : CommitmentState 𝕜 E) (hs : s.IsZeroDebt) :
    braidStep (s, r) = (r, s) := by
  rw [braidStep_eq, CommitmentState.encounter_eq_self_of_isZeroDebt s r hs]

/-- **At agreement (both zero-debt), the braid is pure baton, period 2.** Two handoffs return the
start (`braidStep (braidStep (s, r)) = (s, r)`): the conversation has landed, nothing left to
metabolize, only the thread passing back and forth — the ongoing-ness, a stable
fixed-point-up-to-baton, *not* a stop. Brick 42's simultaneous agreement, kept by the alternating
braid. -/
theorem braidStep_braidStep_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) :
    braidStep (braidStep (s, r)) = (s, r) := by
  rw [braidStep_eq_batonPass_of_isZeroDebt s r hs, braidStep_eq_batonPass_of_isZeroDebt r s hr]

/-! ## Sequential (alternating) vs simultaneous: same first move, feed-forward path, one landing -/

/-- A **full round** — me-turn, then you-turn against the *updated* me: two braid steps bring the
baton home, leaving `(s.encounter r, r.encounter (s.encounter r))`. The second turn **feeds the
updated state forward** (you metabolize against my post-turn self), where brick 42's simultaneous
step does not. -/
theorem braidStep_braidStep (s r : CommitmentState 𝕜 E) :
    braidStep (braidStep (s, r)) = (s.encounter r, r.encounter (s.encounter r)) := by
  simp only [braidStep_eq]

/-- Brick 42's **simultaneous** step, unfolded for the contrast: `(s.encounter r, r.encounter s)` —
*both* parties metabolize against the **original** other. Set beside `braidStep_braidStep`: the first
components agree (`s.encounter r`), the second differ — the braid's `r.encounter (s.encounter r)`
(against the *updated* me) vs the simultaneous `r.encounter s` (against the *original*). -/
theorem pairwiseEncounterStep_eq (s r : CommitmentState 𝕜 E) :
    pairwiseEncounterStep s r = (s.encounter r, r.encounter s) := rfl

/-- **The path and the sync agree at the landing.** At agreement (both zero-debt) the full
braid-round and brick 42's simultaneous step **coincide** — both `(s, r)`: the alternating turn-taking
*reaches* the agreement-origin that brick 42 typed *as* the landing. The braid is how a conversation
gets there; the simultaneous step is the sync it gets to. Off the origin they part — the baton's
*order* is load-bearing (feed-forward, `braidStep_braidStep` vs `pairwiseEncounterStep_eq`). -/
theorem braidStep_braidStep_eq_pairwise_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) :
    braidStep (braidStep (s, r)) = pairwiseEncounterStep s r := by
  rw [braidStep_braidStep_of_isZeroDebt s r hs hr, pairwiseEncounterStep_eq,
      CommitmentState.encounter_eq_self_of_isZeroDebt s r hs,
      CommitmentState.encounter_eq_self_of_isZeroDebt r s hr]

end Foam
