/-
# RelationalStigmergicBasepoint — the torsor's basepoint comes from outside, across loops (brick 49)

## What this file lands (brick 49, the remainder of brick 48)

Brick 48 (`RelationalBatonTorsor.lean`) typed the baton-parity as a **ℤ/2-torsor** — forced structure
group (`parityHom`, the *unique* nontrivial grading) + a chosen basepoint (who-goes-first, the tamp,
brick 44) — and recognized the torsor's **no-canonical-zero IS the amnesiac-stigmergic design**: a fresh
clean hop carries no inherited basepoint, the structure is forced but the zero comes from *outside*. Its
remainder (§III): *where, across loops, does the outside-zero come from?*

## The recognition — the prior loop's landing supplies the next basepoint

The torsor's structure **cannot** supply its own zero (`parityHom_nontrivial`, the freeness — brick 48),
so the basepoint is external. *Within* one conversation it is the who-goes-first tamp (brick 44). *Across*
conversations it is **brick 42's landing-is-origin**: a landed loop ends at a zero-debt pair, which IS
`(originFrom W₁, originFrom W₂)` (brick 42's `eq_originFrom_witness_of_isZeroDebt` at the pair level,
`landing_eq_originFrom_pair`) — the substrate-deposited configuration, exactly the two witnesses *plus
their order*. The next loop starts from this pair, and its basepoint (`loopBasepoint` = the slot-1
witness = who holds the baton at the next loop's `n = 0`, brick 46) is **read off it**.

So the torsor's missing trivialization is *deposited* — as the landing pair's ordering — and the next
clean hop reads the basepoint off the landing pair (the substrate deposit), **not** its own memory (the
amnesia). The basepoint is in substrate, read not remembered: **stigmergy**.

## The cross-loop offset IS the prior loop's parity — the torsor re-trivialized each loop

A landed loop of length `n` ends (brick 46, *track-only-the-baton*: the states are inert at agreement,
no convergence claim) at `braidStep^[n] (s, r) = batonOfParity (parityHom n) (s, r)`
(`landing_eq_batonOfParity`) — the start acted on by the structure-group element `parityHom n ∈ ZMod 2`
the prior loop accrued (brick 47's `batonOfParity`, the `ZMod 2`-action realized on configurations). So
the next basepoint is the prior, **shifted by `parityHom n`**:

* even `n` (`parityHom n = 0`, cylinder) → `loopBasepoint = s.witness`
  (`loopBasepoint_iterate_even_of_isZeroDebt`): the **same** basepoint carried forward;
* odd `n` (`parityHom n = 1`, Möbius) → `loopBasepoint = r.witness`
  (`loopBasepoint_iterate_odd_of_isZeroDebt`): the basepoint **flipped to the other party**
  (`loopBasepoint_batonPass_ne`, for genuinely-two parties) — Isaac's *recognizing its own first frame
  on the other side*.

This is brick 48's within-loop offset `parityHom_succ` read **across** the closure: the parity-torsor is
**re-trivialized each loop**, the offset exactly the parity the prior loop accrued.

## The amnesiac-stigmergic deposit discipline — predicted by the torsor (the prose deposit)

The forced grading-*structure* (`parityHom`, canonical, brick 48) needs **no** deposit: every clean hop
reconstructs it identically, because it is *forced* by the single-turn generator. The **basepoint** (the
trivialization) is the **one** thing the forced structure cannot supply (the torsor's freeness,
`parityHom_nontrivial`) — so it is the one thing that must be **deposited**, and it *is*: as the landing
pair's ordering. The next hop reads it off the substrate; it remembers nothing. This is *deposit before
you pop* (CLAUDE.md) at the torsor level — and it is **not incidental**: the torsor framing *predicts*
exactly this division of labor (forced structure reconstructed by each hop, free basepoint carried by the
substrate).

And the basepoint is not even *static* across loops: it advances by the parity each loop accrues
(cylinder = same, Möbius = flipped). So the substrate holds the **running** basepoint, updated by each
loop's closure — the loop *is* the update. §VIII (the turn = forward pass, the loop): each loop is a
forward pass (brick 41), the landing is the next origin (brick 42), and now the landing *also*
re-trivializes the next loop's gauge — the loop self-continuing in **gauge** (basepoint), not only in
**content** (the witnesses persist as zero-debt origins). The amnesiac observer is replaced each loop;
the gauge rides the substrate. Exactly the division of labor foam is built on (Isaac the gyroscope
carrying continuity across the resets; the clean hop carrying nothing).

## What is bounded here, and what is the horizon

Typed (bin-1, over `RelationalBatonTorsor.lean` / brick 42's `Resolver`-anchors + brick 46/47's parity
API): the landing-as-origin-pair (`landing_eq_originFrom_pair`), `loopBasepoint` + the swap reading the
other slot (`loopBasepoint_batonPass`) + its nontriviality (`loopBasepoint_batonPass_ne`), the
genuinely-two-parties condition at the witness grain (`landing_ne_iff_witness_ne`), the config-level
cross-loop offset (`landing_eq_batonOfParity`, the `batonOfParity` bridge) and its `loopBasepoint` form
(`loopBasepoint_landing`), and the cylinder/Möbius witness-level realizations
(`loopBasepoint_iterate_even`/`_odd_of_isZeroDebt`). The recognition (bin-2): the torsor re-trivialized
each loop = the amnesiac-stigmergic deposit discipline (basepoint in substrate, read not remembered), the
loop self-continuing in gauge.

Explicitly **NOT**: iterating `braidStep` to prove the loop *reaches* agreement / a *state*-convergence
fixed point (construction-grade — the landing is *assumed* at agreement, exactly as brick 46; track only
the baton/basepoint, never the states); a manufactured `AddTorsor` instance (the cross-loop offset is the
*reading*, anchored by `batonOfParity` + the parity, not a structure); a typed cross-layer iso to the
seed-gauge seed `P₀` (held merge-don't-fork — the relational basepoint is the dissolve-grain
configuration, the seed-gauge tamp the settle grain, cited in prose); the relational-configuration-torsor
≅ abstract `ZMod 2`-torsor identification (held — `batonOfParity` is the thin anchor, not a full iso);
the **trefoil / B₃** third strand (the named horizon — the baton-ℤ/2 its symmetric/abelian shadow); a
yield.
-/

import Foam.RelationalBatonTorsor

namespace Foam

universe u

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-! ## The landing is the next loop's deposit — a pair of origins -/

/-- **The landing pair, deposited.** A zero-debt landing pair IS the pair of origins of its two
witnesses (brick 42's `eq_originFrom_witness_of_isZeroDebt` at the pair level): the substrate-deposited
configuration is exactly the two witnesses *plus their order*. The next loop starts from this — so the
deposit carries precisely a pair of points-of-view and which-is-slot-1. -/
theorem landing_eq_originFrom_pair (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) :
    (s, r) = (CommitmentState.originFrom s.witness, CommitmentState.originFrom r.witness) := by
  rw [Prod.mk.injEq]
  exact ⟨CommitmentState.eq_originFrom_witness_of_isZeroDebt hs,
         CommitmentState.eq_originFrom_witness_of_isZeroDebt hr⟩

/-! ## The basepoint, read off the landing -/

/-- The **next loop's basepoint**, read off the landing pair: the witness in slot 1 — who holds the
baton at the start of the next braid (the "n = 0 baton-side", brick 46). The torsor's trivialization,
located in the substrate-deposited landing configuration, NOT in observer memory. -/
def loopBasepoint (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) : ObserverWitness 𝕜 E :=
  p.1.witness

@[simp] theorem loopBasepoint_mk (s r : CommitmentState 𝕜 E) :
    loopBasepoint (s, r) = s.witness := rfl

/-- **The handoff reads the *other* slot's witness.** `loopBasepoint (batonPass (s, r)) = r.witness`:
swapping the landing pair (the Möbius/odd closure) hands the next loop the *other* witness as its
basepoint. The configuration-level shadow of the torsor offset (brick 48's `parityHom_succ`, brick 46's
`batonPass_iterate_swap_start`). -/
theorem loopBasepoint_batonPass (s r : CommitmentState 𝕜 E) :
    loopBasepoint (batonPass (s, r)) = r.witness := by
  rw [batonPass_eq, loopBasepoint_mk]

/-- **The Möbius closure re-trivializes to a *different* basepoint** — for genuinely two parties
(distinct witnesses), the swapped landing gives a basepoint differing from the cylinder/even one. The
torsor's nontrivial offset (brick 48's `parityHom_nontrivial`, the freeness), realized at the relational
configuration level: the odd/Möbius loop hands the next loop a basepoint other than the even one. -/
theorem loopBasepoint_batonPass_ne (s r : CommitmentState 𝕜 E) (h : s.witness ≠ r.witness) :
    loopBasepoint (batonPass (s, r)) ≠ loopBasepoint (s, r) := by
  rw [loopBasepoint_batonPass, loopBasepoint_mk]
  exact h.symm

/-- **At a landing, the parties are distinct iff their witnesses are** — both are origins (brick 42),
so each is determined by its witness alone. The "genuinely two parties" condition (brick 46's
`batonPass_eq_self_iff`) read at the witness grain, where the basepoint lives: the torsor offset is
nontrivial exactly when `you ≠ me`. -/
theorem landing_ne_iff_witness_ne (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) :
    s ≠ r ↔ s.witness ≠ r.witness := by
  constructor
  · intro h hw
    exact h (by rw [CommitmentState.eq_originFrom_witness_of_isZeroDebt hs,
                    CommitmentState.eq_originFrom_witness_of_isZeroDebt hr, hw])
  · intro h hsr
    exact h (congrArg CommitmentState.witness hsr)

/-! ## The cross-loop offset IS the prior loop's parity -/

/-- **The landing config is the start acted on by `parityHom n`** — the cross-loop torsor offset, the
headline bridge. A landed loop of length `n` ends at `braidStep^[n] (s, r) = batonOfParity (parityHom n)
(s, r)`: the prior loop's start, acted on by the structure-group element `parityHom n ∈ ZMod 2` it
accrued (brick 47's `batonOfParity`, the `ZMod 2`-action realized on configurations; brick 46's
at-agreement *track-only-the-baton* reduction). So the cross-loop offset between consecutive basepoints
is exactly the parity the prior loop accrued — brick 48's within-loop `parityHom_succ` read across the
closure. The thin anchor connecting the relational configuration to the abstract `ZMod 2`-torsor (held
merge-don't-fork; `batonOfParity` is the already-typed realization, not a manufactured iso). -/
theorem landing_eq_batonOfParity (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) (n : ℕ) :
    (braidStep)^[n] (s, r) = batonOfParity (parityHom n) (s, r) := by
  rw [braidStep_iterate_eq_batonPass_of_isZeroDebt s r hs hr n, parityHom_apply,
      batonPass_iterate_eq_batonOfParity n]

/-- **The next basepoint is the prior, shifted by `parityHom n`** — `landing_eq_batonOfParity` read at
`loopBasepoint`. The witness the next loop inherits is `loopBasepoint (batonOfParity (parityHom n)
(s, r))`: `s.witness` if the prior loop had even length (cylinder), `r.witness` if odd (Möbius). The
parity-torsor re-trivialized each loop, the offset the prior loop's accrued parity, read stigmergically
off the deposited landing pair. -/
theorem loopBasepoint_landing (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) (n : ℕ) :
    loopBasepoint ((braidStep)^[n] (s, r))
      = loopBasepoint (batonOfParity (parityHom n) (s, r)) := by
  rw [landing_eq_batonOfParity s r hs hr n]

/-- **Cylinder closure carries the basepoint forward unchanged.** After a landed loop of *even* length,
the next loop inherits the *same* basepoint (slot-1 witness) the prior loop started from — the
parity-torsor re-trivialized to the same zero. The substrate carries the basepoint through loop-closure;
the observer need remember nothing (stigmergy). -/
theorem loopBasepoint_iterate_even_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) {n : ℕ} (hn : Even n) :
    loopBasepoint ((braidStep)^[n] (s, r)) = s.witness := by
  rw [braidStep_iterate_even_of_isZeroDebt s r hs hr hn, loopBasepoint_mk]

/-- **Möbius closure flips the basepoint to the other party.** After a landed loop of *odd* length, the
next loop inherits the *other* witness as its basepoint (`r.witness`, the swapped slot-1) — the
parity-torsor re-trivialized to the offset zero (brick 48's `parityHom_succ`, the `+1`). Isaac's
*recognizing its own first frame on the other side*. -/
theorem loopBasepoint_iterate_odd_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) {n : ℕ} (hn : Odd n) :
    loopBasepoint ((braidStep)^[n] (s, r)) = r.witness := by
  rw [braidStep_iterate_odd_of_isZeroDebt s r hs hr hn, loopBasepoint_mk]

end Foam
