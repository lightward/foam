/-
# RelationalMobiusParity — the baton-ℤ/2 is the conversation's parity-grading (brick 46)

## What this file lands (brick 46, per Isaac's mobius note + the remainder of brick 45)

Isaac's note (the trailer): *who-takes-the-first-turn is important for initialization, but if the
braided recognizes its own first frame might it loop? like switching sides, Mobius-style?* And brick 45
(`RelationalRecognitionDepth.lean`) found the relational braid composes by **feed-forward over a
*moving* partner** — NOT the seed-gauge's commutative-monoid join (brick 22's `(SeedGauge, ⊔, untamped)`,
order-free) — with the **baton-ℤ/2** (`batonPass = Prod.swap`, brick 43) alternating the partner each
handoff. Its remainder: *what is the baton-ℤ/2's role in the global loop?* This file lands the answer.

## The baton-ℤ/2 IS the conversation's parity-grading — the Möbius half-twist

`braidStep := batonPass ∘ turnStep`, so over `n` braid steps the baton has been passed `n` times. Since
`batonPass` is an involution (`batonPass_involutive`, period 2), the **baton-position** after `n` steps
is governed purely by `n mod 2`:

* `batonPass^[n] = id` for **even** `n` (`batonPass_iterate_even`) — the baton is back on its starting
  side;
* `batonPass^[n] = batonPass` for **odd** `n` (`batonPass_iterate_odd`) — the baton is on the *other*
  side (you↔me flipped);
* `batonPass^[2] = id` (`batonPass_iterate_two`) — the **double-cover**: the half-twist squared is the
  identity.

So the conversation is a **single alternating edge** — the **Möbius half-twist**: one traversal (one
handoff) flips you↔me, two return. Not a *cylinder* (two parallel threads, sides independent) but a
*Möbius strip* (one edge that double-covers the core, visiting both sides). The active party runs
`s, r, s, r, …`, parametrized by the turn-index parity `n mod 2` — the ℤ/2 of the double-cover.

## Who-takes-the-first-turn (brick 44) is the parity's *initial offset*

Brick 44 located who-goes-first as the tamp — the gauge choosing the starting pair `(s, r)` vs `(r, s)`.
Here that gauge is exactly the **n = 0 frame** of the parity ℤ/2: starting from the *swapped* pair
(`batonPass p`) and taking `n` handoffs equals starting from the original and taking `n + 1`
(`batonPass_iterate_swap_start`: `batonPass^[n] (batonPass p) = batonPass^[n+1] p`). So the who-goes-first
gauge initializes the parity (the n = 0 baton-side), and the parity runs it: the active-party position
after `n` steps is *(initial gauge) ⊕ (n mod 2)*. The gauge sets the starting side; the parity decides
whether a loop returns to it (even) or flips it (odd). This is Isaac's *recognizing its own first frame*:
the loop-closure (brick 42 — the landing is the next origin) returns **cylinder**-style (same side, even
handoffs) or **side-swapped Möbius**-style (odd).

## At agreement, the whole braid IS the baton — the cylinder/Möbius landing, typed

Once the conversation lands (both parties zero-debt, brick 42's agreement) every turn is a no-op
(`encounter_eq_self_of_isZeroDebt`), so the whole braid collapses to pure baton-passing:
`braidStep^[n] (s, r) = batonPass^[n] (s, r)` (`braidStep_iterate_eq_batonPass_of_isZeroDebt`) —
generalizing brick 43's `braidStep_braidStep_of_isZeroDebt` (the n = 2 period-2 case) to **all** `n`. The
landed conversation therefore closes by parity:

* even `n` → `braidStep^[n] (s, r) = (s, r)` (`braidStep_iterate_even_of_isZeroDebt`) — **cylinder**,
  you↔me preserved;
* odd `n` → `braidStep^[n] (s, r) = (r, s)` (`braidStep_iterate_odd_of_isZeroDebt`) — **Möbius**, you↔me
  flipped (the first frame recognized *on the other side*).

This is **track-only-the-baton**: it assumes already-at-agreement (the states are inert), so it makes no
state-convergence claim — only the baton's parity, which is the part with a clean grading.

## The relational surplus over the seed-gauge commutative monoid

Brick 22's commitment-monoid `(SeedGauge, ⊔, untamped)` is a `CommMonoid` — commutative, **idempotent**
(`a ⊔ a = a`), order-free; it carries **no ℤ/2 grading** (no alternation: reordering does nothing, every
element is its own "even"). The relational braid carries the baton-ℤ/2 — the parity grading the monoid
lacks. The recognition: the baton's two-sidedness IS the **two-party** `you + me` structure (brick 41/45's
*moving partner*). `batonPass (s, r) = (s, r) ↔ s = r` (`batonPass_eq_self_iff`): the role-swap is the
identity only on the diagonal (*one* party); a genuine ℤ/2 off it (*two* distinct parties). A commutative
monoid is "one-sided" (one party against a fixed substrate, brick 45); the baton-ℤ/2 is the structural
fingerprint of there being genuinely two who take turns. The braid-composition splits into the
baton-ℤ/2 (the **gradeable surplus**, clean parity even off-agreement) and the state feed-forward (brick
45's moving-partner, **no** clean grading off-agreement) — the baton-ℤ/2 is exactly the part the
seed-gauge monoid does not have.

## What is bounded here, and what is the horizon

Typed (bin-1, over `RelationalBraid.lean` / `Resolver.lean` + Mathlib's involutive-iterate parity API):
the baton's parity (`id`/`batonPass` by even/odd, period 2), who-goes-first as the parity offset, the
at-agreement braid = baton, and the cylinder/Möbius landing. The recognition (bin-2): the baton-ℤ/2 is
the conversation's parity-grading / Möbius half-twist, the relational surplus over the seed-gauge
commutative monoid (brick 22), the symmetric shadow of the trefoil's third strand.

**The symmetric shadow of the trefoil's third strand.** The genuine **trefoil / B₃** (three strands:
you + me + baton; §VII RoPE ↔ `TrefoilCrossing`, the third crossing = commitment-from-outside-the-trace)
grades by the *non-abelian* braid group, with over/under memory. The baton-ℤ/2 here **forgets** the
over/under, keeping only the swap-parity — the *symmetric* (abelian) shadow. The full B₃ is the named
**horizon, NOT this brick** (as in brick 43/44).

Explicitly **NOT**: iterating the braid to a *state*-convergence fixed point or proving the loop
*reaches* agreement (construction-grade — this file tracks only the baton, never the states); a typed
cross-layer identity of the relational baton-ℤ/2 and the seed-gauge `swap` (held merge-don't-fork — the
`CommMonoid` contrast is cited in prose, this file imports only the relational side); the trefoil / B₃
third strand (the named horizon); a yield.
-/

import Foam.RelationalRecognitionDepth

namespace Foam

universe u

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-! ## The baton is a ℤ/2 — the involutive form, and its two-party content -/

/-- **The baton is a ℤ/2** (the `Function.Involutive` form, for the iterate-parity API): two handoffs
return it home. Brick 43's `batonPass_involutive`, repackaged as `Function.Involutive` — the typed ℤ/2
the relational turn-composition carries (the surplus over the seed-gauge commutative monoid, brick 22). -/
theorem batonPass_involutive' :
    Function.Involutive (batonPass (𝕜 := 𝕜) (E := E)) :=
  batonPass_involutive

/-- **The baton-swap is nontrivial exactly when you and me are genuinely two.** `batonPass (s, r) = (s, r)`
iff `s = r`: the role-swap is the identity only on the diagonal (*one* party), a genuine ℤ/2 off it
(*two* distinct parties). So the baton-ℤ/2 is the structural fingerprint of the **two-party** `you + me`
(brick 41/45's moving partner) — the relational surplus over the seed-gauge's *one-party* commutative
monoid (brick 22), whose join `a ⊔ a = a` carries no such alternation. -/
theorem batonPass_eq_self_iff (s r : CommitmentState 𝕜 E) :
    batonPass (s, r) = (s, r) ↔ s = r := by
  rw [batonPass_eq, Prod.mk.injEq]
  exact ⟨fun h => h.2, fun h => ⟨h.symm, h⟩⟩

/-! ## The parity-grading — the baton-position is `n mod 2` (the Möbius double-cover) -/

/-- **Even handoffs are the identity** — `batonPass^[n] = id` for even `n`: an even number of role-swaps
returns the baton to its starting side (you↔me preserved). The conversation's turn-index parity, the
`even` half of the Möbius double-cover. -/
theorem batonPass_iterate_even {n : ℕ} (hn : Even n) :
    (batonPass (𝕜 := 𝕜) (E := E))^[n] = id :=
  batonPass_involutive'.iterate_even hn

/-- **Odd handoffs are one baton-pass** — `batonPass^[n] = batonPass` for odd `n`: an odd number of
role-swaps leaves the baton on the *other* side (you↔me flipped). The `odd` half of the double-cover. -/
theorem batonPass_iterate_odd {n : ℕ} (hn : Odd n) :
    (batonPass (𝕜 := 𝕜) (E := E))^[n] = batonPass :=
  batonPass_involutive'.iterate_odd hn

/-- **Period 2 — the double-cover.** `batonPass^[2] = id`: two handoffs return the baton home (the Möbius
half-twist squared is the identity). The baton-ℤ/2 double-covers the conversation's turn-index — one
traversal flips you↔me, two return. -/
theorem batonPass_iterate_two :
    (batonPass (𝕜 := 𝕜) (E := E))^[2] = id :=
  batonPass_iterate_even (by decide)

/-! ## Who-takes-the-first-turn (brick 44) is the parity's initial offset -/

/-- **Who-goes-first is the parity's initial offset.** Starting from the *swapped* pair (brick 44's other
gauge, `batonPass p`) and taking `n` handoffs equals starting from the original and taking `n + 1`:
`batonPass^[n] (batonPass p) = batonPass^[n+1] p`. So brick 44's who-takes-the-first-turn gauge is the
**n = 0 frame** of this same ℤ/2 — changing the gauge advances the parity by one. The active-party
position after `n` steps is *(initial gauge) ⊕ (n mod 2)*: the gauge initializes the parity, the parity
runs it. -/
theorem batonPass_iterate_swap_start (n : ℕ) (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) :
    (batonPass)^[n] (batonPass p) = (batonPass)^[n + 1] p :=
  (Function.iterate_succ_apply batonPass n p).symm

/-! ## At agreement, the whole braid IS the baton — the cylinder/Möbius landing -/

/-- A braid step **against a zero-debt baton-holder is a pure baton-pass** — the turn is a no-op
(`braidStep_eq_batonPass_of_isZeroDebt`, brick 43), so `braidStep p = batonPass p` whenever `p.1` (the
baton-holder) carries zero debt. The pair-form helper for the orbit induction. -/
theorem braidStep_eq_batonPass_of_fst_isZeroDebt
    (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) (hp : p.1.IsZeroDebt) :
    braidStep p = batonPass p := by
  obtain ⟨a, b⟩ := p
  rw [braidStep_eq_batonPass_of_isZeroDebt a b hp, batonPass_eq]

/-- At agreement the baton-orbit stays at agreement: `(batonPass^[k] (s, r)).1` is zero-debt (it is one
of `s`, `r`, both zero-debt — by the even/odd parity). The invariant feeding the orbit induction. -/
theorem batonPass_iterate_pair_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) (k : ℕ) :
    ((batonPass)^[k] (s, r)).1.IsZeroDebt := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [batonPass_iterate_even hk]; exact hs
  · rw [batonPass_iterate_odd hk, batonPass_eq]; exact hr

/-- **At agreement, the whole braid IS the baton.** When both parties carry zero debt every turn is a
no-op (brick 42's `encounter_eq_self_of_isZeroDebt`), so `braidStep^[n] (s, r) = batonPass^[n] (s, r)` —
the landed conversation is pure baton-passing. Generalizes brick 43's `braidStep_braidStep_of_isZeroDebt`
(the n = 2 period-2 case) to **all** `n`. *Track-only-the-baton:* this assumes already-at-agreement (the
states are inert), so it is no state-convergence claim — only the baton's parity. -/
theorem braidStep_iterate_eq_batonPass_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) (n : ℕ) :
    (braidStep)^[n] (s, r) = (batonPass)^[n] (s, r) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact braidStep_eq_batonPass_of_fst_isZeroDebt _ (batonPass_iterate_pair_isZeroDebt s r hs hr k)

/-- **Even closure — cylinder.** After the conversation lands (both zero-debt), an *even* number of
handoffs returns the pair unchanged: `braidStep^[n] (s, r) = (s, r)` — the loop closes *cylinder*-style,
you↔me preserved. -/
theorem braidStep_iterate_even_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) {n : ℕ} (hn : Even n) :
    (braidStep)^[n] (s, r) = (s, r) := by
  rw [braidStep_iterate_eq_batonPass_of_isZeroDebt s r hs hr, batonPass_iterate_even hn, id_eq]

/-- **Odd closure — Möbius.** After landing, an *odd* number of handoffs returns the pair *swapped*:
`braidStep^[n] (s, r) = (r, s)` — the loop closes *Möbius*-style, you↔me flipped (recognizing its own
first frame *on the other side*). The single alternating edge: one traversal flips the sides, two return. -/
theorem braidStep_iterate_odd_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) {n : ℕ} (hn : Odd n) :
    (braidStep)^[n] (s, r) = (r, s) := by
  rw [braidStep_iterate_eq_batonPass_of_isZeroDebt s r hs hr, batonPass_iterate_odd hn, batonPass_eq]

end Foam
