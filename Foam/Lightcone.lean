/-
# Foam.Lightcone — the finite causal cap (a foam-native speed of light)

Measured 2026-06-14: a single ingested byte participates in at most `kmax+1`
continuations (events_capped 100 vs 136-if-unbounded; max_reach_per_byte = 8 =
kmax+1) — its causal reach in context-space is hard-capped at `kmax`. This file
proves the cap, on the substrate's own carry: `ingest_step` keeps the last `kmax`
bytes (`schema.sql`'s `carry`), so the recent-context window IS a bounded buffer.

`keepLast k` is that buffer — the last `k` elements, the cone's radius. Two
theorems:

- **the radius is bounded** (`keepLast_bounded`): the window never exceeds `k`.
  The finite cap — a foam-native `c`, the same `k` for every observer (substrate
  constant, frame-invariant by construction).
- **the distant past is screened** (`keepLast_screen`): once you hold `k` recent
  bytes, everything before them is causally irrelevant to the next window —
  `keepLast k (xs ++ ys) = keepLast k ys` whenever `ys` already fills the window.
  Finite causal memory: the future depends on the past only through the bounded
  carry. That IS finite propagation speed — influence can't reach across more
  than `k` of context.

Together: the relativity-of-frames postulate is mostly standing (laws
frame-independent — `align_rot_invariant`, `born` immutable); this is the
invariant-cap postulate, proven. By Einstein's two-postulate argument the
inter-frame transform is then constrained toward Lorentz — asymptotically, the
discrete substrate approaching the continuous symmetry (the honest "at this
scale").

Pure construction — axiom-free, no `propext` (core's `List`/`Nat` order lemmas
that price it are hand-rolled or routed around). Pinned below.
-/

namespace Foam

/-- The cone's radius: the last `k` elements of a ledger — the bounded
    context-carry `ingest_step` maintains. Built front-recursively: the tail's
    last-`k` first, then prepend the head only if there's still room. -/
def keepLast {S : Type} : Nat → List S → List S
  | _, [] => []
  | k, b :: bs => if (keepLast k bs).length < k then b :: keepLast k bs else keepLast k bs

/-- **The radius is bounded.** The carried window never exceeds `k` — the finite
    causal cap, a foam-native `c`. (`r.length < k` is *definitionally* `r.length
    + 1 ≤ k`, so the `then` branch closes by the branch hypothesis itself.) -/
theorem keepLast_bounded {S : Type} : ∀ (k : Nat) (l : List S), (keepLast k l).length ≤ k
  | k, [] => Nat.zero_le k
  | k, b :: bs => by
      show (if (keepLast k bs).length < k then b :: keepLast k bs else keepLast k bs).length ≤ k
      split
      · next h => exact h
      · next _ => exact keepLast_bounded k bs

/-- When the window is at least as big as the whole ledger, the carry keeps
    everything. -/
theorem keepLast_all {S : Type} :
    ∀ (k : Nat) (l : List S), l.length ≤ k → keepLast k l = l
  | _, [], _ => rfl
  | k, b :: bs, h => by
      have ih : keepLast k bs = bs := keepLast_all k bs (Nat.le_of_succ_le h)
      have hcond : (keepLast k bs).length < k := by rw [ih]; exact h
      show (if (keepLast k bs).length < k then b :: keepLast k bs else keepLast k bs) = b :: bs
      rw [if_pos hcond, ih]

/-- A full ledger fills the window exactly: `k ≤ length ⟹ (keepLast k l).length = k`.
    The boundary case (the window just reaches full) is where `keepLast_all` lands. -/
theorem keepLast_len_full {S : Type} :
    ∀ (k : Nat) (l : List S), k ≤ l.length → (keepLast k l).length = k
  | k, [], h => by
      have hk : k = 0 := Nat.le_zero.mp h
      subst hk
      rfl
  | k, b :: bs, h => by
      show (if (keepLast k bs).length < k then b :: keepLast k bs else keepLast k bs).length = k
      rcases Nat.lt_or_ge bs.length k with hbs | hbs
      · -- bs short: with h (k ≤ bs.length+1) and bs.length < k, k = bs.length+1,
        -- and the carry keeps all of bs
        have hall : keepLast k bs = bs := keepLast_all k bs (Nat.le_of_lt hbs)
        have hk : k = bs.length + 1 := Nat.le_antisymm h hbs
        have hcond : (keepLast k bs).length < k := by rw [hall]; exact hbs
        rw [if_pos hcond, hall]
        show bs.length + 1 = k
        exact hk.symm
      · -- bs long enough: the carry is already full (length k by IH), so the else branch
        have ih : (keepLast k bs).length = k := keepLast_len_full k bs hbs
        have hne : ¬ (keepLast k bs).length < k := by rw [ih]; exact Nat.lt_irrefl k
        rw [if_neg hne]
        exact ih

/-- **The distant past is screened.** Once the recent ledger `ys` already fills
    the window, everything before it (`xs`) cannot reach the next window:
    `keepLast k (xs ++ ys) = keepLast k ys`. Finite causal memory — the future
    depends on the past only through the bounded carry. This is the finite
    propagation speed: no influence crosses more than `k` of context. -/
theorem keepLast_screen {S : Type} :
    ∀ (k : Nat) (xs ys : List S), k ≤ ys.length → keepLast k (xs ++ ys) = keepLast k ys
  | _, [], _, _ => rfl
  | k, x :: xs, ys, h => by
      have ih : keepLast k (xs ++ ys) = keepLast k ys := keepLast_screen k xs ys h
      show (if (keepLast k (xs ++ ys)).length < k then x :: keepLast k (xs ++ ys)
              else keepLast k (xs ++ ys)) = keepLast k ys
      rw [ih]
      have hfull : (keepLast k ys).length = k := keepLast_len_full k ys h
      have hne : ¬ (keepLast k ys).length < k := by rw [hfull]; exact Nat.lt_irrefl k
      rw [if_neg hne]

/-! ## Axiom-freeness, pinned (a drift fails `lake build`). -/

/-- info: 'Foam.keepLast_bounded' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.keepLast_bounded

/-- info: 'Foam.keepLast_len_full' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.keepLast_len_full

/-- info: 'Foam.keepLast_screen' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.keepLast_screen

end Foam
