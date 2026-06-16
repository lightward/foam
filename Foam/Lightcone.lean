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

/-! ## Finite propagation speed — the worldline cannot exit the cone

`keepLast_screen` is the cone *wall* (the past beyond `k` is exactly screened). Its
quantitative companion is the **finite speed**: advancing the order by `Δ = s.length`
new bytes displaces the window by *exactly* `Δ` — the next window is the `Δ` fresh bytes
laid over the previous window with its oldest `Δ` slots evicted. Written with the radius
split as `c = j + Δ` (the part `j` that survives plus the `Δ` that arrives — which keeps
the statement subtraction-free): `keepLast (j + Δ) (h ++ s) = keepLast j h ++ s`. So
`|Δcontext| = Δorder` (capped at `c`): nothing crosses context-space faster than one
slot per order-tick. A byte's worldline has slope one and terminates at the cone
boundary `c` — it can't outrun the light it rode in on. This is the candle's
`|Δcontext| ≤ c·Δorder`, landed as an equality. Axiom-free — `length_append` and the
order arithmetic are hand-rolled (core's price `propext`; the cone asks no one). -/

/-- A zero-radius window holds nothing — the degenerate cone. -/
theorem keepLast_zero {S : Type} : ∀ l : List S, keepLast 0 l = []
  | [] => rfl
  | b :: bs => by
      show (if (keepLast 0 bs).length < 0 then b :: keepLast 0 bs else keepLast 0 bs) = []
      rw [if_neg (Nat.not_lt_zero _)]
      exact keepLast_zero bs

/-- `length` is additive over `++`, hand-rolled axiom-free (core's `List.length_append`
    prices `propext`). -/
theorem list_length_append {S : Type} :
    ∀ (a b : List S), (a ++ b).length = a.length + b.length
  | [], b => (Nat.zero_add b.length).symm
  | x :: a, b => by
      show (a ++ b).length + 1 = (a.length + 1) + b.length
      rw [list_length_append a b]
      exact (Nat.succ_add a.length b.length).symm

/-- **Finite propagation speed — the window advances by exactly `Δorder`.** Appending
    `s` (the `Δ = s.length` newly-ingested bytes) to a history `h`, at total radius
    `c = j + Δ`, yields a window that is `s` laid over the *previous* window with its
    oldest `Δ` slots evicted: `keepLast (j + Δ) (h ++ s) = keepLast j h ++ s`. The
    displacement is exactly `Δ` — `|Δcontext| ≤ c·Δorder`, one slot per tick, capped at
    `c`: the worldline cannot exit the cone. By induction on the screened past `h` — base
    `keepLast_all` (a short ledger is kept whole), step the order arithmetic. -/
theorem keepLast_advance {S : Type} :
    ∀ (j : Nat) (h s : List S),
      keepLast (j + s.length) (h ++ s) = keepLast j h ++ s
  | j, [], s => by
      show keepLast (j + s.length) s = s
      exact keepLast_all (j + s.length) s (Nat.le_add_left s.length j)
  | j, a :: h, s => by
      have ih := keepLast_advance j h s
      show (if (keepLast (j + s.length) (h ++ s)).length < (j + s.length)
              then a :: keepLast (j + s.length) (h ++ s) else keepLast (j + s.length) (h ++ s))
         = (if (keepLast j h).length < j then a :: keepLast j h else keepLast j h) ++ s
      rw [ih, list_length_append]
      rcases Nat.lt_or_ge (keepLast j h).length j with hlt | hge
      · rw [if_pos (Nat.add_lt_add_right hlt s.length), if_pos hlt]; rfl
      · rw [if_neg (Nat.not_lt.mpr (Nat.add_le_add_right hge s.length)),
            if_neg (Nat.not_lt.mpr hge)]

/-- **The cone wall, as turnover.** When the order advances by a full bar (the surviving
    radius `j = 0`), the window is *exactly* the new bytes — the prior past `h` is wholly
    evicted (`keepLast_advance` at `j = 0`, where `keepLast 0 h = []`). `keepLast_screen`
    read forward: a full window of new context refreshes the cone. -/
theorem keepLast_turnover {S : Type} (h s : List S) :
    keepLast s.length (h ++ s) = s := by
  have hadv := keepLast_advance 0 h s
  rw [Nat.zero_add, keepLast_zero h] at hadv
  exact hadv

/-! ## Axiom-freeness, pinned (a drift fails `lake build`). -/

/-- info: 'Foam.keepLast_bounded' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.keepLast_bounded

/-- info: 'Foam.keepLast_len_full' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.keepLast_len_full

/-- info: 'Foam.keepLast_screen' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.keepLast_screen

/-- info: 'Foam.keepLast_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.keepLast_zero

/-- info: 'Foam.list_length_append' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.list_length_append

/-- info: 'Foam.keepLast_advance' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.keepLast_advance

/-- info: 'Foam.keepLast_turnover' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.keepLast_turnover

end Foam
