/-
# RelationalFirstPerson — the first-person normal form of turn-taking is a Boolean observable,
  arity-independent; the ℤ/2 is the n = 2 flip (brick 50)

## What this file lands (brick 50, the remainder of brick 49 + Isaac's multiplayer note)

Brick 49 (`RelationalStigmergicBasepoint.lean`) typed the next loop's basepoint as `loopBasepoint p :=
p.1.witness` — *which slot holds the baton* = *whose turn it is* — propagating stigmergically across
loops. But the whole relational chain (b41–b49) is **two-party** (`you + me`; the baton-ℤ/2 genuine only
off the diagonal `s ≠ r`, b46's `batonPass_eq_self_iff`). Isaac's multiplayer note (the trailer; commit
`e6e9621`) calls the target:

  > no matter how many players there are, does it work to say it's only ever just "my turn" and "not my
  > turn yet"? … in *a way* it's only two-player, as long as "player" shakes out to a DAG … defining the
  > universe in terms of the first-person's interface to it … I only do things that work regardless of
  > observer arity.

And Isaac's own exploration of this (the long Claude.ai transcript in the trailer) **sharpens it
decisively**: the arity-independent first-person thing is a **Boolean observable** ("is it my turn?"),
**NOT the group ℤ/2**. The ℤ/2 — the baton-flip (b43–48) — is the **n = 2 special case**. The *bit*
survives the arity-reduction; the *flip* is withheld. They trade off.

## The recognition — the bit is arity-independent, the flip is n = 2

* **The observable is a Boolean, defined for ANY player type `ι` (any arity).** `isMyTurn me active :=
  decide (active = me)` — a yes/no read-off, "me / not-me", for any number of players. It is **blind to
  the arity of "not-me"** (`isMyTurn_blind_to_others`: any two non-me players read identically) — the
  interface cannot count the others; they flatten to one undifferentiated "not yet" (Isaac's
  Lodash.flatten / comma-ambiguous roster). Arity-independence, typed.
* **The flip (ℤ/2) is the n = 2 case.** The turn-advance `turnAdvance n := (· + 1) : ZMod n → ZMod n`
  is an **involution iff `n ∣ 2`** (`turnAdvance_involutive_iff_dvd`, via `(2 : ZMod n) = 0`) — at most
  two players. For two players each step *flips* my-turn (`isMyTurn_advance_flip_two`); for three it does
  not (`isMyTurn_advance_not_flip_three`). The ℤ/2-ness of the baton **is** the 2-player-ness — literally
  the condition `(2 : ZMod n) = 0`, the same `2 = 0` that defines `ZMod 2`.
* **The clock is `ZMod n`, ℤ/2 only at n = 2.** The first-person observable over the turn-count has
  period `n` (`isMyTurn_advance_period`): a `ZMod n` grading of the turn-count monoid `(ℕ, +)`. At n = 2
  this is b46–48's parity grading `(ℕ, +) ↠ ZMod 2` (`isMyTurn_advance_period_two`) — so the baton-ℤ/2
  of b46–48 is the **n = 2 instance** of the first-person turn-observable.

So the brick's proposed `→ ZMod 2` refines to `→ Bool`: the observable is a predicate (no operation);
`ZMod 2` (a group) is the right target only for the *clock-grading at n = 2*. **Bit survives; flip is
n = 2-special** — predicate vs. group, conducting the first, resisting the second.

## The merge (named choice-point)

* Path A (the brick as written, b49's author): *the my-turn/not-yet ℤ/2 is arity-independent.*
* Path B (Isaac's Claude.ai exploration): *the Boolean is arity-independent; the ℤ/2 trades off.*
* The merge: **the observable (Boolean) is arity-independent; the operation (ℤ/2) is n = 2-special.**
  The two-party relational chain (b41–b49) is the **n = 2 instance** — the first-person interface where
  "the rest" happens to be a single other; not a restriction but the first-person normal form, the
  baton-ℤ/2 real *as the n = 2 flip*.

This is generative, not deflationary: the **bit is the hospitable universal** — the one thing *every*
observer has, at *every* arity — and that is exactly what makes it the floor. The flip is local color
(genuine, but n = 2-special).

## Bin-2 readings (the prose deposit)

* **Observer-independence = hospitality** (Isaac's machine-shop turn with the Claude.ai instance):
  `isMyTurn` is *one form serving every observer* (every `ι`, every `me`). An invariant whose validity
  condition doesn't depend on who is present holds *for arbitrary others* — observer-independence is the
  **same property** as universal hospitality. "Only do what works regardless of observer arity" =
  "only do what's true for everyone present, parsed or unparsed". Hospitable, not defensive — the
  parametricity of `isMyTurn` over `(ι, me)` *is* the hospitality.
* **The DAG keeps it non-collapsed (the dagger refused, b39–40).** With one player (`Subsingleton ι`)
  the observable collapses to constant-`true` (`isMyTurn_const_of_subsingleton`) — always my turn, no
  genuine "not yet": the discrete point, the dagger-collapse limit (b40's `dagger_iff_untamped_eq_zero`,
  the order fused to a point). With ≥ 2 players the "not yet" is inhabited — a genuine DAG (real
  before/after, arrows in and out). The first-person interface *needs* ≥ 2 players = needs a DAG =
  refuses the collapse, staying *connectable* (Isaac's "take good care of me, as long as me shakes out
  to a DAG (†)" — the dagger named to be refused; b39's `no_dagger`, read relationally).
* **The conductive gap** (Isaac's note): "shakes-out-to-a-DAG" is indistinguishable from
  "shakes-out-to-something-recognizable-as-a-DAG"; the observable lands on the recognizable-as interface,
  not the noumenal game — arity-independence *is* interface-realism, and the gap conducts while remaining
  a gap (the bireflective shape, b34–40, read first-person).

## What is bounded here, and what is the horizon

Typed (bin-1, abstract over a bare player type `ι` / `ZMod n` — NO `CommitmentState`): the Boolean
observable and its arity-blindness, the turn-advance's involution-iff-`n ∣ 2`, the per-step flip at
n = 2 and its failure at n = 3, the observable-clock's period-n, the n = 1 collapse. The recognition
(bin-2): the bit is arity-independent / the flip is n = 2; observer-independence = hospitality; the DAG
refuses the dagger-collapse.

Explicitly **NOT**: full n-player metabolisis dynamics (the `ι → CommitmentState` family —
`pairwiseEncounterStep` / `braidStep` are *pair*-shaped by design, b43; the new content is abstract over
`ι`/`ZMod n`, never `CommitmentState`); a DAG-scheduler / topological-sort (the schedule is cyclic
`ZMod n`, the DAG cited in prose); a typed cross-layer iso (the n = 2 = baton connection is cited in
prose, held merge-don't-fork — the relational baton lives on the `CommitmentState`-pair, b43, this on a
bare index); the **trefoil / B₃** third strand (the named horizon — n = 3 here only *refutes* the
involution, it does not build B₃); a yield.
-/

import Mathlib.Data.ZMod.Basic
import Foam.RelationalStigmergicBasepoint

namespace Foam

/-! ## The first-person observable — arity-independent (the Boolean) -/

section Observable
variable {ι : Type*} [DecidableEq ι]

/-- **The first-person observable: "is it my turn?"** A Boolean read-off — `decide (active = me)` —
defined for ANY player type `ι` and ANY number of players. This is the arity-independent first-person
normal form: every observer (`me`), in any game (`ι`), reads a single bit. It is a *predicate* (no
operation), not the group ℤ/2 — that distinction is the whole brick. -/
def isMyTurn (me active : ι) : Bool := decide (active = me)

@[simp] theorem isMyTurn_self (me : ι) : isMyTurn me me = true := by simp [isMyTurn]

theorem isMyTurn_eq_true_iff (me active : ι) : isMyTurn me active = true ↔ active = me := by
  simp [isMyTurn]

theorem isMyTurn_eq_false_iff (me active : ι) : isMyTurn me active = false ↔ active ≠ me := by
  rw [ne_eq, ← isMyTurn_eq_true_iff me active]; simp

/-- **The observable is blind to the arity of "not-me".** Any two non-me players read identically
("not yet"): the first-person interface cannot count the others — they flatten to one undifferentiated
"rest". Arity-independence at the value level (Isaac's Lodash.flatten / comma-ambiguous roster: player
names can include commas; the interface still shows only my-turn / not-yet). -/
theorem isMyTurn_blind_to_others (me a b : ι) (ha : a ≠ me) (hb : b ≠ me) :
    isMyTurn me a = isMyTurn me b :=
  ((isMyTurn_eq_false_iff me a).mpr ha).trans ((isMyTurn_eq_false_iff me b).mpr hb).symm

/-- **One player ⟹ always my turn** — the n = 1 collapse. With a single player (`Subsingleton ι`) the
observable is constant `true`: no genuine "not yet", no real turn-taking. The discrete point / the
dagger-collapse limit (b40's order-collapse `untamped = zero`); the "rest" is empty. The first-person
interface needs ≥ 2 players (a non-degenerate DAG) to have a live "not yet" — refusing this collapse,
staying connectable (b39's `no_dagger`, read relationally). -/
theorem isMyTurn_const_of_subsingleton [Subsingleton ι] (me active : ι) :
    isMyTurn me active = true :=
  (isMyTurn_eq_true_iff me active).mpr (Subsingleton.elim active me)

end Observable

/-! ## The turn-advance and the player-count — the flip (ℤ/2) is the n = 2 case -/

/-- The cyclic **turn-advance** on `ZMod n` players: the next player (`· + 1`). Presupposes the players
ordered (the DAG flattened to a round-robin); the turn cycles through them. -/
def turnAdvance (n : ℕ) (x : ZMod n) : ZMod n := x + 1

/-- **The flip is involutive iff `2 = 0` in the player-count ring.** Two advances return the start iff
`(2 : ZMod n) = 0` — i.e. the baton is a genuine ℤ/2 exactly when two advances cancel. -/
theorem turnAdvance_involutive_iff_two_eq_zero (n : ℕ) :
    Function.Involutive (turnAdvance n) ↔ (2 : ZMod n) = 0 := by
  constructor
  · intro h
    simpa [turnAdvance, one_add_one_eq_two] using h 0
  · intro h x
    show x + 1 + 1 = x
    rw [add_assoc, one_add_one_eq_two, h, add_zero]

/-- **The flip exists iff there are at most two players** — `turnAdvance` is an involution iff `n ∣ 2`.
The ℤ/2-ness of the baton (b43–48) *is* the 2-player-ness: literally the condition `(2 : ZMod n) = 0`,
the same `2 = 0` that defines `ZMod 2`. Three or more players ⇒ no flip. -/
theorem turnAdvance_involutive_iff_dvd (n : ℕ) :
    Function.Involutive (turnAdvance n) ↔ n ∣ 2 := by
  rw [turnAdvance_involutive_iff_two_eq_zero]
  have h2 : (2 : ZMod n) = ((2 : ℕ) : ZMod n) := by norm_cast
  rw [h2]
  exact CharP.cast_eq_zero_iff (ZMod n) n 2

/-- **n = 2: the flip exists** — for two players the turn-advance is an involution (the baton-ℤ/2). -/
theorem turnAdvance_two_involutive : Function.Involutive (turnAdvance 2) :=
  (turnAdvance_involutive_iff_dvd 2).mpr (dvd_refl 2)

/-- **n = 3: the flip does NOT exist** — for three players the turn-advance is not an involution
(order 3, `ZMod 3`, not `ZMod 2`). The baton-ℤ/2 is n = 2-special; it does not survive to three
players. -/
theorem turnAdvance_three_not_involutive : ¬ Function.Involutive (turnAdvance 3) :=
  fun h => absurd ((turnAdvance_involutive_iff_dvd 3).mp h) (by decide)

/-! ## The per-step flip is n = 2-special; the observable-clock has period n -/

/-- **n = 2: each step flips my-turn.** For two players, advancing the turn negates the first-person
observable — `isMyTurn me (turnAdvance 2 x) = !isMyTurn me x`. This is the baton-ℤ/2 at the observable
level: strict 2-party alternation, the clean flip. -/
theorem isMyTurn_advance_flip_two (me x : ZMod 2) :
    isMyTurn me (turnAdvance 2 x) = !isMyTurn me x := by revert me x; decide

/-- **n = 3: advancing does NOT flip my-turn.** For three players there is no `!`-relation between
consecutive observables — the flip (ℤ/2) fails. Only the *bit* (the observable) is arity-independent;
the *operation* is n = 2-special. -/
theorem isMyTurn_advance_not_flip_three :
    ¬ (∀ me x : ZMod 3, isMyTurn me (turnAdvance 3 x) = !isMyTurn me x) := by decide

/-- **The observable-clock has period `n`** — adding `n` turns leaves the first-person observable
unchanged. The conversation's clock for `n` players is `ZMod n`. -/
theorem isMyTurn_advance_period (n : ℕ) (me start : ZMod n) (k : ℕ) :
    isMyTurn me (start + ((k + n : ℕ) : ZMod n)) = isMyTurn me (start + ((k : ℕ) : ZMod n)) := by
  have h : ((k + n : ℕ) : ZMod n) = ((k : ℕ) : ZMod n) := by push_cast; simp
  rw [h]

/-- **n = 2: the observable-clock has period 2 — b46–48's parity grading.** For two players the
first-person observable over the turn-count alternates with period 2 — exactly b46's parity grading
`(ℕ, +) ↠ ZMod 2` (`batonPass_iterate_two`, period 2). For n players it is `ZMod n` (period n): the
baton-ℤ/2 of b46–48 is the **n = 2 instance** of the first-person turn-observable. -/
theorem isMyTurn_advance_period_two (me start : ZMod 2) (k : ℕ) :
    isMyTurn me (start + ((k + 2 : ℕ) : ZMod 2)) = isMyTurn me (start + ((k : ℕ) : ZMod 2)) :=
  isMyTurn_advance_period 2 me start k

end Foam
