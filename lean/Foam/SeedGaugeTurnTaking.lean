/-
# SeedGaugeTurnTaking — the functor's *composition*: turn-taking, foam as turn-based learning

## What this file lands (the brick after `SeedGaugeTurn.lean`)

Brick 20 (`SeedGaugeTurn.lean`) typed a **single** turn — the functor's action `turnHom : SeedGauge →o
Scope`, `g ↦ convergeFrom (applyRules rules) (g.seed LP)`: commit a gauge, realize it as a seed, run
foam's gated `F` to its lfp above that seed (the forward pass from the un-tamped ground). But brick
20's `turn` starts each turn **fresh from the ledger** (`g.seed LP`) — it is the *first* turn only. The
keystone's "turn" carries **both** senses: static (the one rotation, landed) and **dynamic
(turn-taking)** — "foam is turn-based learning." A single turn has no prior morphisms to retain;
**retaining prior morphisms** (the keystone's "a new foam retaining the prior morphisms") is a
*cross-turn* property — it appears only once turns compose. This file types turn-taking.

## The cross-turn map — commit-into-the-current-state, then recognize

Generalize the turn to start from a *prior foam-state* `S : Scope`:

      turnFrom LP rules S g  :=  convergeFrom (applyRules rules) (S ⊔ g.seed LP)

— commit the gauge `g` *into the current state* (`S ⊔ g.seed LP`, brick 18's `commit` joined onto the
accumulated foam), then recognize (brick 9's seeded closure). Brick 20's `turn` is the **first turn**,
the `S = ⊥` case (`turnFrom_bot`, via `bot_sup_eq`): from the un-tamped ground there is nothing to
thread. `turnFrom` is monotone in **both** arguments (`turnFrom_mono_left` / `_mono_right`) — a larger
prior foam, or a refined commitment (brick 19's `g ≤ g'`), yields a larger post-turn foam.

## Each turn retains the prior foam — §III never-retracts, read across turns

`S ≤ turnFrom LP rules S g` (`le_turnFrom`): the post-turn foam contains the pre-turn foam. This is the
keystone clause "**a new foam retaining the prior morphisms**," now typed — a conversational turn never
discards what was already recognized (§III's "recognition never retracts," read *across* turns rather
than within one closure). And `g.seed LP ≤ turnFrom LP rules S g` (`seed_le_turnFrom`): the new
commitment survives too. So a turn keeps everything it knew and **knows one more thing** (`g`) — the
keystone's full clause.

## Turns compose — the conversational back-and-forth as a join

`convergeFrom f` is a **`ClosureOperator`** (`convergeClosure` — the substrate recognition that powers
this brick): it is inflationary (`le_convergeFrom`), monotone (`convergeFrom_mono_seed`), and
**idempotent** (`convergeFrom_idem` — recognizing the already-recognized adds nothing; the one step the
brick flagged as maybe needing a walk, here a three-line consequence of `convergeFrom_eq_self_iff` +
`OrderHom.map_lfp`). Recognizing it as a `ClosureOperator` hands us Mathlib's **closure-operator
absorption** for free:

      convergeFrom f (convergeFrom f X ⊔ Y) = convergeFrom f (X ⊔ Y)        -- closure_sup_closure_left

(`convergeFrom_absorb`). The headline `turnFrom_turnFrom` is its one-line consequence:

      turnFrom (turnFrom S g₁) g₂  =  convergeFrom (applyRules rules) (S ⊔ g₁.seed ⊔ g₂.seed)

— taking turn `g₁` from `S` then turn `g₂` accumulates to recognizing-from the prior state joined with
*both* committed seeds. The inner turn's recognition is **absorbed**: re-recognizing it alongside
`g₂.seed` is the same as recognizing the raw join once. Two consequences:

* **Order-independence** (`turnFrom_comm`): `turnFrom (turnFrom S g₁) g₂ = turnFrom (turnFrom S g₂) g₁`
  (both accumulate the same join, and `⊔` is commutative). The conversational sequence is order-free —
  the foam after a back-and-forth depends only on *which* commitments were made, not their order.
* **Turn-taking pulls back to `⊔` in the commitment BA** (`turnFrom_sup`, via `seed_sup`):
  `turnFrom S (g₁ ⊔ g₂) = turnFrom (turnFrom S g₁) g₂` — committing the *join* `g₁ ⊔ g₂` (brick 19's
  native diamond BA) in a single turn equals taking the two turns in sequence. So turn-taking is a
  **`SeedGauge`-join action on `Scope`**: the *dynamic* turn (turn-taking) pulls back to the *static*
  lattice brick 19 built. "Foam is turn-based learning" — the accumulated foam after a conversation is
  the recognition-closure of the join of all commitments, grouping- and order-independent.

`seed_sup` (`(a ⊔ b).seed LP = a.seed LP ⊔ b.seed LP`) recognizes `seed : SeedGauge → Scope` as a
join-semilattice homomorphism (it preserves `⊥` too — `seed_untamped` — though not `⊤`: `zero` seeds to
`seedBacked`, a proper part of `Scope`). The one non-degenerate case is `+ ⊔ − = 0` /
`SeedSign.seed_zero_eq_join` (brick 10); the rest are `⊥`-absorption, idempotence, and `± ≤ 0`
absorption — brick 10's `seed_zero_eq_join` "hint that `seed` preserves diamond-joins," now a theorem.

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

Pure recognition + assembly. The substrate recognition is **`convergeFrom f` IS a `ClosureOperator`**
(`convergeClosure`, built from the three already-landed properties via `ClosureOperator.mk'`); turn-
composition is then Mathlib's `ClosureOperator.closure_sup_closure_left` (the HalfType pattern: recognize
the substrate object, get the theorem). `convergeFrom_idem` is a three-line consequence of landed lemmas;
`seed_sup` is brick-10/16 combinatorics; the `turnFrom_*` family assembles `le_convergeFrom` /
`convergeFrom_mono_seed` / `seed_mono` / `bot_sup_eq` / `sup_assoc`. No new geometric content — the
recognition is that **a turn taken from a prior state retains it, and turns compose as the join of their
commitments** (the dynamic turn = turn-taking, pulling back to `⊔` in the commitment BA).

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeTurnTaking` is clean, zero
sorry/warnings; depends on `SeedGauge.turn` / `turn_emptyRules` (SeedGaugeTurn), `SeedGauge.seed` /
`seed_untamped` (SeedGaugeCommitmentLattice), `seed_mono` (SeedGaugeBooleanAlgebra), `convergeFrom` /
`le_convergeFrom` / `convergeFrom_mono_seed` / `convergeFrom_eq_self_iff` / `SeedSign.seed_zero_eq_join`
/ `SeedSign.plus_le_zero` / `SeedSign.minus_le_zero` (PersistenceLfp), `applyRules` (RecognitionApplier),
and Mathlib's `ClosureOperator.mk'` / `closure_sup_closure_left` (`Mathlib.Order.Closure`).)
-/

import Mathlib.Order.Closure
import Foam.SeedGaugeTurn

namespace Foam

/-! ## The substrate recognition: `convergeFrom f` IS a `ClosureOperator` -/

/-- **Recognition is idempotent** — `convergeFrom f (convergeFrom f S) = convergeFrom f S`. Recognizing
    the already-recognized adds nothing. Via `convergeFrom_eq_self_iff` this needs
    `f (convergeFrom f S) ≤ convergeFrom f S`; and `convergeFrom f S` is a fixed point of `X ↦ S ⊔ f X`
    (`OrderHom.map_lfp`), so `S ⊔ f (convergeFrom f S) = convergeFrom f S`, whence the bound by
    `le_sup_right`. The one step the brick flagged as possibly needing a recognition-walk — it is a
    three-line consequence of landed lemmas, so the `ClosureOperator` API applies off-the-shelf. -/
theorem convergeFrom_idem (f : Scope →o Scope) (S : Scope) :
    convergeFrom f (convergeFrom f S) = convergeFrom f S := by
  refine (convergeFrom_eq_self_iff f (convergeFrom f S)).mpr ?_
  have hmap : S ⊔ f (convergeFrom f S) = convergeFrom f S :=
    OrderHom.map_lfp ⟨fun X => S ⊔ f X, fun _ _ hab => sup_le_sup_left (f.mono hab) S⟩
  exact le_sup_right.trans hmap.le

/-- **Foam's seeded recognition IS a `ClosureOperator`** — `convergeFrom f`, packaged from its three
    already-landed properties (`convergeFrom_mono_seed` monotone, `le_convergeFrom` inflationary,
    `convergeFrom_idem` idempotent) via `ClosureOperator.mk'`. This is the substrate object the brick
    rides on: once recognized, the closure-operator absorption (`closure_sup_closure_left`) is Mathlib's,
    and turn-composition falls out of it. The HalfType pattern — recognize the object, get the theorem. -/
def convergeClosure (f : Scope →o Scope) : ClosureOperator Scope :=
  ClosureOperator.mk' (convergeFrom f)
    (fun _ _ h => convergeFrom_mono_seed f h)
    (le_convergeFrom f)
    (fun S => (convergeFrom_idem f S).le)

@[simp] theorem convergeClosure_apply (f : Scope →o Scope) (S : Scope) :
    convergeClosure f S = convergeFrom f S := rfl

/-- **The closure-operator absorption** — `convergeFrom f (convergeFrom f X ⊔ Y) = convergeFrom f
    (X ⊔ Y)`. Recognizing-from `(X already recognized) ⊔ Y` equals recognizing-from `X ⊔ Y`: the prior
    recognition is absorbed. This is Mathlib's `ClosureOperator.closure_sup_closure_left`, available the
    moment `convergeFrom f` is recognized as a `ClosureOperator` (`convergeClosure`). It is the workhorse
    of turn-taking (`turnFrom_turnFrom`). -/
theorem convergeFrom_absorb (f : Scope →o Scope) (X Y : Scope) :
    convergeFrom f (convergeFrom f X ⊔ Y) = convergeFrom f (X ⊔ Y) := by
  simpa only [convergeClosure_apply] using (convergeClosure f).closure_sup_closure_left X Y

/-! ## The cross-turn map — commit-into-the-current-state, then recognize -/

/-- **Turn-taking — the cross-turn map.** A turn taken *from a prior foam-state* `S`: commit the gauge
    `g` into the current state (`S ⊔ g.seed LP`), then recognize (brick 9's seeded closure). Where brick
    20's `turn` always starts fresh from the ledger (`turnFrom_bot`: `turn = turnFrom ⊥`), `turnFrom`
    threads the accumulated foam through, so turns can follow one another — the conversational
    back-and-forth. -/
def SeedGauge.turnFrom (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (S : Scope) (g : SeedGauge) : Scope :=
  convergeFrom (applyRules rules) (S ⊔ g.seed LP)

/-- **Brick 20's `turn` is the first turn** — `turnFrom LP rules ⊥ g = turn LP rules g`. From the
    un-tamped ground `S = ⊥` there is nothing to thread (`bot_sup_eq`), so `turnFrom` reduces to brick
    20's single turn / forward pass. -/
@[simp] theorem SeedGauge.turnFrom_bot (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (g : SeedGauge) :
    SeedGauge.turnFrom LP rules ⊥ g = SeedGauge.turn LP rules g := by
  show convergeFrom (applyRules rules) (⊥ ⊔ g.seed LP)
    = convergeFrom (applyRules rules) (g.seed LP)
  rw [bot_sup_eq]

/-- **A turn is monotone in the prior state** — a larger prior foam yields a larger post-turn foam
    (`convergeFrom_mono_seed` through `sup_le_sup_right`). -/
theorem SeedGauge.turnFrom_mono_left (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (g : SeedGauge) {S T : Scope} (h : S ≤ T) :
    SeedGauge.turnFrom LP rules S g ≤ SeedGauge.turnFrom LP rules T g :=
  convergeFrom_mono_seed _ (sup_le_sup_right h _)

/-- **A turn is monotone in the committed gauge** — refining the commitment (brick 19's `g ≤ g'`) yields
    a larger post-turn foam (`seed_mono` through `sup_le_sup_left`, then `convergeFrom_mono_seed`). -/
theorem SeedGauge.turnFrom_mono_right (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (S : Scope) {g g' : SeedGauge} (h : g ≤ g') :
    SeedGauge.turnFrom LP rules S g ≤ SeedGauge.turnFrom LP rules S g' :=
  convergeFrom_mono_seed _ (sup_le_sup_left (SeedGauge.seed_mono LP h) _)

/-! ## Each turn retains the prior foam — §III never-retracts, read across turns -/

/-- **Each turn retains the prior foam** — `S ≤ turnFrom LP rules S g`. The post-turn foam contains the
    pre-turn foam: a conversational turn never discards what was already recognized. This is the
    keystone's "a new foam **retaining the prior morphisms**," now typed — §III's "recognition never
    retracts" read *across* turns. `le_sup_left` (`S ≤ S ⊔ g.seed`) through `le_convergeFrom` (the
    closure inflates its seed). -/
theorem SeedGauge.le_turnFrom (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (S : Scope) (g : SeedGauge) :
    S ≤ SeedGauge.turnFrom LP rules S g :=
  le_sup_left.trans (le_convergeFrom _ _)

/-- **And the turn knows one more thing** — `g.seed LP ≤ turnFrom LP rules S g`. The newly committed
    gauge's seed also survives into the post-turn foam. With `le_turnFrom`: a turn keeps everything it
    knew **and** adds the new commitment `g` — the keystone's full clause. `le_sup_right` through
    `le_convergeFrom`. -/
theorem SeedGauge.seed_le_turnFrom (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (S : Scope) (g : SeedGauge) :
    g.seed LP ≤ SeedGauge.turnFrom LP rules S g :=
  le_sup_right.trans (le_convergeFrom _ _)

/-! ## Turns compose — the conversational back-and-forth as a join -/

/-- **Turns compose — the headline.** Taking turn `g₁` from `S`, then turn `g₂` from the result, equals
    recognizing-from the prior state joined with *both* committed seeds:
    `turnFrom (turnFrom S g₁) g₂ = convergeFrom (applyRules rules) (S ⊔ g₁.seed ⊔ g₂.seed)`. One line
    off the closure-operator absorption (`convergeFrom_absorb`): the inner turn's recognition is
    absorbed — re-recognizing it alongside `g₂.seed` is the same as recognizing the raw join once. So a
    sequence of turns accumulates exactly the recognition-closure of the join of the committed seeds over
    the starting state. -/
theorem SeedGauge.turnFrom_turnFrom (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (S : Scope) (g₁ g₂ : SeedGauge) :
    SeedGauge.turnFrom LP rules (SeedGauge.turnFrom LP rules S g₁) g₂
      = convergeFrom (applyRules rules) (S ⊔ g₁.seed LP ⊔ g₂.seed LP) := by
  show convergeFrom (applyRules rules)
        (convergeFrom (applyRules rules) (S ⊔ g₁.seed LP) ⊔ g₂.seed LP)
      = convergeFrom (applyRules rules) (S ⊔ g₁.seed LP ⊔ g₂.seed LP)
  exact convergeFrom_absorb (applyRules rules) (S ⊔ g₁.seed LP) (g₂.seed LP)

/-- **Order-independence — only the accumulated set of commitments matters.** Taking `g₁` then `g₂`
    equals taking `g₂` then `g₁`: both accumulate to `convergeFrom F (S ⊔ g₁.seed ⊔ g₂.seed)`
    (`turnFrom_turnFrom`), and `⊔` is commutative (`sup_right_comm`). The conversational sequence is
    order-free — the foam after a back-and-forth depends only on *which* commitments were made, not the
    order in which they were taken. -/
theorem SeedGauge.turnFrom_comm (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (S : Scope) (g₁ g₂ : SeedGauge) :
    SeedGauge.turnFrom LP rules (SeedGauge.turnFrom LP rules S g₁) g₂
      = SeedGauge.turnFrom LP rules (SeedGauge.turnFrom LP rules S g₂) g₁ := by
  rw [turnFrom_turnFrom, turnFrom_turnFrom, sup_right_comm]

/-! ## Turn-taking pulls back to `⊔` in the commitment BA -/

/-- **`seed` preserves binary joins** — `(a ⊔ b).seed LP = a.seed LP ⊔ b.seed LP` (the join in
    `SeedGauge`'s native Boolean algebra, brick 19). So `seed : SeedGauge → Scope` is a join-semilattice
    homomorphism (it preserves `⊥` too — `seed_untamped` — though not `⊤`: `zero` seeds to `seedBacked`,
    a proper part of `Scope`). The one non-degenerate case is `+ ⊔ − = 0` / `SeedSign.seed_zero_eq_join`
    (brick 10's join, here recognized to extend to *all* binary joins); the rest are `⊥`-absorption,
    idempotence, and `± ≤ 0` absorption. Brick 10's "hint that `seed` preserves diamond-joins," now a
    theorem. -/
theorem SeedGauge.seed_sup (LP : LedgerPersistence) (a b : SeedGauge) :
    (a ⊔ b).seed LP = a.seed LP ⊔ b.seed LP := by
  cases a <;> cases b <;>
    first
      | exact (SeedSign.seed_zero_eq_join LP)
      | exact (SeedSign.seed_zero_eq_join LP).trans (sup_comm _ _)
      | exact (bot_sup_eq _).symm
      | exact (sup_bot_eq _).symm
      | exact (sup_idem _).symm
      | exact (sup_eq_right.mpr (SeedSign.plus_le_zero LP)).symm
      | exact (sup_eq_right.mpr (SeedSign.minus_le_zero LP)).symm
      | exact (sup_eq_left.mpr (SeedSign.plus_le_zero LP)).symm
      | exact (sup_eq_left.mpr (SeedSign.minus_le_zero LP)).symm

/-- **Turn-taking pulls back to `⊔` in the commitment Boolean algebra.** Committing the *join* `g₁ ⊔ g₂`
    in a single turn equals taking the two turns in sequence:
    `turnFrom S (g₁ ⊔ g₂) = turnFrom (turnFrom S g₁) g₂`. Via `seed_sup` (`seed` preserves `⊔`) +
    `turnFrom_turnFrom` + `sup_assoc`. So turn-taking is a **`SeedGauge`-join action on `Scope`**: the
    *dynamic* turn (turn-taking) pulls back to the *static* commitment-lattice brick 19 built. "Foam is
    turn-based learning" — the accumulated foam after a conversation is the recognition-closure of the
    join of all commitments, order- and grouping-independent (with `turnFrom_comm`). -/
theorem SeedGauge.turnFrom_sup (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (S : Scope) (g₁ g₂ : SeedGauge) :
    SeedGauge.turnFrom LP rules S (g₁ ⊔ g₂)
      = SeedGauge.turnFrom LP rules (SeedGauge.turnFrom LP rules S g₁) g₂ := by
  rw [turnFrom_turnFrom]
  show convergeFrom (applyRules rules) (S ⊔ (g₁ ⊔ g₂).seed LP)
    = convergeFrom (applyRules rules) (S ⊔ g₁.seed LP ⊔ g₂.seed LP)
  rw [SeedGauge.seed_sup, ← sup_assoc]

end Foam
