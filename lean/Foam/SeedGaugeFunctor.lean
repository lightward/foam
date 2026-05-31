/-
# SeedGaugeFunctor — the single-external-commitment functor, named as ONE object

## What this lands (the brick after `SeedGaugeTurnTaking.lean`)

Bricks 18–21 built the single-external-commitment functor in pieces: brick 18 (`SeedGauge`) its
**source+target** as one 4-element type (`untamped` the unit/input, `{+, −, 0}` the three outputs);
brick 19 (`SeedGaugeBooleanAlgebra`) its **category** (the native diamond Boolean algebra, composition
= refinement); brick 20 (`SeedGaugeTurn`) its **action** (`turnHom : SeedGauge →o Scope`, the single
turn = commit-then-recognize); brick 21 (`SeedGaugeTurnTaking`) its **composition** (`turnFrom`,
turn-taking as a join-action — `turnFrom_sup` / `turnFrom_comm`). But brick 21 typed the action *laws*
without **bundling** the action as a single object, and the keystone wants the functor named *as one
object*. This file bundles it.

## The recognition — three Mathlib-or-Foam facts compose

1. **A bounded join-semilattice IS a commutative (idempotent) monoid.** `SeedGauge`'s native Boolean
   algebra (brick 19) makes `(SeedGauge, ⊔, ⊥)` a `CommMonoid` — the **commitment-monoid**, whose
   *multiplication is the join of commitments* (commitments accumulate, brick 21) and whose *unit is
   the un-tamped ground* (`1 = ⊥ = untamped`, bricks 17/18). Mathlib supplies no `CommMonoid` from a
   bounded join-semilattice, so it is named here directly (`mul_eq_sup`, `one_eq_untamped`).

2. **The closed foam-states are the carrier.** A `Scope` is *closed* when it is a fixed point of
   foam's recognition-closure `convergeClosure (applyRules rules)` (brick 21's `ClosureOperator`); by
   brick 9's `convergeFrom_eq_self_iff` these are exactly the `applyRules`-closed scopes
   (`applyRules rules S ≤ S` — recognition adds nothing). This is Mathlib's `ClosureOperator.Closeds`,
   here `ClosedScope rules`. Turn-taking lands in it (`turnFrom_isClosed`, brick 21's
   `convergeFrom_idem`), so the action is internal; and the un-tamped ground `⊥` is itself a closed
   state (`isClosed_bot`, brick 9's `applyRules_lfp_bot`) — the **basepoint** the forward pass orbits.

3. **A monoid hom into `Function.End` IS a functor from the one-object commitment-category.** A monoid
   is a one-object category; a monoid homomorphism `M →* Function.End X` (the endo-maps of `X` under
   composition) is exactly a functor from `BM` into `X`'s endo-maps. So the commitment-monoid acting on
   the closed foam-states bundles as

       commitmentFunctor LP rules : SeedGauge →* Function.End (ClosedScope rules)

   — the keystone **single-external-commitment functor, at last as a single object**. `map_one'` is the
   identity action (`untamped` acts trivially on closed states — the un-tamped turn is just the
   closure, which fixes them: `commitmentAction_untamped`); `map_mul'` is composition (joining
   commitments composes turns: `commitmentAction_sup`, off brick 21's `turnFrom_sup` /
   `turnFrom_comm`). Brick 20's forward pass is its orbit of the basepoint: `commitmentFunctor_bot`
   (`(commitmentFunctor g) ⊥ = turn g`).

A small but load-bearing corollary: the commitment-monoid is **idempotent** (`g ⊔ g = g`), so the
functor's image consists of **idempotent endo-maps** (`commitmentAction_idem` — committing the same
gauge twice adds nothing; the foam already knows `g`). The functor lands in the closure-operator-like
(inflationary, idempotent) endos of the closed states — "foam retains, doesn't churn," at the level of
the action.

## What this closes

The single-external-commitment functor's arc — **source+target (18) → category (19) → action (20) →
composition (21) → bundled-as-object (22)** — is complete. The functor is one typed object. Its source
is the 4-element commitment-monoid (`untamped` the unit, `{+, −, 0}` the three commitments); its action
is turn-taking; its orbit-of-basepoint is the forward pass.

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

Pure recognition + assembly. `Function.End` / its `Monoid` / `MonoidHom` / `ClosureOperator.Closeds` /
`convergeFrom_idem` are Mathlib-or-Foam; the `CommMonoid SeedGauge` is the
bounded-join-semilattice-is-a-commutative-monoid recognition (hand-built from lattice lemmas, since
Mathlib has no off-the-shelf instance); the action laws are brick 21's `turnFrom_sup` / `turnFrom_comm`
plus the identity-on-closed (`commitmentAction_untamped`); the functor-as-object is the prose
recognition that *a monoid hom into `Function.End` is a functor*. No new geometric content — the
recognition is that the four pieces brick 18–21 typed separately ARE one object: a monoid action /
functor from the one-object commitment-category.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeFunctor` is clean, zero
sorry/warnings; depends on `SeedGauge.turnFrom` / `turnFrom_sup` / `turnFrom_comm` / `turnFrom_bot` /
`convergeClosure` / `convergeFrom_idem` (SeedGaugeTurnTaking), `SeedGauge.turn` (SeedGaugeTurn),
`SeedGauge.seed` / `seed_untamped` (SeedGaugeCommitmentLattice), `bot_eq_untamped` (SeedGaugeBooleanAlgebra),
`convergeFrom` / `convergeFrom_bot` / `convergeFrom_eq_self_iff` (PersistenceLfp), `applyRules` /
`applyRules_lfp_bot` (RecognitionApplier), and Mathlib's `Function.End` / `MonoidHom` /
`ClosureOperator.Closeds` (`Mathlib.Algebra.Group.End`, `Mathlib.Order.Closure`).)
-/

import Mathlib.Algebra.Group.End
import Foam.SeedGaugeTurnTaking

namespace Foam

/-! ## The commitment monoid — `(SeedGauge, ⊔, untamped)` is a commutative monoid -/

/-- **The commitment monoid.** `SeedGauge`'s native Boolean algebra (brick 19) makes it a bounded
    join-semilattice, hence a commutative (idempotent) monoid under `⊔` with unit `⊥`. The
    *multiplication is the join of commitments* (commitments accumulate — brick 21's turn-taking) and
    the *unit is the un-tamped ground* (`⊥ = untamped`, bricks 17/18). Mathlib supplies no `CommMonoid`
    from a bounded join-semilattice, so it is named here directly — the recognition that the static
    commitment-lattice (brick 19) IS the commitment-monoid the functor's composition (brick 21) acts
    through. -/
instance : CommMonoid SeedGauge where
  mul a b := a ⊔ b
  mul_assoc a b c := by show a ⊔ b ⊔ c = a ⊔ (b ⊔ c); rw [sup_assoc]
  one := ⊥
  one_mul a := by show ⊥ ⊔ a = a; rw [bot_sup_eq]
  mul_one a := by show a ⊔ ⊥ = a; rw [sup_bot_eq]
  mul_comm a b := by show a ⊔ b = b ⊔ a; rw [sup_comm]

/-- The commitment-monoid's multiplication **is** the join of commitments (`rfl`). Committing `a` and
    `b` in one turn is committing their join. -/
@[simp] theorem SeedGauge.mul_eq_sup (a b : SeedGauge) : a * b = a ⊔ b := rfl

/-- The commitment-monoid's unit **is** the un-tamped ground — `(1 : SeedGauge) = untamped` (brick 18's
    `bot_eq_untamped`). The empty commitment is the monoid identity. -/
@[simp] theorem SeedGauge.one_eq_untamped : (1 : SeedGauge) = SeedGauge.untamped :=
  SeedGauge.bot_eq_untamped

/-! ## The carrier — the closed foam-states -/

/-- **The closed foam-states** — the carrier the commitment-monoid acts on. A `Scope` is *closed* when
    it is a fixed point of foam's recognition-closure `convergeClosure (applyRules rules)` (brick 21);
    by brick 9's `convergeFrom_eq_self_iff` these are exactly the `applyRules`-closed scopes
    (`applyRules rules S ≤ S` — recognition adds nothing). This is Mathlib's
    `ClosureOperator.Closeds`. -/
abbrev ClosedScope (rules : RewriteRule → Prop) : Type :=
  (convergeClosure (applyRules rules)).Closeds

/-- **Closed = `applyRules`-closed** — the closure-operator fixed points are exactly the `F`-closed
    scopes (brick 9's `convergeFrom_eq_self_iff`, read through the `ClosureOperator` packaging). The
    `IsClosed` predicate is definitionally `convergeFrom (applyRules rules) S = S`. -/
theorem isClosed_iff_applyRules_le (rules : RewriteRule → Prop) (S : Scope) :
    (convergeClosure (applyRules rules)).IsClosed S ↔ applyRules rules S ≤ S :=
  convergeFrom_eq_self_iff (applyRules rules) S

/-- **The un-tamped ground is a closed state** — `⊥` is closed (`convergeFrom F ⊥ = lfp F = ⊥`, brick
    9's `applyRules_lfp_bot`). It is the **basepoint** of the action: the foam-state the functor's
    forward pass (brick 20's `turn`) orbits from — the no-commitment fixed point. -/
theorem isClosed_bot (rules : RewriteRule → Prop) :
    (convergeClosure (applyRules rules)).IsClosed (⊥ : Scope) := by
  show convergeFrom (applyRules rules) ⊥ = ⊥
  rw [convergeFrom_bot, applyRules_lfp_bot]

/-! ## The action — turn-taking on the closed foam-states -/

/-- **Turn-taking lands in the closed states** — `turnFrom LP rules S g` is closed (it is an image of
    the recognition-closure, so a fixed point of it: brick 21's `convergeFrom_idem`). So the action is
    internal to `ClosedScope`. -/
theorem SeedGauge.turnFrom_isClosed (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (S : Scope) (g : SeedGauge) :
    (convergeClosure (applyRules rules)).IsClosed (SeedGauge.turnFrom LP rules S g) :=
  convergeFrom_idem (applyRules rules) (S ⊔ g.seed LP)

/-- **The commitment-monoid's action** on the closed foam-states: commit `g` into the current closed
    state `S`, then recognize (brick 21's `turnFrom`), landing back in the closed states. This is the
    single-external-commitment functor's action, valued in the closed carrier. -/
def commitmentAction (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (g : SeedGauge) (S : ClosedScope rules) : ClosedScope rules :=
  ⟨SeedGauge.turnFrom LP rules S.val g, SeedGauge.turnFrom_isClosed LP rules S.val g⟩

/-- **The unit acts as the identity** — `commitmentAction LP rules untamped S = S` on closed `S`. The
    un-tamped turn is just the closure (`turnFrom S untamped = convergeFrom F S`), which fixes the
    already-closed states. The monoid unit `untamped = ⊥` acts trivially *exactly* on the carrier — on
    a *non*-closed `S` it would return the closure, not `S`, which is why the carrier must be the
    closed states. -/
@[simp] theorem commitmentAction_untamped (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (S : ClosedScope rules) :
    commitmentAction LP rules (⊥ : SeedGauge) S = S := by
  apply Subtype.ext
  show convergeFrom (applyRules rules) (S.val ⊔ (⊥ : SeedGauge).seed LP) = S.val
  simp only [SeedGauge.bot_eq_untamped, SeedGauge.seed_untamped, sup_bot_eq]
  exact S.property

/-- **Joining commitments composes turns** — `commitmentAction (g₁ ⊔ g₂) S = commitmentAction g₁
    (commitmentAction g₂ S)`. Committing the join in one turn equals taking the two turns in sequence
    (brick 21's `turnFrom_sup` then order-independence `turnFrom_comm`). This is the action-compatibility
    law `(g₁ * g₂) • S = g₁ • (g₂ • S)`. -/
theorem commitmentAction_sup (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (g₁ g₂ : SeedGauge) (S : ClosedScope rules) :
    commitmentAction LP rules (g₁ ⊔ g₂) S
      = commitmentAction LP rules g₁ (commitmentAction LP rules g₂ S) := by
  apply Subtype.ext
  show SeedGauge.turnFrom LP rules S.val (g₁ ⊔ g₂)
     = SeedGauge.turnFrom LP rules (SeedGauge.turnFrom LP rules S.val g₂) g₁
  rw [SeedGauge.turnFrom_sup, SeedGauge.turnFrom_comm]

/-- **Each commitment's action is idempotent** — committing the same gauge twice adds nothing:
    `commitmentAction g (commitmentAction g S) = commitmentAction g S`. The action-level shadow of
    recognition's idempotence (brick 21's `convergeFrom_idem`): the foam already knows `g`. Since the
    commitment-monoid is idempotent (`g ⊔ g = g`), the functor's image consists of idempotent endo-maps
    — the functor lands in the closure-operator-like (inflationary, idempotent) endos of the closed
    states. -/
theorem commitmentAction_idem (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (g : SeedGauge) (S : ClosedScope rules) :
    commitmentAction LP rules g (commitmentAction LP rules g S) = commitmentAction LP rules g S := by
  rw [← commitmentAction_sup, sup_idem]

/-! ## The functor as ONE object — the monoid hom into endo-maps of the closed states -/

/-- **The single-external-commitment functor, named as ONE object.** A monoid is a one-object category;
    a monoid homomorphism into `Function.End X` (the endo-maps of `X` under composition) is a functor
    from that one-object category into `X`'s endo-maps. So the commitment-monoid acting on the closed
    foam-states bundles as

        commitmentFunctor LP rules : SeedGauge →* Function.End (ClosedScope rules)

    — the keystone single-external-commitment functor, at last as a single object. `map_one'` is the
    identity action (`untamped ↦ id`, `commitmentAction_untamped`); `map_mul'` is composition
    (`g₁ ⊔ g₂ ↦ commitmentAction g₁ ∘ commitmentAction g₂`, `commitmentAction_sup`). The source
    `SeedGauge` is brick 18/19's commitment-lattice (`untamped` the unit/input, `{+, −, 0}` the three
    commitments); the action is brick 20/21's turn-taking. This closes the functor's
    source+target → category → action → composition → object arc. -/
def commitmentFunctor (LP : LedgerPersistence) (rules : RewriteRule → Prop) :
    SeedGauge →* Function.End (ClosedScope rules) where
  toFun g := commitmentAction LP rules g
  map_one' := by
    funext S
    show commitmentAction LP rules (⊥ : SeedGauge) S = S
    exact commitmentAction_untamped LP rules S
  map_mul' g₁ g₂ := by
    funext S
    show commitmentAction LP rules (g₁ ⊔ g₂) S
       = commitmentAction LP rules g₁ (commitmentAction LP rules g₂ S)
    exact commitmentAction_sup LP rules g₁ g₂ S

/-- The functor applied to a gauge `g` and a closed state `S` is the action (`rfl`, peeling the
    `MonoidHom` coercion). -/
@[simp] theorem commitmentFunctor_apply (LP : LedgerPersistence) (rules : RewriteRule → Prop)
    (g : SeedGauge) (S : ClosedScope rules) :
    commitmentFunctor LP rules g S = commitmentAction LP rules g S := rfl

/-- **The forward pass is the orbit of the un-tamped basepoint** — brick 20's single turn `turn` is the
    functor applied to `g`, evaluated at the basepoint `⊥`:
    `(commitmentFunctor LP rules g) ⊥ = turn LP rules g`. The forward pass from the un-tamped ground
    (brick 20) is the orbit of the basepoint `⊥` under the commitment-functor (brick 22) — the single
    turn is the functor acting on the no-commitment ground state. -/
theorem commitmentFunctor_bot (LP : LedgerPersistence) (rules : RewriteRule → Prop) (g : SeedGauge) :
    (commitmentFunctor LP rules g ⟨⊥, isClosed_bot rules⟩).val = SeedGauge.turn LP rules g := by
  show SeedGauge.turnFrom LP rules ⊥ g = SeedGauge.turn LP rules g
  exact SeedGauge.turnFrom_bot LP rules g

end Foam
