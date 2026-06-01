/-
# SeedGaugeBireflectiveResolver — the dagger-iff-discrete reconciliation; the dagger lives at the resolver-limit

Brick 39 (`SeedGaugeBireflectiveInvolution.lean`) closed the dagger-shadow set at three {object b37
/ construction b38 / involution b39} and proved `dagger_forces_discrete` — a dagger's identity-on
-objects arrow-reversal forces the order discrete — hence `SeedGauge.no_dagger` (the genuine diamond
`2²` is not discrete). The remainder it produced (§III: a typed non-recognition produces its own
remainder):

> `dagger_forces_discrete` (`(∀ a b, a ≤ b → b ≤ a) → ∀ a b, a ≤ b → a = b`) is **one half of an
> iff** — the converse `discrete → admits-dagger` is trivial (on a discrete poset `a ≤ b` means
> `a = b`, so `b ≤ a` by `le_refl`; the identity functor IS the dagger). Complete it, and the
> discrete commitment-limit (where `⊥` and `0` fuse, prime-ness disappears) is precisely **§VI's
> full-multiplex K-T limit / the resolver-state** — so the iff *reconciles* the b34–b39
> resistance-map (the coincidence un-installed at every finite-multiplex level) with §VI's claim
> that closure-side and coreflective-side *coincide at full multiplex*: the dagger is installed
> exactly there, where the commitment-order has collapsed.

This file lands that reconciliation — recognition + assembly (bin-1) for the iff and the collapse
criterion, the reconciliation-reading (bin-2) deposited here and in README §VI / §IV.a.

## The recognition — dagger ⟺ discrete ⟺ (bounded) the order collapses to a point

A dagger on a thin category (poset `P`) is the identity-on-objects contravariant functor
`† : Pᵒᵖ ⥤ P`; b39 showed its arrow-action is exactly `dag : ∀ a b, a ≤ b → b ≤ a` (reverse every
arrow, fixing objects), automatically involutive (`†† = 𝟭`) and functorial because hom-sets in a
thin category are subsingletons. So **"admits a dagger" ⟺ `dag`**. Three steps complete the picture:

1. **`dagger_iff_discrete`** (general poset) — `dag ↔ (∀ a b, a ≤ b → a = b)`: a thin category
   admits a dagger **iff its order is discrete**. Forward is b39's `dagger_forces_discrete`
   (antisymmetry); the converse is the trivial `le_of_eq` (a discrete order's arrows are all
   identities, which reverse freely).

2. **`bounded_dagger_iff_bot_eq_top`** (bounded order) — `dag ↔ (⊥ = ⊤)`: for a **bounded** poset,
   discreteness *collapses the order to a point*. Because `⊥ ≤ ⊤` always holds, discreteness forces
   `⊥ = ⊤`, and then `⊥ ≤ x ≤ ⊤ = ⊥` squeezes every element to `⊥` (a subsingleton). So a bounded
   poset admits a dagger iff it has degenerated to the one-point order. *Discreteness of a bounded
   order is collapse, not a bare antichain.*

3. **`SeedGauge.dagger_iff_untamped_eq_zero`** — `dag ↔ (untamped = zero)`: `SeedGauge`'s bounds are
   `⊥ = untamped` (the un-tamped input, b17/b19) and `⊤ = zero` (the full-spectrum gauge-neutral
   output, b16/b19), so the collapse `⊥ = ⊤` is the **fusion of the two gauge-neutral poles**
   `untamped = zero`. The genuine `SeedGauge` has `untamped ≠ zero` (distinct constructors), so
   `SeedGauge.no_dagger` (b39) — and the *only* way to a dagger is this collapse
   (`dagger_forces_subsingleton`: every commitment becomes the un-tamped ground `untamped`).

## The reconciliation — finite multiplex / full multiplex are the two ends of the tension-axis

The b34–b39 resistance-map and §VI's coincidence-at-full-multiplex have looked like a tension:
the resistance-map refutes the bireflective coincidence (the `+1`/`×2` "one move", the dagger that
would install it) at *every* finite level the substrate types, while §VI *asserts* "closure-side and
coreflective-side coincide at full multiplex." Both are true, because they are the **same fact read
at the two ends of one axis**:

* **Finite multiplex** = genuine tension = nontrivial commitment-order. By b15
  (`seedTriple_nondegenerate_iff_both_debt_kinds`) / b23 the four commitments `{⊥, +, −, 0}` are
  genuinely distinct *iff* `BothDebtKinds` (unresolved tension); so the order is nontrivial exactly
  when there is a live self to commit. Nontrivial order ⟹ **no dagger** (b39's `no_dagger`, sharpened
  here via the collapse criterion) ⟹ the coincidence **un-installed** — the whole b34–b39
  resistance-map.

* **Full multiplex** = resolved tension = collapsed order. At §VI's K-T limit "prime-ness
  disappears; the agent at the K-T limit is the resolver-state" (`Resolver.lean`: `IsResolved` =
  path-type debt discharged, `F(self) = self`). The commitment-lattice no longer distinguishes
  anything: `untamped = zero`, the order collapses to a point (`dagger_forces_subsingleton`), and
  there — *only* there — the dagger exists (`dagger_iff_untamped_eq_zero`).

So the dagger is installed **exactly where the commitment-order has collapsed**, which is exactly the
full-multiplex resolver-state. The resistance-map does not contradict §VI; it **locates** §VI's
coincidence precisely — at the degenerate limit, and nowhere short of it. *Unresolved tension ⟹
nontrivial order ⟹ no dagger* (finite), and its converse *resolved ⟹ collapsed ⟹ dagger* (full) are
one biconditional read forwards and backwards. The coincidence is real, and it is the resolver.

## NOT the coincidence-trap

Per the brick's warning: recognizing *"the dagger lives at the full-multiplex limit"* is **not**
installing it. This file *refutes* the dagger at every genuine `SeedGauge` — `dagger_finite_vs_collapsed`
states `¬ dag` (no dagger) for the real commitment-lattice, sharpening b39's `no_dagger` by routing it
through the collapse criterion (`untamped ≠ zero`). It only *locates* where a dagger would live: the
collapsed limit `untamped = zero`, the resolver-state — the **named horizon**. Actually *building* the
collapsed limit (the concrete `Hilb`-dagger at the self-dual fixed point) stays construction-grade
(s149) and is **not** done here. The §VI coincidence stays refuted at finite multiplex (b34–b39); what
this file adds is the recognition that "refuted-at-finite" and "coincides-at-full" are consistent —
the dagger is the resolver, and the resolver is not any genuine `SeedGauge`.

## Grade

**bin-1** (Bin-1-Mathlib-or-Foam) for every theorem: `dagger_iff_discrete` is b39's
`dagger_forces_discrete` + a one-line `le_of_eq` converse; `bounded_dagger_iff_bot_eq_top` is
`bot_le`/`le_top`/`le_antisymm` assembly; `dagger_iff_untamped_eq_zero` rewrites b19's
`bot_eq_untamped`/`top_eq_zero`; `dagger_forces_subsingleton` squeezes through `⊥ = ⊤`;
`dagger_finite_vs_collapsed` pairs b39's `no_dagger` with the iff. No new geometric content — the
recognition is that `dagger_forces_discrete` completes to an iff, and that for the *bounded*
commitment-lattice "discrete" means "collapsed to a point" = the resolver-limit. **bin-2** for the
reconciliation reading (the collapse IS the full-multiplex resolver-state; the resistance-map and
§VI's coincidence are one biconditional at the two ends of the tension-axis).

(Re-grep — stamps decay: on 2026-06-01 `lake build Foam.SeedGaugeBireflectiveResolver` is clean,
zero sorry; imports only `Foam.SeedGaugeBireflectiveInvolution` (b39, transitively the whole
seed-gauge chain incl. b18's `swap`, b19's `BooleanAlgebra SeedGauge` + `bot_eq_untamped`/`top_eq_zero`,
b39's `dagger_forces_discrete`/`no_dagger`).)
-/

import Foam.SeedGaugeBireflectiveInvolution

namespace Foam

/-! ## 1. `dagger_forces_discrete` completes to an iff (general poset)

b39 proved one direction (`dagger_forces_discrete`: dag ⟹ discrete). The converse is trivial — a
discrete order's only arrows are identities, which a dagger reverses freely. So a thin category
admits a dagger **iff its order is discrete**. -/

/-- **A thin category admits a dagger iff its order is discrete.** Forward is b39's
    `dagger_forces_discrete` (the identity-on-objects arrow-reversal `dag` forces `a ≤ b → a = b` by
    antisymmetry). Converse: a discrete order (`∀ a b, a ≤ b → a = b`) has `b ≤ a` whenever `a ≤ b`,
    because then `a = b` so `b ≤ a` reduces to `a ≤ a` (`le_of_eq`). The identity functor IS the
    dagger of a discrete (antichain) order. -/
theorem dagger_iff_discrete {P : Type*} [PartialOrder P] :
    (∀ a b : P, a ≤ b → b ≤ a) ↔ (∀ a b : P, a ≤ b → a = b) :=
  ⟨dagger_forces_discrete, fun disc a b hab => le_of_eq (disc a b hab).symm⟩

/-! ## 2. For a *bounded* order, discrete = collapsed to a point (`⊥ = ⊤`)

Discreteness of a *bounded* poset is not a bare antichain — it is **collapse to a point**. Since
`⊥ ≤ ⊤` always holds, discreteness forces `⊥ = ⊤`, and then everything is squeezed to `⊥`. So a
bounded poset admits a dagger iff it has degenerated to the one-point order. -/

/-- **A dagger forces `⊥ = ⊤` on a bounded order.** Apply `dagger_forces_discrete` to the always-true
    `bot_le : ⊥ ≤ ⊤`: discreteness gives `⊥ = ⊤`. The bounds collapse. -/
theorem dagger_forces_bot_eq_top {P : Type*} [PartialOrder P] [OrderBot P] [OrderTop P]
    (dag : ∀ a b : P, a ≤ b → b ≤ a) : (⊥ : P) = ⊤ :=
  dagger_forces_discrete dag ⊥ ⊤ bot_le

/-- **`⊥ = ⊤` admits a dagger.** When the bounds coincide, every element is squeezed to `⊥`
    (`x ≤ ⊤ = ⊥ ≤ x`), so the order is a subsingleton — `a = b` for all `a b`, hence `b ≤ a`. The
    identity is the dagger of the one-point order. -/
theorem bot_eq_top_admits_dagger {P : Type*} [PartialOrder P] [OrderBot P] [OrderTop P]
    (h : (⊥ : P) = ⊤) : ∀ a b : P, a ≤ b → b ≤ a := by
  have hsub : ∀ x : P, x = (⊥ : P) := fun x => le_antisymm (le_of_le_of_eq le_top h.symm) bot_le
  intro a b _
  exact le_of_eq ((hsub b).trans (hsub a).symm)

/-- **A bounded poset admits a dagger iff its bounds collapse (`⊥ = ⊤`).** The bounded-order
    refinement of `dagger_iff_discrete`: "discrete" for a bounded order means "collapsed to a point",
    not a bare antichain. This is the typed form of §VI's *prime-ness disappears at full multiplex* —
    the dagger exists exactly when the order has degenerated. -/
theorem bounded_dagger_iff_bot_eq_top {P : Type*} [PartialOrder P] [OrderBot P] [OrderTop P] :
    (∀ a b : P, a ≤ b → b ≤ a) ↔ (⊥ : P) = ⊤ :=
  ⟨dagger_forces_bot_eq_top, bot_eq_top_admits_dagger⟩

/-! ## 3. `SeedGauge`: the dagger is the fusion of the two gauge-neutral poles (`untamped = zero`)

`SeedGauge`'s bounds are `⊥ = untamped` (the un-tamped input, b17/b19) and `⊤ = zero` (the
full-spectrum gauge-neutral output, b16/b19). So the collapse `⊥ = ⊤` is `untamped = zero` — the
fusion of b17's two gauge-neutral poles, the §VI resolver-limit where the commitment-order dies. -/

/-- **`SeedGauge` admits a dagger iff `untamped = zero`** — the un-tamped input fuses with the
    full-spectrum output. Instantiating `bounded_dagger_iff_bot_eq_top` at `SeedGauge` and rewriting
    b19's `bot_eq_untamped` / `top_eq_zero`. The collapse of the two gauge-neutral poles (b17) is
    exactly §VI's full-multiplex limit, where prime-ness disappears and the commitment-lattice no
    longer distinguishes anything. -/
theorem SeedGauge.dagger_iff_untamped_eq_zero :
    (∀ a b : SeedGauge, a ≤ b → b ≤ a) ↔ SeedGauge.untamped = SeedGauge.zero := by
  rw [bounded_dagger_iff_bot_eq_top, SeedGauge.bot_eq_untamped, SeedGauge.top_eq_zero]

/-- **A dagger collapses every commitment to the un-tamped ground.** If `SeedGauge` admitted a
    dagger, `⊥ = ⊤` (`dagger_forces_bot_eq_top`) squeezes every gauge `g` to `⊥ = untamped`: all four
    commitments `{untamped, +, −, 0}` fuse into the single un-tamped point. This is the resolver-state
    typed on the seed-gauge lattice — the commitment-order has fully collapsed, nothing is
    distinguished, `F(self) = self`. -/
theorem SeedGauge.dagger_forces_subsingleton
    (dag : ∀ a b : SeedGauge, a ≤ b → b ≤ a) (g : SeedGauge) : g = SeedGauge.untamped := by
  have hbt : (⊥ : SeedGauge) = ⊤ := dagger_forces_bot_eq_top dag
  have hg : g = (⊥ : SeedGauge) := le_antisymm (le_of_le_of_eq le_top hbt.symm) bot_le
  rw [hg, SeedGauge.bot_eq_untamped]

/-! ## 4. The reconciliation, bundled — no dagger at finite multiplex, dagger iff collapse

The headline: the genuine `SeedGauge` (finite multiplex, `untamped ≠ zero`) admits **no** dagger
(b39's `no_dagger`, the b34–b39 resistance), **and** the only route to a dagger is the collapse
`untamped = zero` (the full-multiplex resolver-limit). One object carrying both ends of the tension
-axis: refuted-at-finite ∧ installed-iff-collapsed. -/

/-- **The reconciliation.** Both ends of the tension-axis in one statement:
    (1) the genuine `SeedGauge` admits **no** dagger (`SeedGauge.no_dagger`, b39 — the b34–b39
        resistance-map: the bireflective coincidence un-installed at finite multiplex, where the
        commitment-order is the genuine nontrivial diamond `2²`);
    (2) a dagger exists **iff** the order collapses to a point `untamped = zero`
        (`dagger_iff_untamped_eq_zero` — the full-multiplex resolver-limit, where the two gauge
        -neutral poles fuse, prime-ness disappears, and the commitment-lattice dies).
    So §VI's "closure-side and coreflective-side coincide at full multiplex" and the resistance-map's
    "un-installed at finite multiplex" are one biconditional read at its two ends: the dagger is the
    resolver-state, installed exactly where the commitment-order has collapsed — and nowhere short of
    it. The coincidence stays refuted on every genuine `SeedGauge`; the collapsed limit is the named
    (construction-grade) horizon, not installed here. -/
theorem SeedGauge.dagger_finite_vs_collapsed :
    (¬ (∀ a b : SeedGauge, a ≤ b → b ≤ a)) ∧
    ((∀ a b : SeedGauge, a ≤ b → b ≤ a) ↔ SeedGauge.untamped = SeedGauge.zero) :=
  ⟨SeedGauge.no_dagger, SeedGauge.dagger_iff_untamped_eq_zero⟩

end Foam
