/-
# RelationalBatonGrading — the baton-ℤ/2 is the turn-count monoid's nontrivial grading (brick 47)

## What this file lands (brick 47, the remainder of brick 46)

Brick 46 (`RelationalMobiusParity.lean`) recognized the baton-ℤ/2 as the conversation's
**parity-grading** / Möbius half-twist, and *the relational surplus over brick 22's commitment-monoid*
`(SeedGauge, ⊔, untamped)` — but left "carries a ℤ/2 the monoid lacks" as **prose**, supported only by
the even/odd facts (`batonPass_iterate_even`/`_odd`). This file types the surplus.

## The recognition

`braidStep := batonPass ∘ turnStep`, and iterating it `n` times passes the baton `n` times. Two
substrate facts make the grading precise:

* **The turn-count monoid `(ℕ, +)` indexes braid-step composition.** `braidStep^[m + n] =
  braidStep^[m] ∘ braidStep^[n]` (`braidStep_iterate_add`, = `Function.iterate_add`) with
  `braidStep^[0] = id` (`braidStep_iterate_zero`): `n ↦ braidStep^[n]` is a monoid hom from `(ℕ, +)`
  to the endo-monoid `(Function.End _, ∘)`. The conversation's clock is `(ℕ, +)`.
* **The baton-position is the image of `n` under the parity hom `ℕ →+ ZMod 2`.** `batonPass^[n] =
  batonOfParity (n : ZMod 2)` (`batonPass_iterate_eq_batonOfParity`), where `batonOfParity` is the
  section `ZMod 2 → (baton-positions)` sending `0 ↦ id`, `1 ↦ batonPass`. So `n ↦ batonPass^[n]`
  factors as `batonOfParity ∘ parityHom`: the baton-position depends on `n` *only through* its parity.

The **parity hom is nontrivial** (`parityHom_nontrivial` : `Nat.castAddMonoidHom (ZMod 2) ≠ 0`) — it
separates even from odd. So `(ℕ, +)` carries a *nontrivial* ℤ/2-grading (the parity). And the
nontriviality is exactly the two-party content: the grading separates the baton-positions
(`batonOfParity_apply_ne_iff` : `batonOfParity 0 (s,r) ≠ batonOfParity 1 (s,r) ↔ s ≠ r`) precisely
when `s ≠ r` — *two* genuine parties, brick 46's `batonPass_eq_self_iff` read at the grading.

## The bin-1 substance — idempotent monoids carry no nontrivial grading

The contrast that makes "surplus" precise: **any monoid hom from an idempotent monoid to a group is
trivial** (`monoidHom_eq_one_of_idempotent` : if `∀ a, a * a = a` then every `f : M →* G` is `1`,
because `f a` is idempotent in a group, and the only idempotent of a group is `1`). The dividing line
is *idempotency*:

* `(ℕ, +)` is **not** idempotent (`nat_add_not_idempotent` : `1 + 1 ≠ 1`) — which is *why* it admits
  the nontrivial parity grading: the parity sees `1 + 1 = 2 ≠ 1` and flips.
* Brick 22's commitment-monoid `(SeedGauge, ⊔, untamped)` (`SeedGaugeFunctor.lean`) is a `CommMonoid`
  with `a * a = a ⊔ a = a` (`mul_eq_sup` + `sup_idem`) — **idempotent**. So
  `monoidHom_eq_one_of_idempotent` gives: every `SeedGauge →* G` is trivial. The commitment-monoid
  carries **no** nontrivial ℤ/2-grading. *(Cited in prose, held merge-don't-fork — this file imports
  only the relational side and the generic algebra, not the seed-gauge side.)*

So the baton-ℤ/2 — the parity quotient `(ℕ, +) ↠ ZMod 2` — is the gradeable structure on the *index
monoid* that the *commitment monoid* structurally cannot carry. **The surplus, typed.**

## Brick 45's fixed-vs-moving partner, read one level out

This is brick 45's *fixed-vs-moving partner* read at the **composition-monoid** level. The relational
braid composes by feed-forward over a *moving* partner (`braidStep_braidStep` feeds the *updated*
state forward), and that composition is indexed by `(ℕ, +)` — a monoid with non-idempotent elements,
hence *gradeable* (the parity / alternation). The seed-gauge recognizes against a *fixed* rule-set,
and its commitments *accumulate* by the idempotent join `⊔` (brick 22) — order-free, *ungradeable*.
The moving partner makes the composition **alternate** (parity-graded `(ℕ, +)`); the fixed partner
makes it **accumulate** (idempotent, ungraded). The baton-ℤ/2 is the fingerprint of the former.

## What is bounded here, and what is the horizon

Typed (bin-1, over `RelationalMobiusParity.lean` / `RelationalBraid.lean` + generic algebra + Mathlib's
`Nat.castAddMonoidHom` / `ZMod`): the `(ℕ, +)`-indexing of composition, the parity hom and its
nontriviality, the baton-position as the image under it, the off-diagonal separation, and the generic
idempotent-monoid → trivial-grading lemma. The recognition (bin-2): the baton-ℤ/2 is the
turn-count monoid's nontrivial grading, the relational surplus over the idempotent commitment-monoid,
brick 45's fixed-vs-moving partner read at the composition-monoid.

Explicitly **NOT**: importing the seed-gauge side / a typed iso between the two composition-monoids
(held merge-don't-fork — the idempotent-triviality is stated *generically*, SeedGauge cited in prose);
the **trefoil / B₃** third strand (the named horizon — the baton-ℤ/2 is its symmetric/abelian shadow,
the parity quotient of the non-abelian braid grading); iterating `braidStep` to a *state*-convergence
fixed point (construction-grade — this file grades only the baton, never the states); a yield.
-/

import Mathlib.Data.ZMod.Basic
import Foam.RelationalMobiusParity

namespace Foam

universe u

/-! ## The bin-1 substance — an idempotent monoid carries no nontrivial grading

These are generic facts of algebra (no relational content): a monoid hom from an idempotent monoid
to a group is trivial. They are stated **generically** and cited in prose for `SeedGauge` (brick 22),
held merge-don't-fork — this file does not import the seed-gauge side. -/

/-- **From an idempotent monoid, every group-valued hom is pointwise trivial.** If every element of
`M` is idempotent (`a * a = a`), then for any group `G` and hom `f : M →* G`, `f a = 1`: the image
`f a` is idempotent in `G` (`f a * f a = f (a * a) = f a`), and the only idempotent of a group is the
identity (cancel `f a` on the left). -/
theorem monoidHom_apply_eq_one_of_idempotent {M G : Type*} [Monoid M] [Group G]
    (hidem : ∀ a : M, a * a = a) (f : M →* G) (a : M) : f a = 1 := by
  have h : f a * f a = f a * 1 := by rw [mul_one, ← map_mul, hidem]
  exact mul_left_cancel h

/-- **An idempotent monoid carries only the trivial grading.** Every monoid hom `f : M →* G` from an
idempotent monoid to a group is the trivial hom `1` — there is no nontrivial group-grading. The
contrast that makes the baton-ℤ/2 a genuine *surplus*: brick 22's commitment-monoid `(SeedGauge, ⊔,
untamped)` is idempotent (`a ⊔ a = a`), so this gives `every SeedGauge →* G is trivial` — no
nontrivial ℤ/2-grading — while the turn-count monoid `(ℕ, +)` (not idempotent) has the parity. -/
theorem monoidHom_eq_one_of_idempotent {M G : Type*} [Monoid M] [Group G]
    (hidem : ∀ a : M, a * a = a) (f : M →* G) : f = 1 :=
  MonoidHom.ext fun a =>
    (monoidHom_apply_eq_one_of_idempotent hidem f a).trans (MonoidHom.one_apply a).symm

/-- **The turn-count monoid `(ℕ, +)` is not idempotent** — `1 + 1 ≠ 1`. This is *why* it escapes
`monoidHom_eq_one_of_idempotent` and carries the nontrivial parity grading: a non-idempotent element
(here `1`) is exactly what a grading can *see*. The dividing line between `(ℕ, +)` (graded) and the
commitment-monoid (ungraded) is idempotency. -/
theorem nat_add_not_idempotent : ∃ a : ℕ, a + a ≠ a := ⟨1, by decide⟩

/-! ## The parity hom — the turn-count monoid's nontrivial ℤ/2-grading -/

/-- The **parity hom** — the turn-count monoid's ℤ/2-grading, `ℕ →+ ZMod 2`, `n ↦ (n : ZMod 2)`
(even/odd parity). The baton-position factors through this (`batonPass_iterate_eq_batonOfParity`). -/
abbrev parityHom : ℕ →+ ZMod 2 := Nat.castAddMonoidHom (ZMod 2)

@[simp] theorem parityHom_apply (n : ℕ) : parityHom n = (n : ZMod 2) := rfl

/-- **The parity hom is nontrivial** — it is not the zero (trivial) grading: its value at the single
turn `1` is `1 ≠ 0` in `ZMod 2`. So `(ℕ, +)` carries a genuine ℤ/2-grading (unlike the idempotent
commitment-monoid, `monoidHom_eq_one_of_idempotent`). -/
theorem parityHom_nontrivial : parityHom ≠ 0 := by
  intro h
  have h1 : (1 : ZMod 2) = 0 := by
    have := DFunLike.congr_fun h 1
    rwa [parityHom_apply, Nat.cast_one, AddMonoidHom.zero_apply] at this
  exact one_ne_zero h1

/-! ## The turn-count monoid indexes braid-step composition -/

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- **The unit** — `braidStep^[0] = id`: zero turns is the identity. With `braidStep_iterate_add`,
`n ↦ braidStep^[n]` is a monoid hom from `(ℕ, +)` to the endo-monoid `(Function.End _, ∘)`. -/
theorem braidStep_iterate_zero :
    (braidStep (𝕜 := 𝕜) (E := E))^[0] = id := rfl

/-- **The turn-count monoid `(ℕ, +)` indexes composition** — `braidStep^[m + n] = braidStep^[m] ∘
braidStep^[n]`. Iterating `braidStep` is a monoid hom `(ℕ, +) → (Function.End _, ∘)`; the
conversation's clock is the additive monoid of natural numbers. -/
theorem braidStep_iterate_add (m n : ℕ) :
    (braidStep (𝕜 := 𝕜) (E := E))^[m + n] = braidStep^[m] ∘ braidStep^[n] :=
  Function.iterate_add (braidStep (𝕜 := 𝕜) (E := E)) m n

/-! ## The baton-position is the image of `n` under the parity hom -/

/-- `(n : ZMod 2) = 0 ↔ Even n` — the parity value is `0` exactly on even turn-counts. -/
theorem natCast_zmod_two_eq_zero_iff (n : ℕ) : (n : ZMod 2) = 0 ↔ Even n := by
  rw [CharP.cast_eq_zero_iff (ZMod 2) 2 n]
  exact even_iff_two_dvd.symm

/-- The baton-position as a function of the **parity value alone** — `id` at `0`, `batonPass` at `1`.
The section `ZMod 2 → (baton-positions)` through which `n ↦ batonPass^[n]` factors: the baton-position
is the *image of `n` under the parity hom* `ℕ →+ ZMod 2` (`batonPass_iterate_eq_batonOfParity`). -/
def batonOfParity (z : ZMod 2) :
    CommitmentState 𝕜 E × CommitmentState 𝕜 E → CommitmentState 𝕜 E × CommitmentState 𝕜 E :=
  if z = 0 then id else batonPass

@[simp] theorem batonOfParity_zero :
    batonOfParity (𝕜 := 𝕜) (E := E) 0 = id := by
  unfold batonOfParity; rw [if_pos rfl]

@[simp] theorem batonOfParity_one :
    batonOfParity (𝕜 := 𝕜) (E := E) 1 = batonPass := by
  unfold batonOfParity; rw [if_neg (by decide)]

/-- **The baton-position is the image of `n` under the parity hom.** `batonPass^[n] = batonOfParity
(n : ZMod 2)`: the baton after `n` handoffs depends on `n` only through its parity `(n : ZMod 2)`,
realized by the section `batonOfParity`. So `n ↦ batonPass^[n]` = `batonOfParity ∘ parityHom` — the
baton-ℤ/2 is the turn-count monoid's parity grading, made literal (brick 46's `id`/`batonPass`-by-
parity packaged as a factoring through `ℕ →+ ZMod 2`). -/
theorem batonPass_iterate_eq_batonOfParity (n : ℕ) :
    (batonPass (𝕜 := 𝕜) (E := E))^[n] = batonOfParity (n : ZMod 2) := by
  unfold batonOfParity
  rcases Nat.even_or_odd n with h | h
  · rw [batonPass_iterate_even h, if_pos ((natCast_zmod_two_eq_zero_iff n).mpr h)]
  · rw [batonPass_iterate_odd h,
        if_neg (fun hz => (Nat.not_even_iff_odd.mpr h) ((natCast_zmod_two_eq_zero_iff n).mp hz))]

/-- **The grading separates the baton-positions exactly off the diagonal — exactly when you and me are
genuinely two.** `batonOfParity 0 (s,r) ≠ batonOfParity 1 (s,r) ↔ s ≠ r`: the parity grading
distinguishes the even baton (`(s,r)`) from the odd baton (`(r,s)`) precisely when `s ≠ r` (two
distinct parties). This is brick 46's `batonPass_eq_self_iff` read at the grading: the nontriviality
of the baton-ℤ/2 IS the two-party `you + me` content (brick 41/45's moving partner). -/
theorem batonOfParity_apply_ne_iff (s r : CommitmentState 𝕜 E) :
    batonOfParity (0 : ZMod 2) (s, r) ≠ batonOfParity (1 : ZMod 2) (s, r) ↔ s ≠ r := by
  rw [batonOfParity_zero, batonOfParity_one, id_eq, ne_eq, ne_eq, not_iff_not]
  exact eq_comm.trans (batonPass_eq_self_iff s r)

end Foam
