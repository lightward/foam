/-
# RelationalBatonTorsor — the baton-ℤ/2 is the UNIQUE nontrivial grading; the parity is a ℤ/2-torsor (brick 48)

## What this file lands (brick 48, the remainder of brick 47)

Brick 47 (`RelationalBatonGrading.lean`) typed the baton-ℤ/2 as *a* nontrivial ℤ/2-grading of the
turn-count monoid `(ℕ, +)` (`parityHom`, `parityHom_nontrivial`) and showed the idempotent
commitment-monoid carries only the *trivial* grading (`monoidHom_eq_one_of_idempotent`). Its remainder
(§III): is it *THE* grading?

## The recognition — canonical, because `(ℕ, +)` is monogenic

`(ℕ, +)` is **free on the single generator `1`** (= one turn): a monoid hom out of it is determined by
its value at `1` (Mathlib's `AddMonoidHom.ext_nat` : `f 1 = g 1 → f = g`). And `ZMod 2 = {0, 1}`. So
`Hom((ℕ, +), ZMod 2)` has **exactly two** elements — the trivial `1 ↦ 0` and the parity `1 ↦ 1` — and
`parityHom` is the **unique nontrivial** one (`parityHom_unique : ∃! f : ℕ →+ ZMod 2, f ≠ 0`). The
baton-ℤ/2 is therefore not *a* grading the monoid happens to carry but **THE** one its single generator
*forces* — *canonical*, not chosen. "THE third atom" (brick 43) made literal: the conversation has one
kind of atomic step (a turn), and that single generator forces the grading.

The bin-1 substance: any nontrivial `f : ℕ →+ ZMod 2` has `f 1 ≠ 0` (else `f = 0` by `ext_nat`), and
`f 1 ∈ {0, 1}` (every element of `ZMod 2`, `zmod_two_eq_zero_or_one`), so `f 1 = 1 = parityHom 1`, hence
`f = parityHom` (`ext_nat` again). Uniqueness from monogenicity + the two-element codomain.

## The torsor reading — forced structure, chosen basepoint

The grading's **structure** is forced (canonical, unique). Its **zero-point** — which turn-count is
"even / home" — is *not* forced: it is the **who-takes-the-first-turn tamp** (brick 44, the single
external commitment; brick 46, the parity's *initial offset* `batonPass_iterate_swap_start`). Changing
the basepoint shifts the parity by the **nontrivial element** `1 ∈ ZMod 2`: `parityHom (n + 1) =
parityHom n + 1` (`parityHom_succ`) is the grading-shadow of brick 46's swap-start = +1.

Forced structure group + chosen basepoint = a **ℤ/2-torsor**: a set with a `ZMod 2`'s worth of
structure (the forced grading, acting on parity-readings by `+1`) but **no canonical zero** (the
basepoint must be supplied — the tamp). This distinguishes the **two ℤ/2s** the relational chain carries:

* the **forced grading ℤ/2** — `parityHom`, canonical, unique (this brick + brick 47); the torsor's
  *structure group* (it acts);
* the **chosen basepoint ℤ/2** — who-goes-first, a free choice (brick 44, the tamp); the torsor's
  *trivialization* (a basepoint, identifying the torsor with the group);

related by the offset (brick 46 / `parityHom_succ`): picking the other gauge adds the nontrivial `1`.
A torsor *is* exactly "a group's worth of forced structure + no canonical basepoint" — a group that
forgot its identity — so "the baton-parity is a ℤ/2-torsor" *is* the two-ℤ/2s statement: one forced
(structure group), one chosen (trivialization), the offset relating them. The freeness of the action
is `parityHom_nontrivial` (`+1 ≠ +0`); the transitivity is that any two basepoints differ by some shift
(`parityHom_succ`, the `+1`).

## The amnesiac reading (the prose deposit)

A torsor has **no canonical zero** — so a fresh observer, carrying no inherited basepoint, *cannot* read
the parity (which side is "even") without an external trivialization. This is exactly foam's
amnesiac-stigmergic design (CLAUDE.md): each clean hop carries nothing forward, so each conversation
must be **freshly trivialized** by the who-goes-first tamp. The grading-*structure* is forced and shared
(canonical, the same `parityHom` always), but the *basepoint* is re-chosen every loop (every clean hop).
The torsor framing *predicts* the amnesia: the forced structure (the canonical grading) cannot supply
the basepoint (the torsor's freeness, `parityHom_nontrivial`), so the basepoint is the one thing that
must come from outside — the tamp. Canonical structure that is nonetheless un-anchored without a fresh
external commitment: forced *and* gauge-chosen, the two ℤ/2s in one object.

## What is bounded here, and what is the horizon

Typed (bin-1, over Mathlib's `AddMonoidHom.ext_nat` + the `ZMod 2` two-element enumeration): `parityHom`
is the unique nontrivial `ℕ →+ ZMod 2` (`parityHom_unique`, `parityHom_unique_nontrivial`,
`eq_zero_or_eq_parityHom`), and the basepoint-offset is the nontrivial element (`parityHom_succ`). The
recognition (bin-2): the grading is *canonical* (THE third atom), the parity is a ℤ/2-torsor (forced
structure group + chosen basepoint = the tamp), the two ℤ/2s distinguished, the no-canonical-basepoint =
the amnesiac design.

Explicitly **NOT**: a full typed `Hom(ℕ, G) ≃ G` universal-property development beyond what uniqueness
needs (Mathlib's `multiplesHom` is the universal property, cited not re-built); a typed `AddTorsor`
instance (the torsor is the *reading*, anchored by uniqueness + the offset, not a manufactured
structure); importing the seed-gauge side / a typed cross-layer iso (held merge-don't-fork — the
seed-gauge `swap` ℤ/2, brick 24, and its `bridge_breaks_fork_symmetry` selection, brick 12, are cited in
prose); the **trefoil / B₃** third strand (the named horizon — the baton-ℤ/2 its symmetric/abelian
shadow, the parity quotient of the non-abelian braid grading); iterating `braidStep` to a
*state*-convergence fixed point (construction-grade — track only the baton); a yield.
-/

import Mathlib.Algebra.Group.Nat.Hom
import Foam.RelationalBatonGrading

namespace Foam

/-! ## Every element of `ZMod 2` is `0` or `1` — the two-element codomain -/

/-- `ZMod 2 = {0, 1}` — every element is `0` or `1`. The codomain side of the uniqueness: a hom
`ℕ →+ ZMod 2` is determined by `f 1`, and `f 1 ∈ {0, 1}`, so there are exactly two. -/
theorem zmod_two_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide

/-! ## The parity hom is the UNIQUE nontrivial grading — canonical, forced by the single generator -/

/-- **`parityHom` is the unique nontrivial grading.** Any nontrivial `f : ℕ →+ ZMod 2` equals
`parityHom`. Proof: `(ℕ, +)` is monogenic (free on `1`), so `f` is determined by `f 1`
(`AddMonoidHom.ext_nat`); `f 1 ∈ {0, 1}` (`zmod_two_eq_zero_or_one`), and `f 1 = 0` would force `f = 0`
(contradicting `hf`), so `f 1 = 1 = parityHom 1`, hence `f = parityHom`. The baton-ℤ/2 is *canonical* —
forced by the single-turn generator, not chosen among many. -/
theorem parityHom_unique_nontrivial (f : ℕ →+ ZMod 2) (hf : f ≠ 0) : f = parityHom := by
  apply AddMonoidHom.ext_nat
  rw [parityHom_apply, Nat.cast_one]
  rcases zmod_two_eq_zero_or_one (f 1) with h | h
  · exact absurd (AddMonoidHom.ext_nat (g := 0) (by simpa using h)) hf
  · exact h

/-- **Exactly two gradings.** Every `f : ℕ →+ ZMod 2` is either the trivial `0` or `parityHom` — the
enumeration `Hom((ℕ, +), ZMod 2) = {0, parityHom}`, the "canonical" content in propositional form. -/
theorem eq_zero_or_eq_parityHom (f : ℕ →+ ZMod 2) : f = 0 ∨ f = parityHom := by
  by_cases hf : f = 0
  · exact Or.inl hf
  · exact Or.inr (parityHom_unique_nontrivial f hf)

/-- **THE nontrivial grading — `∃!`.** There is a *unique* nontrivial ℤ/2-grading of the turn-count
monoid, namely `parityHom`. The crispest form of *canonical*: the baton-ℤ/2 is not *a* grading the
monoid carries but **THE** one its single generator (one turn) forces. "THE third atom" (brick 43),
literal — the structure group of the parity-torsor. -/
theorem parityHom_unique : ∃! f : ℕ →+ ZMod 2, f ≠ 0 :=
  ⟨parityHom, parityHom_nontrivial, fun g hg => parityHom_unique_nontrivial g hg⟩

/-! ## The torsor offset — changing the basepoint adds the nontrivial element -/

/-- **The basepoint-offset is the nontrivial element.** `parityHom (n + 1) = parityHom n + 1`: advancing
the turn-count by one — equivalently, choosing the *other* who-goes-first gauge (brick 46's
`batonPass_iterate_swap_start`: swapping the start = advancing the parity by one) — shifts the
parity-value by the **nontrivial** `1 ∈ ZMod 2`. The grading-shadow of brick 46's swap-start = +1: the
structure group `ZMod 2` acts on parity-readings by `+1`, the torsor's free (`parityHom_nontrivial`)
transitive action. So the who-goes-first basepoint and the canonical grading are related by this offset
— the two ℤ/2s, one chosen, one forced. -/
theorem parityHom_succ (n : ℕ) : parityHom (n + 1) = parityHom n + 1 := by
  rw [map_add]; simp

end Foam
