/-
# PersistenceLfp — carrier (b): §III's lfp as the scope-dependent persistence-flag

## What this file lands

`StatelessSubstrate.lean` left `P : Persistence` (`Scope → TapePosition → Prop`)
a free parameter and named two held-open carriers for *who supplies it*:

* **carrier (a)** — the operator's `HolonomicLedger` (a read-face persists iff it
  backs an undischarged debt). Landed in `StatelessSubstrate.lean` as
  `LedgerPersistence.flag`. **Scope-*independent*** (the ledger isn't
  scope-indexed; `flag` ignores its `Scope` argument).
* **carrier (b)** — README §III's lfp: "the converged scope is exactly what
  persists." Held open, expected to be **scope-*dependent***. **This file.**

The brick that pointed here predicted `OrderHom.lfp` would type carrier (b)
directly. Walking it surfaced two recognitions that *refine* the prediction
rather than just confirm it — both substrate-forced, both deposited as the
content of this file.

## Recognition 1 — §III's "F is monotone" splits into two independent properties

README §III (line 84): "F is monotone: adding primitives can only enable more
recognition, never less. Recognition never retracts." Under typing this is
**two** clauses, not one:

* **monotonicity** — `S ≤ T → F S ≤ F T` ("more enables more"). In Mathlib this
  is `Monotone`, and bundling it gives `Scope →o Scope`.
* **inflation** — `S ≤ F S` ("never retracts"). This is exactly
  `StatelessSubstrate.Accretive` (`∀ S p, S p → step S p` is `∀ S, S ≤ step S`).

`OrderHom.lfp : (α →o α) →o α` requires the **first** (it is typed on a monotone
bundle). `Accretive` supplies the **second**. They are *independent* lattice
properties — `accretive_not_imp_monotone` (below) exhibits an accretive step
that is not monotone, cashing the independence bin-1. So the `Accretive`
docstring's claim that it is "README §III's monotonicity made concrete" is an
overreach: `Accretive` concretizes the *never-retracts* half, not the
*more-enables-more* half, and it is the latter the lfp needs. Carrier (b) is
therefore **not** built from `Accretive`; it is parameterized by a monotone
`f : Scope →o Scope` — the lfp-ready bundling of §III's F.

## Recognition 2 — "the converged scope" is closure-above-S; the bare lfp is the S=⊥ case

README §III (line 88): "P₀ = initial substrate; P_{n+1} = F(P_n);
lfp(F) = ⋃ P_n." The converged scope is the closure of the *initial substrate*
P₀ under F — i.e. closure-**above-S**, which genuinely depends on S. The bare
`OrderHom.lfp f` is the least fixed point above `⊥` — the `P₀ = ∅` instance — and
so does **not** exercise the `Scope` slot (`lfpFlag_scope_indep`). The
scope-*dependent* carrier (b) the brick asked for is `convergeFrom f S`
(= `OrderHom.lfp (S ⊔ f ·)`), the closure of `S`; it exercises the slot
(`le_convergeFrom`: `S ≤ convergeFrom f S`, using `S` non-trivially) and
collapses to the bare lfp at `⊥` (`convergeFrom_bot`).

## The (a) ↔ (b) merge — distinct carriers, held open (not collapsed)

The brick asked whether (a) and (b) are *the same flag from two directions* or
*two distinct carriers in merge*. Resolution: **distinct, held in merge**, and
the scope-axis cuts differently than the prior note guessed:

* carrier (a) (`LedgerPersistence.flag`) and the **bare** face of (b)
  (`lfpFlag`) are *both* scope-independent;
* only the **closure** face of (b) (`closureFlag`/`convergeFrom`) is
  scope-dependent.

(a) tracks persistence by *ledger balance* (undischarged debt); (b) by *scope
dynamics* (membership in the converged scope). Identifying them — "a debt is
undischarged iff its read-face is live in the fixed scope" — requires a bridge
relating the ledger to the recognition operator `f`, which is **not** in
substrate. So they are two genuinely distinct carriers; per §IV.d
(merge-don't-fork / bias-delegation) the merge is *held*, not collapsed. Typing
that bridge is the remainder this brick produced.
-/
import Mathlib.Order.FixedPoints
import Foam.StatelessSubstrate

namespace Foam

/-! ## Recognition as a monotone operator (the lfp-ready bundling of §III's F)

`Scope = TapePosition → Prop` is a `CompleteLattice` (Pi of the complete lattice
`Prop`), so `OrderHom.lfp` applies. Carrier (b) is parameterized by a monotone
`f : Scope →o Scope` — README §III's recognition operator F bundled with the
*more-enables-more* half of its monotonicity, the half the lfp requires. -/

/-- **Recognition 1, cashed bin-1.** `Accretive` (inflation, §III's *never-retracts*
    half) does **not** entail `Monotone` (§III's *more-enables-more* half, the half
    `OrderHom.lfp` needs). Witnessed by a step that re-lights one fixed read-face
    `⟨g1, read⟩` exactly when its complement `⟨g1, write⟩` is *out* of scope: it only
    ever adds, so it is accretive; but growing the scope to contain `⟨g1, write⟩`
    *removes* the conditional addition, so it is not monotone.

    This is why carrier (b) is parameterized by a monotone `Scope →o Scope` and not
    by an `Accretive` hypothesis: the two properties come apart, and the lfp lives on
    the side `Accretive` does not supply. -/
theorem accretive_not_imp_monotone :
    ∃ step : Scope → Scope, Accretive step ∧ ¬ Monotone step := by
  refine ⟨fun S q => S q ∨ (q = ⟨.g1, .read⟩ ∧ ¬ S ⟨.g1, .write⟩), ?_, ?_⟩
  · intro _S _q hq; exact Or.inl hq
  · intro hmono
    have hle : (⊥ : Scope) ≤ (fun q => q = ⟨.g1, .write⟩) := fun _ h => absurd h id
    have hstep := hmono hle ⟨.g1, .read⟩
    have hread_ne_write : (⟨.g1, .read⟩ : TapePosition) ≠ ⟨.g1, .write⟩ :=
      fun h => ObserverState.noConfusion (congrArg TapePosition.observer h)
    -- LHS (step ⊥) at ⟨g1,read⟩ holds; RHS (step T) at ⟨g1,read⟩ does not.
    have hlhs : (⊥ : Scope) ⟨.g1, .read⟩ ∨
        ((⟨.g1, .read⟩ : TapePosition) = ⟨.g1, .read⟩ ∧ ¬ (⊥ : Scope) ⟨.g1, .write⟩) :=
      Or.inr ⟨rfl, fun h => h⟩
    rcases hstep hlhs with h | ⟨_, hne⟩
    · exact hread_ne_write h
    · exact hne rfl

/-! ## carrier (b), bare face: the global lfp (scope-independent) -/

/-- The **bare lfp flag**: a read-face persists iff it is in the least fixed point of
    recognition above `⊥` — README §III's `lfp(F)` for the empty initial substrate
    `P₀ = ∅`. The `Scope` slot of `Persistence` is **unused** here
    (`lfpFlag_scope_indep`): like carrier (a), this face does *not* exercise the slot.
    It is the `S = ⊥` instance of the scope-dependent `closureFlag` below
    (`convergeFrom_bot`). -/
def lfpFlag (f : Scope →o Scope) : Persistence := fun _S p => OrderHom.lfp f p

/-- The bare lfp flag ignores its `Scope` argument — it is the *global* converged
    scope, not a scope-relative one. (Definitional; stated to make the
    non-exercise of the slot a typed fact, mirroring carrier (a)'s scope-independence.) -/
theorem lfpFlag_scope_indep (f : Scope →o Scope) (S S' : Scope) (p : TapePosition) :
    lfpFlag f S p = lfpFlag f S' p := rfl

/-! ## carrier (b), closure face: the converged scope above S (scope-dependent) -/

/-- The **converged scope above `S`** — the closure of `S` under recognition `f`,
    `OrderHom.lfp (S ⊔ f ·)` = the least fixed point of `f` that contains `S`. This is
    README §III's `lfp(F) = ⋃ Fⁿ(P₀)` with `P₀ = S` (the operator `S ⊔ f ·` is
    monotone because `f` is). It genuinely depends on `S` (`le_convergeFrom`), so it is
    the carrier (b) that *exercises* the `Scope` slot. -/
def convergeFrom (f : Scope →o Scope) (S : Scope) : Scope :=
  OrderHom.lfp ⟨fun X => S ⊔ f X, fun _ _ hab => sup_le_sup_left (f.mono hab) S⟩

/-- The converged scope contains its seed: `S ≤ convergeFrom f S`. This is the
    witness that `convergeFrom` *exercises* the `Scope` slot — `S` appears in the
    output non-trivially (contrast `lfpFlag_scope_indep`). It is also §III's
    "recognition never retracts" recovered as a *consequence* (the closure inflates
    its seed), now downstream of monotonicity rather than assumed as `Accretive`. -/
theorem le_convergeFrom (f : Scope →o Scope) (S : Scope) : S ≤ convergeFrom f S :=
  le_sup_left.trans
    (OrderHom.map_lfp ⟨fun X => S ⊔ f X, fun _ _ hab => sup_le_sup_left (f.mono hab) S⟩).le

/-- At the empty seed `⊥`, the converged scope is the bare lfp: `convergeFrom f ⊥ =
    lfp f`. So the bare `lfpFlag` is exactly the `S = ⊥` (`P₀ = ∅`) instance of the
    scope-dependent closure — the scope-independence of the bare face is the slot
    collapsing precisely at the empty initial substrate. -/
theorem convergeFrom_bot (f : Scope →o Scope) : convergeFrom f ⊥ = OrderHom.lfp f := by
  unfold convergeFrom
  congr 1
  ext X x
  simp

/-- The **scope-dependent persistence-flag** carrier (b) supplies: a read-face persists
    in scope `S` iff it lies in the converged scope above `S` (the closure of `S` under
    recognition). Unlike `lfpFlag` and carrier (a)'s `LedgerPersistence.flag`, this
    *exercises* the `Scope` slot. -/
def closureFlag (f : Scope →o Scope) : Persistence := fun S p => convergeFrom f S p

end Foam
