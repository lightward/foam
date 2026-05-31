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
relating the ledger to the recognition operator `f`. That bridge is now typed
(below, "The (a) ↔ (b) bridge — typed, and its sign is gauge"):
`LedgerRecognitionBridge LP f`, on the `DesarguesianWitness` template. Walking it
landed the resolution — **the bridge has a sign, and the sign is gauge.** Nothing
in `LP` fixes which way recognition points; two ledger-built operators bracket
the choice — `recognizeUndischarged` (lfp = carrier (a) *exactly*, coincidence)
and `recognizeDischarged` (lfp *complementary* to carrier (a)). Committing which
is `F` is gauge-fixing, the single external commitment / the tamp. So per §IV.d
(merge-don't-fork / bias-delegation) the merge stays held — the carriers are
neither the same flag nor plain negations until the observer fixes the gauge.
The remainder is now sharper: *which gauge does foam's concrete `F` commit to.*
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

/-- **The closure realizes its seed exactly iff the seed is `f`-closed.**
    `convergeFrom f S = S` precisely when `S` is a prefixed point of `f` (`f S ≤ S`).

    * `←` if `f S ≤ S` then `S ⊔ f S = S`, so `S` is a fixed point of the closure
      operator `X ↦ S ⊔ f X` and the lfp sits at `S` (`OrderHom.lfp_le`), giving
      `convergeFrom f S ≤ S`; `le_convergeFrom` is the other half.
    * `→` the lfp is a fixed point (`OrderHom.map_lfp`), so
      `S ⊔ f (convergeFrom f S) = convergeFrom f S`; substituting the hypothesis
      `convergeFrom f S = S` yields `S ⊔ f S = S`, i.e. `f S ≤ S`.

    This is the hinge for reading the *seed's* gauge (`RecognitionApplier.lean`,
    "Seeded from the ledger"): it cleaves "does the closure equal the seed?" — a
    fixed-point property of the `(step, seed)` pair, blind to any ledger — from
    "what gauge does the seed carry?". So any gauge the seeded closure realizes is
    sourced from the seed, never manufactured by the step; whether realization is
    *exact* (closure `=` seed-gauge) or merely a *lower bound* (closure `⊋`
    seed-gauge) is decided here, gauge-independently, by `f`-closedness. -/
theorem convergeFrom_eq_self_iff (f : Scope →o Scope) (S : Scope) :
    convergeFrom f S = S ↔ f S ≤ S := by
  constructor
  · intro h
    have hmap : S ⊔ f (convergeFrom f S) = convergeFrom f S :=
      OrderHom.map_lfp ⟨fun X => S ⊔ f X, fun _ _ hab => sup_le_sup_left (f.mono hab) S⟩
    rw [h] at hmap
    exact sup_eq_left.mp hmap
  · intro h
    refine le_antisymm ?_ (le_convergeFrom f S)
    exact OrderHom.lfp_le
      ⟨fun X => S ⊔ f X, fun _ _ hab => sup_le_sup_left (f.mono hab) S⟩
      (sup_le le_rfl h)

/-- The **scope-dependent persistence-flag** carrier (b) supplies: a read-face persists
    in scope `S` iff it lies in the converged scope above `S` (the closure of `S` under
    recognition). Unlike `lfpFlag` and carrier (a)'s `LedgerPersistence.flag`, this
    *exercises* the `Scope` slot. -/
def closureFlag (f : Scope →o Scope) : Persistence := fun S p => convergeFrom f S p

/-! ## The (a) ↔ (b) bridge — typed, and its sign is gauge

The merge block above named the remainder the two-carrier merge produced:
*relating carrier (a)'s undischarged-debt flag to carrier (b)'s lfp needs a
bridge from the ledger to the recognition operator `f`, which is not in
substrate.* This block types that bridge — and walking it lands a recognition
sharper than the merge anticipated: **the bridge has a sign, and the sign is
gauge** (observer-supplied), not substrate-fixed.

Both carriers in play are scope-independent (the brick's recognition): carrier
(a) `LedgerPersistence.flag` ignores its `Scope`, and the bare lfp `lfpFlag`
does too (`lfpFlag_scope_indep`). So the well-posed bridge is `(a) ↔ lfpFlag`
(both constant in `S`), **not** `(a) ↔ closureFlag` (type-incompatible: the
closure face grows with `S`). The bridge asks: does "`p` backs an undischarged
debt" coincide with "`p ∈ OrderHom.lfp f`"?

**The ledger does not fix `f`.** A `HolonomicLedger` carries a *static*
partition of debts into discharged / undischarged (`Discharged`), but it does
not say which way a recognition operator built over it *points*. Two natural
ledger-built operators bracket the choice — they differ only in which side of
the partition recognition accretes:

* `recognizeUndischarged` — accrete the **still-owed** read-faces. Its bare lfp
  is *exactly* carrier (a): `LP.flag = lfpFlag (recognizeUndischarged LP)`
  (`flag_eq_lfpFlag_recognizeUndischarged`). **Coincidence** — README §V's "a
  debt is undischarged iff its read-face is live in the fixed scope," now a
  theorem at this gauge.
* `recognizeDischarged` — accrete the **settled** read-faces. Its bare lfp is
  the discharged-backing set, which is **complementary** to carrier (a): under
  `holds`-injectivity, on any debt-backed face `lfp ↔ ¬ LP.flag`
  (`lfp_iff_not_flag_of_injective`), and coincidence is outright *impossible*
  there (`not_coincide_recognizeDischarged_of_injective`).

So the *sign* of the (a) ↔ (b) relation — coincide vs. complement — is fixed by
which operator the observer commits to as `F`. The ledger-geometry alone is
sign-free; committing the gauge is the **single external commitment / the tamp**
(README §IV.a, §VIII): generation and uncertainty in one act. This is why the
merge stayed held distinct — the two carriers are neither the same flag nor
plain negations until a gauge is fixed, and the gauge is the observer's.

**Grade.** The bridge over an arbitrary `f` is bin-2, observer-supplied
(`LedgerRecognitionBridge`, on the `DesarguesianWitness` template). It is
*discharged for free at the `recognizeUndischarged` gauge*
(`LedgerRecognitionBridge.ofRecognizeUndischarged`, bin-1 — the substrate fills
the slot, as `DesarguesianWitness` is inhabited when `L = Sub(D, V)`) and
*refuted at the `recognizeDischarged` gauge*
(`not_bridge_recognizeDischarged_of_injective`). The remainder is therefore not
"is there a bridge" (there is, at one gauge) but "which gauge does foam's
*concrete* `F` commit to." **Answered in `RecognitionApplier.lean`:** foam's `F`
(the `applyRules` rewrite-applier) is sign-*neutral*. It is *gated* (a rule fires
only when its whole read-triple is in scope) where these toy operators are
*ungated* (`S ↦ S ⊔ Q`), so its bare lfp is `⊥` (`applyRules_lfp_bot`: nothing fires
from nothing) — it equals neither gauge and never reads `Discharged`. Hence
`LedgerRecognitionBridge LP (applyRules rules)` is inhabited **iff the ledger is
fully discharged** (`nonempty_bridge_applyRules_iff`), i.e. only where carrier (a)
is itself `⊥`. So the gauge is the tamp — observer-supplied at the ledger, in the
gap between rule-firing and discharge-status — and the bridge stays **bin-2** in
foam proper. **Refined once more** (RecognitionApplier's "Seeded from the ledger"):
the bare lfp is `⊥` only because `P₀ = ∅`; running the applier from a *seed*
(`convergeFrom`, the carrier-(b) closure below) localizes the tamp precisely — `F`
is sign-neutral, so the gauge enters through the **seed `P₀`**, and the
undischarged-vs-discharged seed-choice is this very coincide/complement fork
relocated from the step to the initial substrate. -/

/-- Recognition built over the ledger that accretes the **undischarged**-backing
    read-faces — "hold open what is still owed." Of the form `S ↦ S ⊔ Q` with `Q`
    the still-owed set, hence monotone. Its bare lfp is exactly carrier (a)
    (`flag_eq_lfpFlag_recognizeUndischarged`): the gauge at which the two carriers
    **coincide** (README §V's phrasing). -/
def recognizeUndischarged (LP : LedgerPersistence) : Scope →o Scope where
  toFun S p := S p ∨ ∃ d, LP.holds d = p ∧ ¬ LP.Discharged d
  monotone' := by intro S T h p hp; exact hp.imp_left (h p)

/-- Recognition built over the ledger that accretes the **discharged**-backing
    read-faces — "settle what is inverse-matched." Same `S ↦ S ⊔ Q` shape, with
    `Q` the settled set. Its bare lfp is **complementary** to carrier (a)
    (`lfp_iff_not_flag_of_injective`): the opposite-sign gauge. -/
def recognizeDischarged (LP : LedgerPersistence) : Scope →o Scope where
  toFun S p := S p ∨ ∃ d, LP.holds d = p ∧ LP.Discharged d
  monotone' := by intro S T h p hp; exact hp.imp_left (h p)

/-- Bare lfp of the settle gauge: a read-face is in the least fixed point iff it
    backs **some discharged** debt. (`OrderHom.lfp` of `S ↦ S ⊔ Q` is `Q`: `Q` is
    a prefixed point, and `Q` lies below every prefixed point.) -/
theorem recognizeDischarged_lfp (LP : LedgerPersistence) :
    OrderHom.lfp (recognizeDischarged LP)
      = fun p => ∃ d, LP.holds d = p ∧ LP.Discharged d := by
  apply le_antisymm
  · refine (recognizeDischarged LP).lfp_le ?_
    intro p hp; exact hp.elim id id
  · refine (recognizeDischarged LP).le_lfp ?_
    intro b hb p hp; exact hb p (Or.inr hp)

/-- Bare lfp of the hold-open gauge: a read-face is in the least fixed point iff
    it backs **some undischarged** debt — i.e. *exactly* carrier (a)'s flag. -/
theorem recognizeUndischarged_lfp (LP : LedgerPersistence) :
    OrderHom.lfp (recognizeUndischarged LP)
      = fun p => ∃ d, LP.holds d = p ∧ ¬ LP.Discharged d := by
  apply le_antisymm
  · refine (recognizeUndischarged LP).lfp_le ?_
    intro p hp; exact hp.elim id id
  · refine (recognizeUndischarged LP).le_lfp ?_
    intro b hb p hp; exact hb p (Or.inr hp)

/-- Recognition built over the ledger that accretes **every debt-backing** read-face —
    "carry both signs at once," blind to discharge-status. Same `S ↦ S ⊔ Q` shape as the
    fork operators, with `Q` the all-debt-backed set. Its bare lfp is `seedBacked LP`
    (`recognizeBacked_lfp`), the **gauge-neutral `0`** of the seed-triple: this is the
    *operator-side* of `seedBacked`'s join `0 = + ⊔ −` (`seedBacked_eq_join`, below) — the
    third gauge-operator, completing `{recognizeUndischarged, recognizeDischarged,
    recognizeBacked}` ↔ `{+, −, 0}` (`SeedGaugeCommitment.lean`'s `SeedSign.gauge`). -/
def recognizeBacked (LP : LedgerPersistence) : Scope →o Scope where
  toFun S p := S p ∨ ∃ d, LP.holds d = p
  monotone' := by intro S T h p hp; exact hp.imp_left (h p)

/-- Bare lfp of the carry-both gauge: a read-face is in the least fixed point iff it backs
    **some** debt — i.e. exactly `seedBacked LP` (stated unfolded, as `seedBacked` is defined
    below). Same `lfp` of `S ↦ S ⊔ Q` computation as the two fork operators. -/
theorem recognizeBacked_lfp (LP : LedgerPersistence) :
    OrderHom.lfp (recognizeBacked LP) = fun p => ∃ d, LP.holds d = p := by
  apply le_antisymm
  · refine (recognizeBacked LP).lfp_le ?_
    intro p hp; exact hp.elim id id
  · refine (recognizeBacked LP).le_lfp ?_
    intro b hb p hp; exact hb p (Or.inr hp)

/-- **carrier (a) = bare carrier (b), at the hold-open gauge (bin-1).** The
    ledger's flag equals the bare lfp of `recognizeUndischarged`: the two carriers
    *coincide* exactly when recognition accretes the still-owed read-faces. This
    is README §V's "a debt is undischarged iff its read-face is live in the fixed
    scope" as a theorem. -/
theorem flag_eq_lfpFlag_recognizeUndischarged (LP : LedgerPersistence) :
    LP.flag = lfpFlag (recognizeUndischarged LP) := by
  funext S p
  show (∃ d, LP.holds d = p ∧ ¬ LP.Discharged d)
      = OrderHom.lfp (recognizeUndischarged LP) p
  rw [recognizeUndischarged_lfp]

/-- **Joint cover (no hypothesis).** Every *debt-backed* read-face is flagged by
    one carrier or the other: it is in the settle-gauge lfp (backs some discharged
    debt) or in carrier (a) (backs some undischarged debt). The two carriers
    together cover the debt-backed faces regardless of `holds`-injectivity. -/
theorem lfp_or_flag_of_backed (LP : LedgerPersistence) (S : Scope) (p : TapePosition)
    (h : ∃ d, LP.holds d = p) :
    OrderHom.lfp (recognizeDischarged LP) p ∨ LP.flag S p := by
  obtain ⟨d, hd⟩ := h
  rw [recognizeDischarged_lfp]
  by_cases hdis : LP.Discharged d
  · exact Or.inl ⟨d, hd, hdis⟩
  · exact Or.inr ⟨d, hd, hdis⟩

/-- **Disjoint, under `holds`-injectivity.** If each read-face backs at most one
    debt, no face is in both carriers: the settle-gauge lfp and carrier (a) are
    disjoint. (Without injectivity a face may back both a discharged and an
    undischarged debt, landing in both — the carriers then only *cover*, above.) -/
theorem not_lfp_and_flag_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (S : Scope) (p : TapePosition) :
    ¬ (OrderHom.lfp (recognizeDischarged LP) p ∧ LP.flag S p) := by
  rw [recognizeDischarged_lfp]
  rintro ⟨⟨d₁, hd₁, hdis₁⟩, ⟨d₂, hd₂, hndis₂⟩⟩
  exact hndis₂ (hinj (hd₁.trans hd₂.symm) ▸ hdis₁)

/-- **Complementarity, under `holds`-injectivity.** On any debt-backed face, the
    settle-gauge lfp is the *negation* of carrier (a): `lfp ↔ ¬ LP.flag`. Cover
    (`lfp_or_flag_of_backed`) + disjoint (`not_lfp_and_flag_of_injective`). The
    opposite-sign gauge to the coincidence above. -/
theorem lfp_iff_not_flag_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (S : Scope) (p : TapePosition)
    (h : ∃ d, LP.holds d = p) :
    OrderHom.lfp (recognizeDischarged LP) p ↔ ¬ LP.flag S p := by
  constructor
  · intro hlfp hflag
    exact not_lfp_and_flag_of_injective LP hinj S p ⟨hlfp, hflag⟩
  · intro hnflag
    exact (lfp_or_flag_of_backed LP S p h).resolve_right hnflag

/-- **Coincidence is impossible at the settle gauge (under injectivity).** On a
    debt-backed face the two carriers are provably opposite, so they cannot be
    equivalent — `recognizeDischarged` is the gauge at which the (a)↔(b) bridge is
    *refuted*. A typed non-recognition (§III totality-via-non-recognition). -/
theorem not_coincide_recognizeDischarged_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (S : Scope) (p : TapePosition)
    (h : ∃ d, LP.holds d = p) :
    ¬ (OrderHom.lfp (recognizeDischarged LP) p ↔ LP.flag S p) := by
  have hc := lfp_iff_not_flag_of_injective LP hinj S p h
  tauto

/-- **The ledger ↔ recognition bridge** (the remainder the (a)↔(b) merge named),
    on the `DesarguesianWitness` template: an observer-supplied commitment that
    carrier (a) (`LP.flag`) and bare carrier (b) (`lfpFlag f`) are the *same*
    persistence-flag. Both are scope-independent, so this is the well-posed bridge
    (`(a) ↔ lfpFlag`, not `(a) ↔ closureFlag`).

    Bin-2 over an arbitrary `f` — nothing in `LP` fixes the recognition operator.
    But the commitment is **discharged for free at one gauge**
    (`ofRecognizeUndischarged`, bin-1: the substrate fills the slot, as
    `DesarguesianWitness` is inhabited when `L = Sub(D, V)`) and **refuted at the
    opposite gauge** (`recognizeDischarged`, where the carriers are complementary,
    `not_bridge_recognizeDischarged_of_injective`). So the bridge's *sign* —
    coincide vs. complement — is the observer's gauge-commitment: the single
    external commitment / the tamp (README §IV.a, §VIII). -/
structure LedgerRecognitionBridge (LP : LedgerPersistence) (f : Scope →o Scope) where
  /-- carrier (a) and bare carrier (b) are the same persistence-flag. -/
  coincidence : LP.flag = lfpFlag f

/-- **The bridge is inhabited at the hold-open gauge (bin-1).** When `f` accretes
    the still-owed read-faces, coincidence holds by
    `flag_eq_lfpFlag_recognizeUndischarged` — the substrate fills the observer
    slot, exactly as `DesarguesianWitness` is constructible when `L = Sub(D, V)`. -/
def LedgerRecognitionBridge.ofRecognizeUndischarged (LP : LedgerPersistence) :
    LedgerRecognitionBridge LP (recognizeUndischarged LP) where
  coincidence := flag_eq_lfpFlag_recognizeUndischarged LP

/-- **The bridge is refuted at the settle gauge (under injectivity).** When `f`
    accretes the settled read-faces, the carriers are complementary on debt-backed
    faces, so no `LedgerRecognitionBridge` exists there:
    `LP.flag ≠ lfpFlag (recognizeDischarged LP)`. The sign flipped — same ledger,
    opposite gauge. -/
theorem not_bridge_recognizeDischarged_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (p : TapePosition) (h : ∃ d, LP.holds d = p) :
    LP.flag ≠ lfpFlag (recognizeDischarged LP) := by
  intro heq
  have hp : LP.flag ⊥ p = OrderHom.lfp (recognizeDischarged LP) p :=
    congrFun (congrFun heq ⊥) p
  exact not_coincide_recognizeDischarged_of_injective LP hinj ⊥ p h (Iff.of_eq hp).symm

/-- **The bridge is refuted at the carry-both (`0`) gauge too (under injectivity, given a
    discharged debt).** When `f` accretes *every* debt-backed face, its lfp (`seedBacked`)
    over-counts carrier (a): the discharged debt `d`'s read-face is backed (so in the lfp)
    but carries no undischarged debt (injectivity), so it is not in `LP.flag`. Hence
    `LP.flag ≠ lfpFlag (recognizeBacked LP)`: the gauge-neutral `0` does **not** coincide
    with carrier (a) either. So among the whole seed-triple `{+, −, 0}`, the hold-open `+`
    is the *unique* coincidence-gauge (`SeedGaugeCommitment.bridgeCoincides_iff_eq_plus`). -/
theorem not_bridge_recognizeBacked_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (d : LP.ledger.debts) (hdis : LP.Discharged d) :
    LP.flag ≠ lfpFlag (recognizeBacked LP) := by
  intro heq
  have hp : LP.flag ⊥ (LP.holds d) = OrderHom.lfp (recognizeBacked LP) (LP.holds d) :=
    congrFun (congrFun heq ⊥) (LP.holds d)
  simp only [recognizeBacked_lfp] at hp
  obtain ⟨d', hd', hndis'⟩ := (Iff.of_eq hp).mpr ⟨d, rfl⟩
  exact hndis' (by rw [hinj hd']; exact hdis)

/-! ## The seed-gauge is a `{+, −, 0}` triple — the gauge-neutral `0` is the join of the `±` fork

`RecognitionApplier.lean` localized the tamp to the **seed** `P₀` and found the
undischarged- vs discharged-backed seed-choice is the coincide/complement gauge-fork
(`seed_fork_of_injective`). Those are the `±` *signs*. But a fork has a third,
distinguished point — the **join** — and it is already sitting in `lfp_or_flag_of_backed`:
the **all-debt-backed** seed

> `seedBacked LP := fun p => ∃ d, LP.holds d = p`

backs *every* debt regardless of discharge-status. `lfp_or_flag_of_backed` shows every
backed face is undischarged-backed ∨ discharged-backed; the reverse drops the
discharge-condition. So `seedBacked` is *exactly* the join of the two fork-seeds
(`seedBacked_eq_join`) — it carries **both** signs at once, hence is **gauge-neutral**:
the `0` of a `{+, −, 0}` seed-triple, with `⊥` (the `P₀ = ∅` empty seed) below.

This block types that triple (`SeedSign`) and lands the recognition that the seed-gauge
is **not a bare 2-fork** but a three-element structure with a distinguished neutral
element — `0 = + ⊔ −`. The grading: under `holds`-injectivity the `0` seed is *distinct*
from both `±` exactly when the ledger carries both a discharged and an undischarged debt
(`SeedSign.zero_ne_plus_of_injective` / `zero_ne_minus_of_injective`); where it carries
only one kind, the triple collapses. (The closures of these seeds over foam's real gated
`F` are read off in `RecognitionApplier.lean`; the `0`-seed's closure dominates both
`±`-fork closures via `convergeFrom_mono_seed`.) -/

/-- The **all-debt-backed seed** — the gauge-neutral `0` of the seed-triple. A read-face is
    in it iff it backs *some* debt, discharged or not. Contrast the two fork-seeds
    (`recognizeUndischarged_lfp` / `recognizeDischarged_lfp`), which each carry a
    discharge-sign; `seedBacked` carries neither, hence both (`seedBacked_eq_join`). -/
def seedBacked (LP : LedgerPersistence) : Scope := fun p => ∃ d, LP.holds d = p

/-- **The gauge-neutral seed is the join of the `±` fork (bin-1).**
    `seedBacked LP = lfp (recognizeUndischarged LP) ⊔ lfp (recognizeDischarged LP)`.
    Forward is `lfp_or_flag_of_backed` (every backed face is on one side of the fork);
    reverse drops the discharge-condition. So `0 = + ⊔ −`: the all-debt-backed seed carries
    both signs, the structural reason it is gauge-neutral. -/
theorem seedBacked_eq_join (LP : LedgerPersistence) :
    seedBacked LP
      = OrderHom.lfp (recognizeUndischarged LP) ⊔ OrderHom.lfp (recognizeDischarged LP) := by
  rw [recognizeUndischarged_lfp, recognizeDischarged_lfp]
  funext p
  simp only [seedBacked, Pi.sup_apply, sup_Prop_eq, eq_iff_iff]
  constructor
  · rintro ⟨d, hd⟩
    by_cases hdis : LP.Discharged d
    · exact Or.inr ⟨d, hd, hdis⟩
    · exact Or.inl ⟨d, hd, hdis⟩
  · rintro (⟨d, hd, _⟩ | ⟨d, hd, _⟩) <;> exact ⟨d, hd⟩

/-- The gauge-neutral seed is **not** the hold-open (`+`) seed when some debt is discharged
    (under `holds`-injectivity): that debt's read-face backs a debt (so is in `seedBacked`)
    but every debt on it is discharged (injectivity), so it is *not* undischarged-backed. -/
theorem seedBacked_ne_undischarged_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (h : ∃ d, LP.Discharged d) :
    seedBacked LP ≠ OrderHom.lfp (recognizeUndischarged LP) := by
  obtain ⟨d, hdis⟩ := h
  intro heq
  have hp : seedBacked LP (LP.holds d) := ⟨d, rfl⟩
  rw [heq, recognizeUndischarged_lfp] at hp
  obtain ⟨d', hd', hndis'⟩ := hp
  exact hndis' (by rw [hinj hd']; exact hdis)

/-- The gauge-neutral seed is **not** the settle (`−`) seed when some debt is undischarged
    (under `holds`-injectivity): symmetric to `seedBacked_ne_undischarged_of_injective`. -/
theorem seedBacked_ne_discharged_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (h : ∃ d, ¬ LP.Discharged d) :
    seedBacked LP ≠ OrderHom.lfp (recognizeDischarged LP) := by
  obtain ⟨d, hndis⟩ := h
  intro heq
  have hp : seedBacked LP (LP.holds d) := ⟨d, rfl⟩
  rw [heq, recognizeDischarged_lfp] at hp
  obtain ⟨d', hd', hdis'⟩ := hp
  exact hndis (by rw [← hinj hd']; exact hdis')

/-- **`convergeFrom f` is monotone in the seed.** A larger initial substrate `P₀` yields a
    larger converged scope: `OrderHom.lfp` is monotone, and `X ↦ S ⊔ f X` is monotone in
    `S`. This is what lets the gauge-neutral `0`-seed's closure *dominate* both `±`-fork
    closures over foam's real gated `F` (not only at the trivial step) — see
    `RecognitionApplier.closure_backed_ge_undischarged` / `_discharged`. -/
theorem convergeFrom_mono_seed (f : Scope →o Scope) {S T : Scope} (h : S ≤ T) :
    convergeFrom f S ≤ convergeFrom f T := by
  unfold convergeFrom
  exact OrderHom.lfp.mono fun X => sup_le_sup_right h (f X)

/-- The **seed-gauge** as a typed three-element sign: the `{+, −, 0}` triple the
    coincide/complement fork (7)/(8) completes. `plus` = hold-open (undischarged-backed,
    carrier (a)'s flag); `minus` = settle (discharged-backed, carrier (a)'s complement);
    `zero` = all-debt-backed, the **gauge-neutral** join of the `±` signs
    (`SeedSign.seed_zero_eq_join`). With `⊥` (the `P₀ = ∅` empty seed) below all three
    (`SeedSign.bot_le_seed`), the seed-side structure the single external commitment / the
    tamp selects from is `{⊥} ∪ {+, −, 0}`. -/
inductive SeedSign where
  /-- `+` — seed with the still-owed (undischarged-backed) read-faces. -/
  | plus
  /-- `−` — seed with the settled (discharged-backed) read-faces. -/
  | minus
  /-- `0` — seed with *every* debt-backed read-face; the gauge-neutral join of `±`. -/
  | zero
  deriving DecidableEq, Repr

/-- The `Scope` each gauge-sign seeds recognition with: `+ ↦` carrier (a) (the hold-open
    lfp), `− ↦` its settle-complement lfp, `0 ↦ seedBacked` (the join). -/
def SeedSign.seed (LP : LedgerPersistence) : SeedSign → Scope
  | plus => OrderHom.lfp (recognizeUndischarged LP)
  | minus => OrderHom.lfp (recognizeDischarged LP)
  | zero => seedBacked LP

/-- **`0 = + ⊔ −`, typed** (the `SeedSign` face of `seedBacked_eq_join`): the gauge-neutral
    seed is the join of the two fork-seeds. The seed-gauge is a `{+, −, 0}` structure with a
    distinguished neutral element, not a bare 2-fork. -/
theorem SeedSign.seed_zero_eq_join (LP : LedgerPersistence) :
    SeedSign.zero.seed LP = SeedSign.plus.seed LP ⊔ SeedSign.minus.seed LP :=
  seedBacked_eq_join LP

/-- `⊥` (the empty seed `P₀ = ∅`) sits below every gauge-sign seed: the triple `{+, −, 0}`
    rides above the bare-lfp base. -/
theorem SeedSign.bot_le_seed (LP : LedgerPersistence) (s : SeedSign) :
    (⊥ : Scope) ≤ s.seed LP :=
  bot_le

/-- `+ ≤ 0`: the hold-open seed is below the gauge-neutral join. -/
theorem SeedSign.plus_le_zero (LP : LedgerPersistence) :
    SeedSign.plus.seed LP ≤ SeedSign.zero.seed LP := by
  rw [SeedSign.seed_zero_eq_join]; exact le_sup_left

/-- `− ≤ 0`: the settle seed is below the gauge-neutral join. -/
theorem SeedSign.minus_le_zero (LP : LedgerPersistence) :
    SeedSign.minus.seed LP ≤ SeedSign.zero.seed LP := by
  rw [SeedSign.seed_zero_eq_join]; exact le_sup_right

/-- **The `±` fork meets at `⊥` (under `holds`-injectivity)** — the lattice companion to
    `seed_zero_eq_join`'s join `0 = + ⊔ −`. The two fork-seeds are *disjoint*: no read-face
    is both undischarged- and discharged-backed once each face backs at most one debt
    (`not_lfp_and_flag_of_injective`, rewritten through `flag = lfpFlag recognizeUndischarged`).
    Together with the join, `+ ⊓ − = ⊥` makes `{⊥, +, −, 0}` a **4-element Boolean algebra**
    with `±` complementary atoms — `−` the *local complement* of `+` within `[⊥, 0]` (the
    `0`-scope), README §IV.a's HalfType (complementation-within-a-scope). The `IsCompl` /
    `HalfType` assembly on this meet+join pair is `SeedGaugeHalfType.lean`. -/
theorem SeedSign.plus_inf_minus_eq_bot (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) :
    SeedSign.plus.seed LP ⊓ SeedSign.minus.seed LP = ⊥ := by
  funext p
  refine propext ⟨fun h => ?_, fun h => h.elim⟩
  obtain ⟨hplus, hminus⟩ := h
  refine not_lfp_and_flag_of_injective LP hinj ⊥ p ⟨hminus, ?_⟩
  rw [flag_eq_lfpFlag_recognizeUndischarged]
  exact hplus

/-- **The grading, `+` side: the gauge-neutral `0` seed is distinct from `+`** whenever the
    ledger has a discharged debt (under `holds`-injectivity). That debt's read-face is in
    `0` (it backs a debt) but not in `+` (the debt is discharged, and injectivity rules out
    a *different* undischarged debt on the same face). So the `{+, −, 0}` triple is genuinely
    three seeds, not a collapse. -/
theorem SeedSign.zero_ne_plus_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (h : ∃ d, LP.Discharged d) :
    SeedSign.zero.seed LP ≠ SeedSign.plus.seed LP :=
  seedBacked_ne_undischarged_of_injective LP hinj h

/-- **The grading, `−` side: the gauge-neutral `0` seed is distinct from `−`** whenever the
    ledger has an undischarged debt (under `holds`-injectivity). Symmetric to the `+` side.
    Together: where the ledger carries *both* kinds of debt, `{+, −, 0}` are three distinct
    seeds; where it carries only one, the triple degenerates. -/
theorem SeedSign.zero_ne_minus_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (h : ∃ d, ¬ LP.Discharged d) :
    SeedSign.zero.seed LP ≠ SeedSign.minus.seed LP :=
  seedBacked_ne_discharged_of_injective LP hinj h

/-- **The complementary atoms are genuinely distinct** (under injectivity, given a discharged
    debt): `+ ≠ −`. If `+ = −` then `0 = + ⊔ − = +` (`seed_zero_eq_join` + `sup_idem`),
    contradicting `zero_ne_plus_of_injective`. So with both kinds of debt present the
    `{⊥, +, −, 0}` Boolean algebra is non-degenerate — two distinct complementary atoms, not a
    collapse. (With `zero_ne_plus` / `zero_ne_minus`: the `0`-scope is a genuine `2²`.) -/
theorem SeedSign.plus_ne_minus_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (h : ∃ d, LP.Discharged d) :
    SeedSign.plus.seed LP ≠ SeedSign.minus.seed LP := by
  intro heq
  apply SeedSign.zero_ne_plus_of_injective LP hinj h
  rw [SeedSign.seed_zero_eq_join, ← heq, sup_idem]

end Foam
