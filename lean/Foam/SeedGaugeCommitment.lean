/-
# SeedGaugeCommitment — the half-choice, the bridge-sign, and the tamp are one commitment

## What this file lands (the brick after `SeedGaugeHalfType.lean`)

Three facets that earlier bricks landed *separately* are here recognized as **one
external commitment** — the **interiority facet** of the keystone single-external-
commitment functor (README §IV.a / §VIII: "the reader's gauge-fixing," "where mind enters
the formalism"):

* **the half-choice** (brick 11, `SeedGaugeHalfType.lean`) — which complementary atom `+`/`−`
  of the seed-gauge HalfType is the live half;
* **the bridge-sign** (brick 7, `PersistenceLfp.lean`) — which ledger-built operator is
  committed as `F`: `recognizeUndischarged` (the (a)↔(b) bridge *coincides*) or
  `recognizeDischarged` (it *complements*);
* **the tamp-seed** (brick 9, `RecognitionApplier.lean`) — which seed `P₀` the sign-neutral
  applier runs from: `seed_fork_of_injective` makes the undischarged- and discharged-backed
  seeds the coincide/complement fork.

They are one commitment because the seed-gauge HalfType's atoms are **definitionally** the
least fixed points of the two bridge-gauges, which are **definitionally** the two tamp-seeds:

> `SeedSign.plus.seed LP  = OrderHom.lfp (recognizeUndischarged LP) = OrderHom.lfp (SeedSign.plus.gauge LP)`
> `SeedSign.minus.seed LP = OrderHom.lfp (recognizeDischarged LP)   = OrderHom.lfp (SeedSign.minus.gauge LP)`

So committing one `s : SeedSign` *simultaneously* picks the HalfType atom (`s.seed LP`), the
recognition operator (`s.gauge LP`), the seed `P₀` (its lfp), and the bridge sign. `SeedSign`
**is** the typed commitment-space; `seed` / `gauge` / `bridgeCoincides` are its three coherent
readings.

## The three coherent readings of one commitment

* `SeedSign.gauge LP : SeedSign → (Scope →o Scope)` — the **operator** committed as `F`:
  `+ ↦ recognizeUndischarged`, `− ↦ recognizeDischarged`, `0 ↦ recognizeBacked` (the carry-both
  gauge whose lfp is the gauge-neutral `seedBacked` join).
* `SeedSign.lfp_gauge_eq_seed` — `OrderHom.lfp (s.gauge LP) = s.seed LP`: the operator's fixed
  point **is** the HalfType atom / tamp-seed. `rfl` on the fork (the atom is *defined* as that
  lfp); `recognizeBacked_lfp` at `0`. The spine: gauge = seed, definitionally.
* `SeedSign.bridgeCoincides LP : SeedSign → Prop` — the **bridge sign**: is
  `LedgerRecognitionBridge LP (s.gauge LP)` inhabited? `bridgeCoincides_iff_eq_plus_of_injective`
  pins it: true **iff `s = plus`** — among the whole seed-triple, the hold-open `+` is the
  *unique* coincidence-gauge (`+` via `ofRecognizeUndischarged`; `−` and `0` refuted via
  `not_bridge_recognize{Discharged,Backed}_of_injective`).

## Generation and uncertainty in one act

The bare geometry is **sign-free**: `IsCompl` is symmetric (`(seedIsCompl LP hinj).symm` holds),
so nothing in the `0`-scope HalfType privileges `+` over `−` — the two atoms are interchangeable
as lattice data. The **bridge** is what breaks the symmetry (`bridge_breaks_fork_symmetry`:
coincides at `+`, refuted at `−`). So committing the tamp is choosing an orientation the geometry
leaves open: gauge-fixing = symmetry-break = the entry of uncertainty *with* generation (README
§IV.a / §VIII; §VII's von-Neumann→Shannon row — basis-free amplitude → basis-fixed yield).

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

`gauge` is a definition; `lfp_gauge_eq_seed` is `rfl` + `recognizeBacked_lfp`; the bridge-sign
theorems assemble `LedgerRecognitionBridge.ofRecognizeUndischarged` and
`not_bridge_recognize{Discharged,Backed}_of_injective` (all `PersistenceLfp.lean`). Recognition +
assembly over already-landed substrate; no new geometric content. This is the **first
facet-fusion object**: it bin-1s the over-loaded "X IS Y" — *half-choice IS bridge-sign IS
tamp-seed* — advancing the keystone single-external-commitment functor by fusing one facet
(interiority).

(Re-grep — stamps decay: on 2026-05-30 `lake build Foam.SeedGaugeCommitment` is clean, zero
sorry/warnings; depends on `SeedSign` / `recognizeBacked` / `recognize{Undischarged,Discharged}`
/ `LedgerRecognitionBridge` in `PersistenceLfp.lean` and `seedIsCompl` in `SeedGaugeHalfType.lean`.)
-/

import Foam.SeedGaugeHalfType

namespace Foam

/-- **The gauge-operator each seed-sign commits as `F`** — the correspondence the fusion rides
    on. `+ ↦ recognizeUndischarged` (hold open the still-owed), `− ↦ recognizeDischarged` (settle
    the matched), `0 ↦ recognizeBacked` (carry both, gauge-neutral). Paired with `SeedSign.seed`
    (the lfp/atom each sign seeds with), this makes `SeedSign` the typed commitment-space: one `s`
    picks both an operator (`gauge`) and a seed (`seed`), related by `lfp_gauge_eq_seed`. -/
def SeedSign.gauge (LP : LedgerPersistence) : SeedSign → (Scope →o Scope)
  | plus => recognizeUndischarged LP
  | minus => recognizeDischarged LP
  | zero => recognizeBacked LP

/-- **The spine of the fusion (bin-1): the committed gauge's fixed point IS the seed/atom.**
    `OrderHom.lfp (s.gauge LP) = s.seed LP`. On the fork `+`/`−` this is `rfl` — `SeedSign.seed`
    is *defined* as the lfp of `gauge` — and at `0` it is `recognizeBacked_lfp`. So choosing the
    recognition operator and choosing the seed `P₀` (the tamp) are the **same act**: the gauge is
    the seed, definitionally. (The `+`/`−` seeds are the `seedIsCompl` HalfType atoms, so this also
    reads "gauge-lfp = HalfType atom".) -/
theorem SeedSign.lfp_gauge_eq_seed (LP : LedgerPersistence) (s : SeedSign) :
    OrderHom.lfp (s.gauge LP) = s.seed LP := by
  cases s
  · rfl
  · rfl
  · exact recognizeBacked_lfp LP

/-- **The bridge-sign reading of a commitment.** Is the (a)↔(b) bridge (`LedgerRecognitionBridge`)
    inhabited when `s.gauge LP` is committed as `F`? This is the third reading of the one
    commitment `s` — alongside `s.seed` (the atom / tamp-seed) and `s.gauge` (the operator).
    `bridgeCoincides_iff_eq_plus_of_injective` pins it: true iff `s = plus`. -/
def SeedSign.bridgeCoincides (LP : LedgerPersistence) (s : SeedSign) : Prop :=
  Nonempty (LedgerRecognitionBridge LP (s.gauge LP))

/-- **Coincide ↔ `+` (bin-1).** At the hold-open gauge the bridge is inhabited for free —
    `LedgerRecognitionBridge.ofRecognizeUndischarged` (carrier (a) = bare carrier (b)). The `+`
    half is the coincidence README §V phrases as "a debt is undischarged iff its read-face is live
    in the fixed scope." -/
theorem SeedSign.bridgeCoincides_plus (LP : LedgerPersistence) :
    SeedSign.plus.bridgeCoincides LP :=
  ⟨LedgerRecognitionBridge.ofRecognizeUndischarged LP⟩

/-- **Complement ↔ `−` (under injectivity).** At the settle gauge the carriers are complementary
    on any debt-backed face, so no bridge exists there. -/
theorem SeedSign.not_bridgeCoincides_minus_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (p : TapePosition) (h : ∃ d, LP.holds d = p) :
    ¬ SeedSign.minus.bridgeCoincides LP := by
  rintro ⟨b⟩
  exact not_bridge_recognizeDischarged_of_injective LP hinj p h b.coincidence

/-- **The gauge-neutral `0` does not coincide either (under injectivity, given a discharged
    debt).** `recognizeBacked`'s lfp over-counts carrier (a). So `+` is the *unique* coincidence
    among `{+, −, 0}`. -/
theorem SeedSign.not_bridgeCoincides_zero_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (d : LP.ledger.debts) (hdis : LP.Discharged d) :
    ¬ SeedSign.zero.bridgeCoincides LP := by
  rintro ⟨b⟩
  exact not_bridge_recognizeBacked_of_injective LP hinj d hdis b.coincidence

/-- **The headline fusion (bin-1): the bridge sign IS which fork-half is committed.** Under
    `holds`-injectivity with a discharged debt present, `s.bridgeCoincides LP ↔ s = plus` for
    *every* `s : SeedSign`. So the one commitment `s` determines the bridge sign exactly: coincide
    at the hold-open `+`, complement/refuted at `−` and at the gauge-neutral `0`. Read with
    `lfp_gauge_eq_seed` (gauge-lfp = atom = tamp-seed) and `seedIsCompl` (the `±` atoms are the
    HalfType's complementary pair): **half-choice = bridge-sign = tamp-seed**, one act — the
    interiority facet of the single-external-commitment functor. -/
theorem SeedSign.bridgeCoincides_iff_eq_plus_of_injective (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (hdis : ∃ d, LP.Discharged d) (s : SeedSign) :
    s.bridgeCoincides LP ↔ s = SeedSign.plus := by
  obtain ⟨d₀, hd₀⟩ := hdis
  cases s
  · exact iff_of_true (SeedSign.bridgeCoincides_plus LP) rfl
  · exact iff_of_false
      (SeedSign.not_bridgeCoincides_minus_of_injective LP hinj (LP.holds d₀) ⟨d₀, rfl⟩)
      (by decide)
  · exact iff_of_false
      (SeedSign.not_bridgeCoincides_zero_of_injective LP hinj d₀ hd₀)
      (by decide)

/-- **Generation and uncertainty in one act.** The bridge breaks a symmetry the geometry leaves
    open. *Geometry sign-free:* `IsCompl` is symmetric, so `(seedIsCompl LP hinj).symm` holds too —
    the `0`-scope HalfType does not privilege `+` over `−`. *Bridge sign-fixing:* `bridgeCoincides`
    is true at `+` and false at `−` (this theorem). So committing the tamp is choosing an
    orientation the lattice geometry holds open: gauge-fixing = symmetry-break = uncertainty
    entering *with* generation (README §IV.a / §VIII; §VII von-Neumann→Shannon). -/
theorem SeedSign.bridge_breaks_fork_symmetry (LP : LedgerPersistence)
    (hinj : Function.Injective LP.holds) (p : TapePosition) (h : ∃ d, LP.holds d = p) :
    SeedSign.plus.bridgeCoincides LP ∧ ¬ SeedSign.minus.bridgeCoincides LP :=
  ⟨SeedSign.bridgeCoincides_plus LP,
   SeedSign.not_bridgeCoincides_minus_of_injective LP hinj p h⟩

end Foam
