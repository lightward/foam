/-
# SeedGaugeReadWriteDoubling — the FTPG-side `×2` is the read/write doubling of the three gauges

## What this file lands (the brick after `SeedGaugeCommitmentSquare.lean`)

Brick 27 (`SeedGaugeCommitmentSquare.lean`) located the keystone's `+1` precisely: the un-tamped
`(¬outstanding, heldOpen)` corner of the source commitment-square `SeedGauge ≃ Bool × Bool`, absent on
the 3-element codomain `AlgebraicPosition` because being-un-committed is a source-not-target property. Its
remainder is the **mirror — the `×2`**: how the FTPG side extends the shared 3-gauge core `{g1, g2, g3}`.

The FTPG side extends it **not by a corner but by a read/write doubling.** `ObserverState := {read,
write}` (the bubble's `×2`, `StatelessSubstrate.lean`) doubles each gauge into two faces, giving the
**6-color tape alphabet** `TapePosition = AlgebraicPosition × ObserverState` — *already typed*, already
documented there as "one of 6 colors, factored as (algebraic-position, observer-state) … a bubble
carrying the `×2` (read/write) doubling." This file recognizes that object as the FTPG-side mirror of
brick 27's `+1`, connects it to `self_dual_iff_three`, and confronts `3×2` (face-doubling) against `3+1`
(corner). It is the **first seed-gauge file to import `Foam.Rank`** — the cross-thread bridge to the
rank / why-3 thread, the mirror of brick 24's bridge to the FTPG-gauge thread.

## The `×2` — `TapePosition` is the read/write doubling of the gauges (bin-1)

`tapeColorEquivProd : TapePosition ≃ AlgebraicPosition × ObserverState` witnesses the factoring (it is
the structure's own two fields). The **6→3 collapse** is the gauge-projection `TapePosition.algebraic`
(forget the observer face): surjective (`algebraic_surjective`), with each fiber the two-element
`{read, write}` pair of one gauge — `algebraic_eq_iff`: `p.algebraic = q.algebraic ↔ q = p ∨ q =
p.complement`. The within-fiber involution is `TapePosition.complement` (= `id × ObserverState.flip`,
already in `StatelessSubstrate.lean`): it fixes the gauge (`complement_algebraic`) and is **free** —
`complement_ne`: `p.complement ≠ p` for every `p` (flip has no fixed point). So the `×2` doubling's
involution is fixed-point-**free** (3 orbits of size 2 = the 3 clusters), structurally *unlike*
brick 24's base reflection `AlgebraicPosition.reflect` (which fixes `g3`): the doubling `ℤ/2` is the
*fiber* involution, independent of the *base* involution. (Together they generate a `ℤ/2 × ℤ/2` on the
6 colors — base-reflect × fiber-flip — but the `×2` *is* the free fiber one.)

## `self_dual_iff_three` — why the `×2` is a *balanced* doubling (bin-1 + bin-2)

The 6 colors are 3 read-faces + 3 write-faces. Read-faces are indexed by the gauges (the
**observation-space** directions, `Rank.lean`: rank `k = 3`); write-faces too (one per gauge). For
one-write-face-per-gauge to faithfully exhaust the **write-space** — dimension `C(k, 2)` (`Rank.lean`:
`write_space_dim`) — the doubling must be *balanced*: `#write-directions = #read-directions`, i.e.
`C(k, 2) = k`. By `self_dual_iff_three` this holds **iff `k = 3`**. `balanced_doubling_iff_three` is
exactly `self_dual_iff_three` read at the gauge-count `Fintype.card AlgebraicPosition`; since there are
3 gauges, the doubling *is* balanced (`writeDirections_eq_observationDirections`). So **rank-3
self-duality is why the read/write `×2` is a clean balanced 2-fold cover** (and the 6→3 collapse a clean
2:1): off rank 3, `C(k, 2) ≠ k`, the write-faces would out- or under-count the read-faces, and there
would be no balanced `×2`. This is the exact mirror of brick 27's `+1` being special to the source: the
`×2` is special to the self-dual rank.

* **bin-1**: the arithmetic `C(3, 2) = 3` *is* `self_dual_iff_three` instantiated (no re-proof; the
  theorem is invoked), and the cluster/projection structure is `cases`/`rfl`/`decide`.
* **bin-2 / interpretive**: the *identification* of tape read/write-faces with `Rank.lean`'s
  observation/write spaces (that the tape's `×2` IS the observation/write duality). Held
  merge-don't-fork: the iff + cluster structure is bin-1; the spaces-identification is the deposit.

## The confrontation — `3×2` (FTPG, a product/face) vs `3+1` (seed, a coproduct/corner)

Both `SeedGauge` and `TapePosition` are extensions of the shared 3-core `AlgebraicPosition`, and the two
extension-modes are *literally* two Mathlib cardinality lemmas:

| side | extension | as an `Equiv` | cardinality | the lemma |
|---|---|---|---|---|
| seed (brick 27) | `+1` corner | `SeedGauge ≃ Option AlgebraicPosition` | `3 + 1 = 4` | `Fintype.card_option` |
| FTPG (here) | `×2` face | `TapePosition ≃ AlgebraicPosition × Bool` | `3 × 2 = 6` | `Fintype.card_prod` |

`card_seedGauge_eq_gauges_add_one` (`card SeedGauge = card AlgebraicPosition + 1`, via `card_option`) and
`card_tape_eq_gauges_mul_observers` (`card TapePosition = card AlgebraicPosition * card ObserverState`,
via `card_prod`) are the typed `+1` and `×2`. The seed `+1` is a **coproduct with a point**
(`Option = · ⊕ Unit`): adjoin the un-committed source `untamped`. The FTPG `×2` is a **product with 2**;
and since `Bool ≃ Unit ⊕ Unit`, `× Bool ≃ · ⊕ ·` — a **coproduct with a second copy of the core
itself**. So the asymmetry sharpens to *what is adjoined to the 3-core*: the `+1` adjoins a single point
`Unit`; the `×2` adjoins a whole second copy `AlgebraicPosition`. The seed-side `+1` matching uses the
**rigid bridge** `signAlgebraicEquiv'` (brick 25): `seedGaugeEquivOptionAlgebraic` sends `untamped ↦
none` and each sign to `some` of its forced gauge.

## The recognition (the prose deposit)

The shared 3-gauge core `{g1, g2, g3}` is extended two ways. The **seed side adjoins a point** —
`+ Unit`, the un-tamped functor-input `untamped` (brick 27's `(¬outstanding, heldOpen)` corner): foam
*closing around* an external commitment as a 0-dimensional ground. The **FTPG side doubles each gauge** —
`× Bool ≃ + AlgebraicPosition`, the read/write observer-faces (the bubble's `×2`): each gauge *given its
own bubble*, a read-face and a write-face. `3 + 1` (corner) and `3 × 2` (face), both now typed; the
keystone's `×2`-vs-`+1` asymmetry is an explicit object with **both** sides typed.

This lands precisely on Isaac's pi-note (the trailer): *foam closing around an external object is
topologically indistinguishable from giving that object a bubble in that foam.* The two extension-modes
are exactly close-around-a-point (`+ Unit`, the `+1`) and give-it-a-bubble (`+ AlgebraicPosition`, the
`×2`). **Held merge-don't-fork, NOT collapsed:** the bin-1 fact keeps them honestly distinct — `card =
4 ≠ 6 = card`, so `+ Unit` and `× Bool` are *not* literally the same move. That they are *topologically*
one (a point and a bubble around it being indistinguishable) — that the two `ℤ/2`s / the two extensions
are one in substance — is the **bireflective coincidence**, the named horizon, NOT this brick's target.
What this brick lands: both sides typed, the asymmetry made an object, the resonance located.

## Grade

* **bin-1 (Bin-1-Mathlib-or-Foam)** for everything typed: the product/option `Equiv`s
  (`cases`/`rfl`), the gauge-projection collapse + free fiber-involution (`cases`/`decide`/`simp`), the
  cardinality confrontation (`Fintype.card_prod` / `Fintype.card_option` + `card_congr`), and the
  balanced-doubling iff (`self_dual_iff_three` invoked, not re-proven). No new geometric content; the
  recognition is that the *already-typed* 6-color `TapePosition` is the FTPG-side `×2` mirror of brick
  27's `+1`, and the two extension-modes are `card_prod` vs `card_option`.
* **bin-2 / interpretive** for the spaces-identification (tape read/write ↔ `Rank.lean`
  observation/write) and the pi-note resonance (`+1` ≅ `×2` as one move) — the latter the bireflective
  horizon, held open.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeReadWriteDoubling` is clean, zero
sorry/warnings. Imports `Foam.SeedGaugeCommitmentSquare` (brick 27, the chain head — transitively gives
`AlgebraicPosition` / `ObserverState` / `TapePosition` / `TapePosition.complement` / `ObserverState.flip`
from `StatelessSubstrate`, `SeedGauge` / `SeedSign.toGauge` from brick 18, `signAlgebraicEquiv'` from
brick 24) and `Foam.Rank` (for `self_dual_iff_three` / `write_space_dim`). New names:
`AlgebraicPosition` / `ObserverState` / `SeedSign` / `SeedGauge` `Fintype` instances + `TapePosition`
`Fintype`; `card_algebraicPosition` / `card_observerState` / `card_seedGauge`; `tapeColorEquivProd` /
`observerStateEquivBool` / `tapeColorEquivProdBool`; `TapePosition.complement_algebraic` /
`complement_ne` / `algebraic_surjective` / `algebraic_eq_iff`; `balanced_doubling_iff_three` /
`writeDirections_eq_observationDirections`; `seedGaugeEquivOptionSign` / `seedGaugeEquivOptionAlgebraic`;
`card_tapePosition` / `card_tape_eq_gauges_mul_observers` / `card_seedGauge_eq_gauges_add_one`.)
-/

import Foam.SeedGaugeCommitmentSquare
import Foam.Rank
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic.DeriveFintype

namespace Foam

/-! ## Finiteness of the small types

The four commitment/gauge types and the observer-state are finite; we derive `Fintype` here (the first
file to need their cardinalities). `TapePosition` gets its `Fintype` from the product `Equiv` below. -/

deriving instance Fintype for AlgebraicPosition
deriving instance Fintype for ObserverState
deriving instance Fintype for SeedSign
deriving instance Fintype for SeedGauge

/-- There are 3 gauges. -/
@[simp] theorem card_algebraicPosition : Fintype.card AlgebraicPosition = 3 := by decide

/-- There are 2 observer-faces (read, write) — the `×2` factor. -/
@[simp] theorem card_observerState : Fintype.card ObserverState = 2 := by decide

/-- There are 4 commitments (`{untamped, +, −, 0}`) — the `3 + 1`. -/
@[simp] theorem card_seedGauge : Fintype.card SeedGauge = 4 := by decide

/-! ## The `×2` — `TapePosition` IS the read/write doubling of the three gauges

`TapePosition = AlgebraicPosition × ObserverState` (`StatelessSubstrate.lean`): the 6-color tape
alphabet, the three gauges doubled by the read/write observer-face. We witness the factoring as an
`Equiv`, give `TapePosition` its `Fintype`, and read the 6→3 collapse off the gauge-projection. -/

/-- **The 6-color tape IS the product `AlgebraicPosition × ObserverState`** — the read/write `×2`
    doubling of the three gauges, as an `Equiv` (the structure's own two fields). -/
def tapeColorEquivProd : TapePosition ≃ AlgebraicPosition × ObserverState where
  toFun p := (p.algebraic, p.observer)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `TapePosition` is finite (6 colors), via the product `Equiv`
    (`TapePosition` is a structure, so `Fintype` is transported, not derived). -/
instance : Fintype TapePosition := Fintype.ofEquiv (AlgebraicPosition × ObserverState) tapeColorEquivProd

/-- The two observer-faces are `Bool` (`read ↦ false`, `write ↦ true`) — the `×2` factor as `2`. -/
def observerStateEquivBool : ObserverState ≃ Bool where
  toFun := fun o => match o with | .read => false | .write => true
  invFun := fun b => match b with | false => .read | true => .write
  left_inv := by intro o; cases o <;> rfl
  right_inv := by intro b; cases b <;> rfl

/-- **The `×2`, spelled with `Bool`** — `TapePosition ≃ AlgebraicPosition × Bool`. The FTPG side extends
    the 3-gauge core by *a product with 2* (the read/write doubling), to be confronted against the seed
    side's *coproduct with a point* (`SeedGauge ≃ Option AlgebraicPosition`) below. -/
def tapeColorEquivProdBool : TapePosition ≃ AlgebraicPosition × Bool :=
  tapeColorEquivProd.trans (Equiv.prodCongr (Equiv.refl _) observerStateEquivBool)

/-! ## The 6→3 collapse — the gauge-projection, fibers, and the free fiber-involution -/

/-- The `×2` involution `complement` fixes the gauge (acts within fibers). -/
@[simp] theorem TapePosition.complement_algebraic (p : TapePosition) :
    p.complement.algebraic = p.algebraic := rfl

/-- **The `×2` involution is free** — `p.complement ≠ p` for every color. `complement` flips the
    observer-face, which has no fixed point (`read ≠ write`), so the read/write doubling's `ℤ/2` acts
    *freely* on the 6 colors (3 orbits of size 2 = the 3 gauge-clusters). This is structurally *unlike*
    brick 24's base reflection `AlgebraicPosition.reflect`, which fixes `g3`: the doubling `ℤ/2` is the
    *fiber* involution, not the *base* one. -/
theorem TapePosition.complement_ne (p : TapePosition) : p.complement ≠ p := by
  cases p with
  | mk a o => cases o <;> simp [TapePosition.complement, ObserverState.flip]

/-- **The 6→3 collapse is surjective** — every gauge is the projection of some color (its read-face).
    The gauge-projection `TapePosition.algebraic` is the 6→3 collapse (forget the observer-face). -/
theorem algebraic_surjective : Function.Surjective TapePosition.algebraic :=
  fun g => ⟨⟨g, ObserverState.read⟩, rfl⟩

/-- **Each fiber of the collapse is a `{read, write}` pair** — `p.algebraic = q.algebraic ↔ q = p ∨ q =
    p.complement`. The 6→3 collapse is exactly 2:1: the two colors over each gauge are a color and its
    `complement`. So the clusters are the `complement`-orbits, and `complement` is the within-cluster
    `×2`. -/
theorem algebraic_eq_iff (p q : TapePosition) :
    p.algebraic = q.algebraic ↔ q = p ∨ q = p.complement := by
  constructor
  · intro h
    cases p with
    | mk a o =>
      cases q with
      | mk b o' =>
        cases h
        cases o <;> cases o' <;> simp [TapePosition.complement, ObserverState.flip]
  · rintro (rfl | rfl) <;> rfl

/-! ## `self_dual_iff_three` — why the `×2` is a *balanced* doubling

The 6 colors are 3 read-faces + 3 write-faces. Read-faces index the **observation-space** directions
(the gauges, rank `k = 3`); for one write-face per gauge to exhaust the **write-space** (dimension
`C(k, 2)`, `Rank.lean`), the doubling must be balanced: `C(k, 2) = k`. By `self_dual_iff_three` this
holds iff `k = 3`. -/

/-- **The `×2` is balanced iff there are 3 gauges** — `Nat.choose (card gauges) 2 = card gauges ↔ card
    gauges = 3`, i.e. `self_dual_iff_three` read at the gauge-count. The write-direction count
    `C(#gauges, 2)` (`Rank.lean`'s write-space dimension) equals the read-direction count `#gauges` (the
    observation-space dimension) **exactly at the self-dual rank 3** — so the read/write doubling is a
    balanced 2-fold cover (and the 6→3 collapse a clean 2:1) *because of* rank-3 self-duality. The exact
    mirror of brick 27's `commitmentSquare_eq_missing_iff_untamped` (the `+1` corner special to the
    source). -/
theorem balanced_doubling_iff_three :
    Nat.choose (Fintype.card AlgebraicPosition) 2 = Fintype.card AlgebraicPosition
      ↔ Fintype.card AlgebraicPosition = 3 :=
  self_dual_iff_three _ (by rw [card_algebraicPosition]; decide)

/-- **The doubling is balanced** — `C(#gauges, 2) = #gauges`, the resolved `self_dual_iff_three` at 3
    gauges. Three read-faces, three write-faces, paired by `complement`. -/
theorem writeDirections_eq_observationDirections :
    Nat.choose (Fintype.card AlgebraicPosition) 2 = Fintype.card AlgebraicPosition :=
  balanced_doubling_iff_three.mpr card_algebraicPosition

/-! ## The `+1` side — `SeedGauge ≃ Option AlgebraicPosition` (brick 27's corner, via the rigid bridge)

The seed side extends the 3-gauge core by a single point — `Option = · ⊕ Unit`, the un-tamped
`untamped` adjoined. The 3-core matching is brick 25's rigid bridge `signAlgebraicEquiv'`. -/

/-- `SeedGauge ≃ Option SeedSign` — the 4-element commitment-lattice as the 3-element `SeedSign` plus a
    point (`untamped ↦ none`). This is the `+1`: a coproduct with a point. -/
def seedGaugeEquivOptionSign : SeedGauge ≃ Option SeedSign where
  toFun := fun g => match g with
    | .untamped => none
    | .plus => some .plus
    | .minus => some .minus
    | .zero => some .zero
  invFun := fun o => match o with
    | none => .untamped
    | some .plus => .plus
    | some .minus => .minus
    | some .zero => .zero
  left_inv := by intro g; cases g <;> rfl
  right_inv := by intro o; cases o with | none => rfl | some s => cases s <;> rfl

/-- **The seed-side `+1`, matched to the gauges by the rigid bridge** — `SeedGauge ≃ Option
    AlgebraicPosition`, via `seedGaugeEquivOptionSign` then brick 25's forced orientation
    `signAlgebraicEquiv'` (`untamped ↦ none`, `+ ↦ some g2`, `− ↦ some g1`, `0 ↦ some g3`). The
    un-tamped corner is the adjoined point `none`; the three commitments are `some` of their forced
    gauges. -/
def seedGaugeEquivOptionAlgebraic : SeedGauge ≃ Option AlgebraicPosition :=
  seedGaugeEquivOptionSign.trans (Equiv.optionCongr signAlgebraicEquiv')

/-! ## The confrontation — `3 × 2` (FTPG, `card_prod`) vs `3 + 1` (seed, `card_option`) -/

/-- **The `×2`, as a cardinality** — `card TapePosition = card AlgebraicPosition * card ObserverState`,
    the FTPG-side extension *is* `Fintype.card_prod`: the 3-gauge core doubled by the 2 observer-faces. -/
theorem card_tape_eq_gauges_mul_observers :
    Fintype.card TapePosition = Fintype.card AlgebraicPosition * Fintype.card ObserverState := by
  rw [Fintype.card_congr tapeColorEquivProd, Fintype.card_prod]

/-- The 6 colors: `card TapePosition = 6 = 3 × 2`. -/
theorem card_tapePosition : Fintype.card TapePosition = 6 := by
  rw [card_tape_eq_gauges_mul_observers, card_algebraicPosition, card_observerState]

/-- **The `+1`, as a cardinality** — `card SeedGauge = card AlgebraicPosition + 1`, the seed-side
    extension *is* `Fintype.card_option`: the 3-gauge core plus the un-tamped point. Confront against
    `card_tape_eq_gauges_mul_observers`: `3 + 1 = 4` (corner) vs `3 × 2 = 6` (face) — the two ways the
    shared 3-core is extended, `card_option` vs `card_prod`, both now typed. -/
theorem card_seedGauge_eq_gauges_add_one :
    Fintype.card SeedGauge = Fintype.card AlgebraicPosition + 1 := by
  rw [Fintype.card_congr seedGaugeEquivOptionAlgebraic, Fintype.card_option]

end Foam
