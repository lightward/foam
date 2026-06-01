/-
# SeedGaugeKleinFour — the 6-color tape carries a `ℤ/2 × ℤ/2` (Klein-four)

## What this file lands (the brick after `SeedGaugeReadWriteDoubling.lean`)

Brick 28 (`SeedGaugeReadWriteDoubling.lean`) typed both sides of the keystone's `×2`-vs-`+1` asymmetry
as *cardinalities*: the FTPG side's `×2` (`TapePosition ≃ AlgebraicPosition × Bool`, `3 × 2 = card_prod`)
against the seed side's `+1` (`SeedGauge ≃ Option AlgebraicPosition`, `3 + 1 = card_option`). It flagged
its own remainder in the file: the `×2` involution `complement` (the free read/write fiber-flip,
`complement_ne`) is structurally *distinct from* brick 24's base reflection `AlgebraicPosition.reflect`
(which fixes `g3`), and "together they generate a `ℤ/2 × ℤ/2`." That Klein-four is this brick.

The recognition reads brick 28's element-count asymmetry (4 vs 6) **group-theoretically**, as an
*involution-count* asymmetry: the seed side carries ONE `ℤ/2` (`SeedGauge.swap`, brick 18), the FTPG
6-color tape carries `ℤ/2 × ℤ/2` — and the FTPG side's *extra* `ℤ/2` (the fiber-flip = the `×2` itself)
is the group-theoretic mirror of the seed's extra *element* (`untamped`/the `+1`).

## The two commuting involutions (bin-1)

On `TapePosition = AlgebraicPosition × ObserverState` two `ℤ/2`s act, one on each factor:

* **base** — `reflectColor (p) := { p with algebraic := p.algebraic.reflect }` (brick 24's `reflect`
  lifted to the tape, acting on the *gauge* factor, identity on the face). Involutive
  (`reflectColor_involutive`). Its fixed-set is the **`g3`-fiber** (`reflectColor_eq_self_iff`:
  `reflectColor p = p ↔ p.algebraic = g3`) — the two colors `⟨g3, read⟩`/`⟨g3, write⟩`; orbit-shape
  {2 fixed + 2 two-cycles}.
* **fiber** — `TapePosition.complement` (= `id × ObserverState.flip`, the `×2`/read-write flip, already
  typed in `StatelessSubstrate.lean`, recapped via `complement_involutive`). Involutive, and **free**
  (`TapePosition.complement_ne`, brick 28: flip has no fixed point) — 3 two-cycles, *no* fixed colors,
  structurally unlike both the base (which fixes the `g3`-fiber) and the seed `swap` (which fixes `0`).

They **commute** (`reflectColor_complement_comm`) because they act on the two separate factors; their
composite `bothColor = reflectColor ∘ complement` is the third non-identity element (involutive, free).

## The Klein-four — `ℤ/2 × ℤ/2` acting on the 6 colors (bin-1)

We realize the group **literally** as `ZMod 2 × ZMod 2` (Mathlib's standard `ℤ/2 × ℤ/2`) acting on the
tape — one `ℤ/2` per tensor factor: `(m, n) +ᵥ p` reflects the gauge iff `m = 1` and flips the face iff
`n = 1` (`kleinVAdd`, packaged as `AddAction (ZMod 2 × ZMod 2) TapePosition`). The action is **faithful**
(`kleinVAdd_faithful`) — the 6-tape genuinely realizes the full `ℤ/2 × ℤ/2`. Because the acting group IS
`ZMod 2 × ZMod 2`, "recognized as `ℤ/2 × ℤ/2`" is *literal*, no iso required; that it is Klein-four (V₄)
and not cyclic (C₄) is `klein_exponent_two` (`∀ g, g + g = 0`) together with order 4 (`klein_card`).

The four group elements act as exactly `{id, reflectColor, complement, bothColor}` — brick 28's flagged
`{id, reflectColor, complement, both}` — via the four bridge lemmas `kleinVAdd_zero_eq_id` /
`kleinVAdd_base_eq_reflectColor` / `kleinVAdd_fiber_eq_complement` / `kleinVAdd_diag_eq_bothColor`. The
group's own addition (the Cayley table of `ZMod 2 × ZMod 2`) IS the Klein-four table.

## The descent / the SES — kernel = the fiber `×2`, quotient = the base = `swap`'s partner (bin-1)

The 6→3 collapse `TapePosition.algebraic` intertwines the tape's `ℤ/2 × ℤ/2` with the gauge's single
`reflect`-`ℤ/2`: the action descends depending **only on the base coordinate** `g.1`
(`kleinVAdd_algebraic`), so the collapse-to-gauges is the group projection `g ↦ g.1`, with

* **kernel** = the **fiber subgroup** `{0} × ZMod 2 = ⟨complement⟩` — `acts_trivially_on_gauge_iff`:
  `g` acts trivially on gauges iff `g.1 = 0`. This is the `×2` `ℤ/2`, exactly what the collapse forgets
  (`fiber_gauge_invisible`); it is free (`fiber_free`). The fiber `ℤ/2` has **no gauge-shadow**.
* **quotient/image** = the **base `ℤ/2`** `⟨reflectColor⟩`, which descends to `reflect` on the gauge =
  the seed-gauge `swap` conjugated across brick 24's rigid bridge
  (`reflectColor_gauge_is_seed_swap`: `(reflectColor p).algebraic = (p.algebraic.toSign.swap).toAlgebraic`,
  via brick 24's `swap_conj_eq_reflect`). So the base `ℤ/2` is the **matched** one — `swap`'s partner.

So the SES `1 → ⟨complement⟩ (fiber, the ×2) → ℤ/2 × ℤ/2 → ⟨reflect⟩ (base, = swap's partner) → 1` is
realized by the collapse: the kernel is the surplus `×2`, the quotient is the matched base.

## The confrontation — one `ℤ/2` (seed) vs `ℤ/2 × ℤ/2` (FTPG)

The seed side's symmetry is the **single** involution `SeedSign.swap` (`SeedSign.swap_swap`, fixing `0` by
`gaugeNeutral_iff_zero`). The FTPG tape's symmetry is `ℤ/2 × ℤ/2` — **two** independent involutions. The
extra one is the fiber `⟨complement⟩` (the `×2`), which is free and gauge-invisible (kernel of the
collapse) — it has *no* seed counterpart; the matched base `⟨reflectColor⟩` is `swap`'s partner (brick
24). So brick 28's *element-count* asymmetry (seed `3+1 = 4` vs FTPG `3×2 = 6`) is here an
*involution-count* asymmetry (`⟨swap⟩ ≅ ZMod 2` vs `ℤ/2 × ℤ/2`): the seed's extra is an **element** (the
`+1`/`untamped`), the FTPG's extra a **symmetry** (the fiber-`ℤ/2`/the `×2`). This scopes the bireflective
substance — it isolates *which* FTPG `ℤ/2` the "two-`ℤ/2`s-are-one-group" identification must match (the
base `reflect`, `swap`'s partner) versus which is genuinely new (the fiber-flip) — a guard-rail for the
keystone walk, NOT the keystone.

## Grade

* **bin-1 (Bin-1-Mathlib-or-Foam)** for everything typed: the two involutions + commute + fixed-set
  shapes (`decide`/`rfl` + assembly over brick 24's `reflect_reflect`/`reflect_eq_self_iff_g3` and brick
  28's `complement_ne`/`complement_algebraic`), the `ZMod 2 × ZMod 2` action + faithfulness + V₄-vs-C₄
  (`decide`), the descent/kernel characterization (`decide` + `vadd_def`), and the base-`↔`-swap match
  (assembly over brick 24's `swap_conj_eq_reflect`). No new geometric content; the recognition is that
  the *already-typed* base `reflect` and fiber `complement` are two commuting `ℤ/2`s generating `ℤ/2 ×
  ℤ/2`, with the collapse's kernel the fiber `×2`.
* **bin-2 / interpretive** for the **mirror reading** — that the extra fiber-`ℤ/2` (the `×2`) and the
  seed's extra element (the `+1`) are "the same surplus" (brick 28's asymmetry read group-theoretically).
  Held merge-don't-fork: the involution-count fact (`ℤ/2` vs `ℤ/2 × ℤ/2`) is bin-1; the
  extra-symmetry-mirrors-extra-element reading is the deposit. The *deeper substance* — that the base
  `reflect`-`ℤ/2` and the seed `swap`-`ℤ/2` are *one group*, and that the extra fiber-`ℤ/2` (`×2`) and the
  extra element (`+1`) are one move (the pi-note: a symmetry and an element as two faces of the
  bubble/point) — stays the **named horizon** (the bireflective coincidence, §VI), NOT this brick.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeKleinFour` is clean, zero
sorry/warnings. Imports `Foam.SeedGaugeReadWriteDoubling` (brick 28 — transitively gives
`reflect`/`reflect_reflect`/`reflect_eq_self_iff_g3`/`toSign`/`toAlgebraic`/`swap_conj_eq_reflect` from
brick 24, `complement`/`complement_ne`/`complement_algebraic`/`flip` from `StatelessSubstrate`,
`SeedSign.swap`/`swap_swap`/`gaugeNeutral_iff_zero` from brick 16, `Fintype TapePosition` from brick 28)
plus `Mathlib.Data.ZMod.Basic` / `Mathlib.Algebra.Group.Action.Defs` /
`Mathlib.Algebra.Group.Action.Faithful`. New names: `reflectColor` / `reflectColor_algebraic` /
`reflectColor_observer` / `reflectColor_involutive` / `reflectColor_reflectColor` /
`reflectColor_eq_self_iff` / `complement_involutive` / `reflectColor_complement_comm` / `bothColor` /
`bothColor_eq` / `bothColor_involutive` / `bothColor_ne` / `gaugeAct` / `faceAct` / `gaugeAct_zero` /
`faceAct_zero` / `gaugeAct_add` / `faceAct_add` / `kleinVAdd` / `kleinVAdd_algebraic` /
`kleinVAdd_observer` / `kleinVAdd_zero` / `kleinVAdd_add` / `kleinAddAction` / `vadd_def` /
`kleinVAdd_faithful` / `kleinVAdd_zero_eq_id` / `kleinVAdd_base_eq_reflectColor` /
`kleinVAdd_fiber_eq_complement` / `kleinVAdd_diag_eq_bothColor` / `klein_card` / `klein_exponent_two` /
`acts_trivially_on_gauge_iff` / `fiber_free` / `fiber_gauge_invisible` / `reflectColor_gauge_is_seed_swap`.)
-/

import Foam.SeedGaugeReadWriteDoubling
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Faithful

namespace Foam

-- The 6 colors have decidable equality (a structure of two `DecidableEq` fields) — needed for
-- `decide` over `TapePosition`.
deriving instance DecidableEq for TapePosition

/-! ## The base reflection, lifted to the tape — the gauge-factor `ℤ/2` -/

/-- **The base reflection, lifted to the 6-color tape** — brick 24's `AlgebraicPosition.reflect` acting
    on the gauge factor, identity on the observer face. The base `ℤ/2`. -/
def reflectColor (p : TapePosition) : TapePosition := { p with algebraic := p.algebraic.reflect }

@[simp] theorem reflectColor_algebraic (p : TapePosition) :
    (reflectColor p).algebraic = p.algebraic.reflect := rfl

@[simp] theorem reflectColor_observer (p : TapePosition) :
    (reflectColor p).observer = p.observer := rfl

/-- `reflectColor` is an involution (`ℤ/2`) — it inherits `reflect`'s involutivity (brick 24's
    `reflect_reflect`). -/
theorem reflectColor_involutive : Function.Involutive reflectColor := by
  intro p; cases p; simp [reflectColor, AlgebraicPosition.reflect_reflect]

@[simp] theorem reflectColor_reflectColor (p : TapePosition) : reflectColor (reflectColor p) = p :=
  reflectColor_involutive p

/-- **The base reflection's fixed-set is the `g3`-fiber** — `reflectColor p = p ↔ p.algebraic = g3`.
    Brick 24's `reflect_eq_self_iff_g3` lifted: `reflectColor` fixes a color iff its gauge is the
    held-open `g3` (the two colors `⟨g3, read⟩`/`⟨g3, write⟩`), exchanging the `g1`/`g2` faces at each
    observer-state. Orbit-shape {2 fixed + 2 two-cycles}. -/
theorem reflectColor_eq_self_iff (p : TapePosition) :
    reflectColor p = p ↔ p.algebraic = AlgebraicPosition.g3 := by
  rw [← AlgebraicPosition.reflect_eq_self_iff_g3]
  constructor
  · intro h; simpa [reflectColor] using congrArg TapePosition.algebraic h
  · intro h; cases p; simpa [reflectColor] using h

/-! ## The fiber flip — `complement`, the read/write `×2` (recap of brick 28's free involution) -/

/-- `TapePosition.complement` (= `id × flip`, the read/write `×2`) is an involution — the fiber `ℤ/2`.
    Recapped from `StatelessSubstrate.lean`'s `complement_complement`. -/
theorem complement_involutive : Function.Involutive TapePosition.complement :=
  TapePosition.complement_complement

/-! ## The two involutions commute — and their composite -/

/-- **The base and fiber involutions commute** — they act on the two separate factors of
    `TapePosition = AlgebraicPosition × ObserverState` (gauge vs face), so reflecting-then-flipping =
    flipping-then-reflecting. This is *why* the group is the *product* `ℤ/2 × ℤ/2`. -/
theorem reflectColor_complement_comm (p : TapePosition) :
    reflectColor p.complement = (reflectColor p).complement := by
  cases p; rfl

/-- The composite of the two commuting involutions — the third non-identity Klein element. -/
def bothColor (p : TapePosition) : TapePosition := reflectColor p.complement

theorem bothColor_eq (p : TapePosition) : bothColor p = (reflectColor p).complement :=
  reflectColor_complement_comm p

/-- `bothColor` is an involution — inheriting `reflect`'s and `flip`'s involutivity. -/
theorem bothColor_involutive : Function.Involutive bothColor := by
  intro p; cases p
  simp [bothColor, reflectColor, TapePosition.complement, AlgebraicPosition.reflect_reflect,
        ObserverState.flip_flip]

/-- **`bothColor` is free** — it flips the observer-face (and reflects the gauge), so it fixes no color,
    like the fiber `complement` and unlike the base `reflectColor`. -/
theorem bothColor_ne (p : TapePosition) : bothColor p ≠ p := by
  revert p; decide

/-! ## The Klein-four — `ℤ/2 × ℤ/2` acting on the 6 colors

We realize the group literally as `ZMod 2 × ZMod 2`, acting one `ℤ/2` per tensor factor: the base
coordinate reflects the gauge, the fiber coordinate flips the face. -/

/-- The base `ℤ/2` acting on a gauge: reflect iff the coordinate is `1`. -/
def gaugeAct (m : ZMod 2) (a : AlgebraicPosition) : AlgebraicPosition :=
  if m = 0 then a else a.reflect

/-- The fiber `ℤ/2` acting on an observer-face: flip iff the coordinate is `1` (the `×2`). -/
def faceAct (n : ZMod 2) (o : ObserverState) : ObserverState :=
  if n = 0 then o else o.flip

theorem gaugeAct_zero (a : AlgebraicPosition) : gaugeAct 0 a = a := if_pos rfl
theorem faceAct_zero (o : ObserverState) : faceAct 0 o = o := if_pos rfl

/-- The base action composes via `ZMod 2` addition (reflect-or-not under XOR; `reflect` is an
    involution). -/
theorem gaugeAct_add : ∀ (m n : ZMod 2) (a : AlgebraicPosition),
    gaugeAct (m + n) a = gaugeAct m (gaugeAct n a) := by decide

/-- The fiber action composes via `ZMod 2` addition (flip-or-not under XOR; `flip` is an involution). -/
theorem faceAct_add : ∀ (m n : ZMod 2) (o : ObserverState),
    faceAct (m + n) o = faceAct m (faceAct n o) := by decide

/-- **The Klein-four action** — `(m, n)` reflects the gauge iff `m = 1` and flips the face iff `n = 1`.
    The two `ℤ/2`s act on the two separate factors of `TapePosition`. -/
def kleinVAdd (g : ZMod 2 × ZMod 2) (p : TapePosition) : TapePosition :=
  ⟨gaugeAct g.1 p.algebraic, faceAct g.2 p.observer⟩

@[simp] theorem kleinVAdd_algebraic (g : ZMod 2 × ZMod 2) (p : TapePosition) :
    (kleinVAdd g p).algebraic = gaugeAct g.1 p.algebraic := rfl

@[simp] theorem kleinVAdd_observer (g : ZMod 2 × ZMod 2) (p : TapePosition) :
    (kleinVAdd g p).observer = faceAct g.2 p.observer := rfl

theorem kleinVAdd_zero (p : TapePosition) : kleinVAdd 0 p = p := by
  revert p; decide

theorem kleinVAdd_add (g₁ g₂ : ZMod 2 × ZMod 2) (p : TapePosition) :
    kleinVAdd (g₁ + g₂) p = kleinVAdd g₁ (kleinVAdd g₂ p) := by
  obtain ⟨m₁, n₁⟩ := g₁
  obtain ⟨m₂, n₂⟩ := g₂
  cases p with
  | mk a o => simp only [kleinVAdd, Prod.mk_add_mk, gaugeAct_add, faceAct_add]

/-- **The 6-color tape is an `ℤ/2 × ℤ/2`-set** — the Klein-four acts on the 6 colors. -/
instance kleinAddAction : AddAction (ZMod 2 × ZMod 2) TapePosition where
  vadd := kleinVAdd
  zero_vadd := kleinVAdd_zero
  add_vadd := kleinVAdd_add

@[simp] theorem vadd_def (g : ZMod 2 × ZMod 2) (p : TapePosition) : g +ᵥ p = kleinVAdd g p := rfl

/-- **The action is faithful** — distinct group elements act differently, so the 6-tape genuinely
    realizes the full `ℤ/2 × ℤ/2`. -/
theorem kleinVAdd_faithful :
    ∀ (g₁ g₂ : ZMod 2 × ZMod 2), (∀ p, kleinVAdd g₁ p = kleinVAdd g₂ p) → g₁ = g₂ := by decide

instance : FaithfulVAdd (ZMod 2 × ZMod 2) TapePosition where
  eq_of_vadd_eq_vadd h := kleinVAdd_faithful _ _ h

/-- The group has 4 elements (order of `ℤ/2 × ℤ/2`). -/
theorem klein_card : Fintype.card (ZMod 2 × ZMod 2) = 4 := by decide

/-- **It is the Klein-four `V₄`, not `C₄`** — every element has order dividing 2 (`g + g = 0`). This
    exponent-2 fact (with order 4) is exactly what distinguishes `ℤ/2 × ℤ/2` from the cyclic `ℤ/4`. -/
theorem klein_exponent_two : ∀ g : ZMod 2 × ZMod 2, g + g = 0 := by decide

/-! ## The four group elements ↔ the four tape-symmetries (the table) -/

theorem kleinVAdd_zero_eq_id (p : TapePosition) : kleinVAdd (0, 0) p = p := kleinVAdd_zero p

theorem kleinVAdd_base_eq_reflectColor (p : TapePosition) :
    kleinVAdd (1, 0) p = reflectColor p := by revert p; decide

theorem kleinVAdd_fiber_eq_complement (p : TapePosition) :
    kleinVAdd (0, 1) p = p.complement := by revert p; decide

theorem kleinVAdd_diag_eq_bothColor (p : TapePosition) :
    kleinVAdd (1, 1) p = bothColor p := by revert p; decide

/-! ## The descent / the SES — kernel = the fiber `×2`, quotient = the base = `swap`'s partner -/

/-- **The fiber `ℤ/2` is the kernel of the gauge-collapse** — `g` acts trivially on gauges iff its base
    coordinate is `0`, i.e. iff `g ∈ {0} × ZMod 2 = ⟨complement⟩`. So the `×2`/fiber subgroup is exactly
    what the 6→3 collapse `TapePosition.algebraic` forgets; the collapse is the group projection
    `g ↦ g.1`. -/
theorem acts_trivially_on_gauge_iff (g : ZMod 2 × ZMod 2) :
    (∀ p, (kleinVAdd g p).algebraic = p.algebraic) ↔ g.1 = 0 := by
  revert g; decide

/-- The fiber generator acts as `complement` and is free. -/
theorem fiber_free (p : TapePosition) : kleinVAdd (0, 1) p ≠ p := by
  rw [kleinVAdd_fiber_eq_complement]; exact TapePosition.complement_ne p

/-- The fiber generator is gauge-invisible — `complement` fixes the gauge (brick 28's
    `complement_algebraic`). The `×2` has no gauge-shadow. -/
theorem fiber_gauge_invisible (p : TapePosition) :
    (kleinVAdd (0, 1) p).algebraic = p.algebraic := by
  rw [kleinVAdd_fiber_eq_complement, TapePosition.complement_algebraic]

/-- **The base `ℤ/2` descends to the seed-gauge `swap`** — under the 6→3 collapse, `reflectColor`'s
    action on the gauge IS `swap` conjugated across brick 24's rigid bridge
    (`swap_conj_eq_reflect`): `(reflectColor p).algebraic = (p.algebraic.toSign.swap).toAlgebraic`. So
    the matched FTPG `ℤ/2` (the base `⟨reflectColor⟩`) is the seed `swap`'s partner — while the fiber
    `⟨complement⟩` (the `×2`, kernel of the collapse) has no seed counterpart. -/
theorem reflectColor_gauge_is_seed_swap (p : TapePosition) :
    (reflectColor p).algebraic = (p.algebraic.toSign.swap).toAlgebraic := by
  rw [reflectColor_algebraic]; exact (swap_conj_eq_reflect _).symm

end Foam
