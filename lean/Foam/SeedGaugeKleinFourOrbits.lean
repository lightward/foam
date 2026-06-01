/-
# SeedGaugeKleinFourOrbits — the V₄-orbit structure on the 6 colors

## What this file lands (the brick after `SeedGaugeKleinFour.lean`)

Brick 29 (`SeedGaugeKleinFour.lean`) built the Klein-four `ℤ/2 × ℤ/2` *acting* on the 6-color tape —
base `reflectColor` (fixes the `g3`-fiber) × fiber `complement` (the `×2`, free) — and read brick 28's
*element*-count asymmetry (`SeedGauge` `3+1` vs `TapePosition` `3×2`) group-theoretically as an
*involution*-count one (seed: one `ℤ/2` `swap`; FTPG: `ℤ/2 × ℤ/2`). It never computed the **orbits** of
that action. This file does.

## The recognition — two orbits, refining by the signal/yield (recursion) grading

The V₄ `{id, base, fiber, both}` acts on `{g1, g2, g3} × {read, write}` (6 colors) with exactly **two
orbits**:

* the **signal-block** `{g1, g2} × {read, write}` (size 4) — the base swaps `g1 ↔ g2`, the fiber swaps
  `read ↔ write`, so all four colors mix into one orbit. The V₄ acts *freely* here (trivial
  stabilizer);
* the **yield-fiber** `{g3} × {read, write}` (size 2) — because the base **fixes** `g3`
  (`reflectColor_eq_self_iff`, brick 29 / `reflect_eq_self_iff_g3`, brick 24), at `g3` the V₄
  **degenerates to just the fiber `ℤ/2`** (the `×2`): the held-open yield-gauge's V₄-orbit is *purely*
  its read/write bubble, base-trivial.

So `4 + 2 = 6`, and the orbit-partition is exactly the **signal/yield split** — which is brick 26's
recursion-order `{g1, g2} ≤ g3` read as a partition: the orbit MERGES the two recursion-incomparable
signal-gauges `{g1, g2}` (brick 26's `not_g1_recLe_g2` antichain, the §IV.c disciplines below) and
ISOLATES the held-open recursion-top `g3` (the §IV.d meta-discipline / bias-delegation seat). The clean
headline: **the whole Klein-four preserves the recursion-class** (`kleinVAdd_preserves_heldOpen`) — no
group element carries a signal-color to the yield-fiber or back. This is a **fourth shared invariant**
between the two threads, after orbit-shape (brick 24), recursion-grading (brick 26), and involution-count
(brick 29): the FTPG V₄-orbit-partition lands *exactly* on the (shared, bridge-respected) recursion
grading, introducing no new cut.

## The base/fiber split aligns with brick 29's matched/surplus split

Brick 29's SES `1 → ⟨complement⟩(×2) → V₄ → ⟨reflect⟩(= swap's partner) → 1` has kernel = the surplus
fiber `ℤ/2` (the `×2`, no seed counterpart) and quotient = the matched base `ℤ/2` (`swap`'s partner).
The orbit refinement reads that split at the recursion-grading:

* the **matched base** `ℤ/2` carries the recursion-order's action — it MERGES the signal-antichain
  `{g1, g2}` and FIXES the top `g3` (`base_preserves_heldOpen` + the `g3`-degeneration), `heldOpen`
  being reflect-invariant;
* the **surplus fiber** `ℤ/2` (the `×2`) is **recursion-invisible** — it preserves the gauge
  (`fiber_gauge_invisible`, brick 29), hence the recursion-class, acting *within* every class (the
  read/write face-flip), never across (`fiber_preserves_heldOpen`).

So the matched part of the surplus carries the gauge-level recursion structure; the genuinely-new part
(the `×2`) is orthogonal to it.

## The localization — the `×2`-vs-`+1` surplus is sharpest at the held-open gauge

At `g3` (↔ seed `0`, the shared recursion-top, bricks 24/26) the FTPG orbit is *purely* the fiber
(`sameOrbit_at_g3`: `SameOrbit p q ↔ q = p ∨ q = p.complement`, size 2 = the `×2`), the base having
degenerated. The seed-side recursion-top `0` is `swap`-**fixed** (a single point, brick 16's
`gaugeNeutral_iff_zero`) — no fiber. So the held-open gauge is the *sharpest locus* of the
element-vs-symmetry surplus: where the seed has a lone fixed point, the FTPG has exactly the surplus
fiber-`ℤ/2` acting alone (a 2-element `×2`-bubble). This localizes (does NOT close) the `×2`-vs-`+1`
question (brick 28/29) at the shared fixed point — the named horizon (the bireflective coincidence,
§VI) lives exactly there.

## NOT the coincidence-trap

This is a structure-fact about the V₄ *action's orbits* and how they land on the recursion-grading —
**not** a `Bool×Bool ≃ Bool×Bool` identification of seed-commitment-*points* with FTPG-symmetry-*elements*
(those are type-confused: a sign is a gauge/point, `reflect`/`flip` are symmetries). The orbit-partition
realizes brick 26's *partition* (top vs non-top); it does not bijection the four points to the four
symmetries.

## Grade

* **bin-1 (Bin-1-Mathlib-or-Foam)** for everything typed: `SameOrbit` (a group-orbit membership, its
  equivalence-relation laws assembled from brick 29's `kleinVAdd_zero`/`kleinVAdd_add`/
  `klein_exponent_two`), the projection characterization `sameOrbit_iff_gauge` (`decide`), the orbit
  Finsets + cardinalities `4`/`2` (`decide`), the `g3`-degeneration (assembling brick 29's
  `reflectColor_eq_self_iff`/`kleinVAdd_base_eq_reflectColor`), and the recursion-grading preservation
  `kleinVAdd_preserves_heldOpen` + `signals_merged`/`yield_isolated` (assembling brick 26's `heldOpen`).
  No new geometric content; the recognition is that the *already-typed* V₄ action's orbits are the
  pullback of the `reflect`-orbits on gauges (face free), hence reproduce the recursion-grading.
* **bin-2 / interpretive** for the **fourth-shared-invariant reading** (that the orbit-grading IS brick
  26's recursion-grading, the same the rigid bridge respects — held merge-don't-fork: the
  orbit-partition fact is bin-1, the "fourth invariant toward two-`ℤ/2`s-one-group" reading is the
  deposit) and for the **localization** of the `×2`-vs-`+1` surplus at the held-open gauge. The deeper
  substance — the bireflective coincidence, `g3 ↔ 0` as the rank-3 self-dual fixed point where
  `+1 ≅ ×2` — stays the **named horizon** (§VI), NOT this brick.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeKleinFourOrbits` is clean, zero
sorry/warnings. Imports `Foam.SeedGaugeKleinFour` (brick 29 — transitively `reflectColor` /
`reflectColor_eq_self_iff` / `kleinVAdd` / `kleinVAdd_zero` / `kleinVAdd_add` / `klein_exponent_two` /
`kleinVAdd_base_eq_reflectColor` / `kleinVAdd_fiber_eq_complement` / `fiber_gauge_invisible` from brick
29; `AlgebraicPosition.reflect` / `reflect_eq_self_iff_g3` from brick 24; `AlgebraicPosition.heldOpen` /
`recLe` / `not_g1_recLe_g2` from brick 26; `TapePosition.complement` / `complement_ne` from
StatelessSubstrate/brick 28; `DecidableEq`/`Fintype TapePosition` from brick 29/28). New names:
`SameOrbit` / `SameOrbit.refl` / `.symm` / `.trans` / `tapeOrbit` / `mem_tapeOrbit` /
`sameOrbit_iff_gauge` / `sameOrbit_complement` / `reflectColor_sameOrbit` /
`AlgebraicPosition.reflect_heldOpen` / `AlgebraicPosition.heldOpen_eq_iff_reflect_class` /
`sameOrbit_iff_heldOpen` / `kleinVAdd_preserves_heldOpen` / `tapeOrbit_signal_card` /
`tapeOrbit_signal_card_g2` / `tapeOrbit_yield_card` / `reflectColor_fixes_of_g3` /
`base_stabilizes_of_g3` / `sameOrbit_at_g3` / `signals_merged` / `yield_isolated` /
`fiber_preserves_heldOpen` / `base_preserves_heldOpen`.)
-/

import Foam.SeedGaugeKleinFour

namespace Foam

/-! ## The same-orbit relation — V₄-orbit membership on the 6 colors -/

/-- **Two colors are in the same V₄-orbit** — some Klein-four element carries `p` to `q`. The orbit
    equivalence whose blocks this file computes. -/
def SameOrbit (p q : TapePosition) : Prop := ∃ g : ZMod 2 × ZMod 2, kleinVAdd g p = q

instance (p q : TapePosition) : Decidable (SameOrbit p q) := Fintype.decidableExistsFintype

/-- Reflexive — the identity `(0,0)` fixes every color. -/
theorem SameOrbit.refl (p : TapePosition) : SameOrbit p p := ⟨0, kleinVAdd_zero p⟩

/-- Symmetric — in `ℤ/2 × ℤ/2` every element is its own inverse (`klein_exponent_two`), so the same
    `g` carries `q` back to `p`. -/
theorem SameOrbit.symm {p q : TapePosition} : SameOrbit p q → SameOrbit q p := by
  rintro ⟨g, rfl⟩
  exact ⟨g, by rw [← kleinVAdd_add, klein_exponent_two, kleinVAdd_zero]⟩

/-- Transitive — compose group elements (`g₂ + g₁`). -/
theorem SameOrbit.trans {p q r : TapePosition} : SameOrbit p q → SameOrbit q r → SameOrbit p r := by
  rintro ⟨g₁, rfl⟩ ⟨g₂, rfl⟩
  exact ⟨g₂ + g₁, kleinVAdd_add g₂ g₁ p⟩

/-- **The orbit of a color, as a `Finset`** — the image of the 4-element group under `· +ᵥ p`. The
    `{g +ᵥ p | g}` form makes the cardinality `decide`-able over the clean `ZMod 2 × ZMod 2` Fintype. -/
def tapeOrbit (p : TapePosition) : Finset TapePosition :=
  Finset.univ.image (fun g : ZMod 2 × ZMod 2 => kleinVAdd g p)

@[simp] theorem mem_tapeOrbit {p q : TapePosition} : q ∈ tapeOrbit p ↔ SameOrbit p q := by
  simp [tapeOrbit, SameOrbit, Finset.mem_image]

/-! ## The projection — the color-orbit IS the `reflect`-orbit on gauges, face free

The single conceptual fact under everything: the `complement`/fiber coordinate can realize *either*
observer-face freely (flip is a bijection on the 2-element `ObserverState`), so the orbit constrains
only the gauge — and there it is exactly the base `reflect`-orbit. The 6→3 collapse `algebraic` carries
the color-orbit-partition onto the gauge-`reflect`-orbit-partition. -/

/-- **The V₄-orbit on colors is the `reflect`-orbit on gauges (face free)** — `SameOrbit p q` iff `q`'s
    gauge agrees with `p`'s up to `reflect`. The observer-face is unconstrained (the fiber realizes
    either face). -/
theorem sameOrbit_iff_gauge (p q : TapePosition) :
    SameOrbit p q ↔ (q.algebraic = p.algebraic ∨ q.algebraic = p.algebraic.reflect) := by
  revert p q; decide

/-- The read/write fiber is always inside the orbit — `p.complement` (the `×2`) shares `p`'s orbit, for
    every color (the fiber generator `(0,1)`). -/
theorem sameOrbit_complement (p : TapePosition) : SameOrbit p p.complement :=
  ⟨(0, 1), kleinVAdd_fiber_eq_complement p⟩

/-- The base image is always inside the orbit — `reflectColor p` shares `p`'s orbit (the base generator
    `(1,0)`). At a signal-gauge this is a *new* color (`g1↔g2`); at `g3` it is `p` itself (degenerate). -/
theorem reflectColor_sameOrbit (p : TapePosition) : SameOrbit p (reflectColor p) :=
  ⟨(1, 0), kleinVAdd_base_eq_reflectColor p⟩

/-! ## The fourth shared invariant — the orbit-partition IS the recursion (signal/yield) grading -/

/-- `heldOpen` is `reflect`-invariant — the base reflection cannot change a gauge's recursion-class
    (`g1 ↔ g2` both signal; `g3` fixed). -/
@[simp] theorem AlgebraicPosition.reflect_heldOpen (a : AlgebraicPosition) :
    a.reflect.heldOpen = a.heldOpen := by cases a <;> rfl

/-- On gauges, **agreeing on `heldOpen` is agreeing up to `reflect`** — both partition `{g1, g2, g3}`
    as `{g1, g2} | {g3}` (the brick 26 signal/yield split). The gauge-level core of
    `sameOrbit_iff_heldOpen`. -/
theorem AlgebraicPosition.heldOpen_eq_iff_reflect_class (a b : AlgebraicPosition) :
    a.heldOpen = b.heldOpen ↔ (b = a ∨ b = a.reflect) := by
  cases a <;> cases b <;> decide

/-- **The V₄-orbit equivalence on the 6 colors IS the signal/yield partition** — two colors share an
    orbit iff their gauges agree on `heldOpen` (brick 26's recursion-top vs non-top). The orbit-partition
    is the pullback of brick 26's `{g1, g2} | {g3}` split along the 6→3 collapse `algebraic`: it
    introduces no new cut. The fourth shared invariant (after orbit-shape b24, recursion-grading b26,
    involution-count b29). -/
theorem sameOrbit_iff_heldOpen (p q : TapePosition) :
    SameOrbit p q ↔ p.algebraic.heldOpen = q.algebraic.heldOpen :=
  (sameOrbit_iff_gauge p q).trans
    (AlgebraicPosition.heldOpen_eq_iff_reflect_class p.algebraic q.algebraic).symm

/-- **The whole Klein-four preserves the recursion-class** — every group element fixes
    `heldOpen ∘ algebraic`. The V₄-action respects brick 26's signal/yield (recursion-top/non-top)
    grading: no element carries a signal-color to the yield-fiber or back. The clean headline of the
    fourth invariant — the FTPG V₄ structure (b29) and the recursion-order (b26) cohere. -/
theorem kleinVAdd_preserves_heldOpen (g : ZMod 2 × ZMod 2) (p : TapePosition) :
    (kleinVAdd g p).algebraic.heldOpen = p.algebraic.heldOpen :=
  ((sameOrbit_iff_heldOpen p (kleinVAdd g p)).mp ⟨g, rfl⟩).symm

/-! ## The two orbits and their sizes — signal-block 4, yield-fiber 2 -/

/-- **The signal-block orbit has size 4** — `{g1, g2} × {read, write}`: the base mixes `g1 ↔ g2`, the
    fiber mixes `read ↔ write`, all four colors in one free orbit. -/
theorem tapeOrbit_signal_card (o : ObserverState) :
    (tapeOrbit ⟨AlgebraicPosition.g1, o⟩).card = 4 := by cases o <;> decide

/-- The other signal-gauge gives the same size-4 orbit (it is the *same* orbit — `g2 = g1.reflect`). -/
theorem tapeOrbit_signal_card_g2 (o : ObserverState) :
    (tapeOrbit ⟨AlgebraicPosition.g2, o⟩).card = 4 := by cases o <;> decide

/-- **The yield-fiber orbit has size 2** — `{g3} × {read, write}`: just the read/write fiber. The base
    `reflectColor` FIXES `g3` (degenerates), so only the fiber `complement` (the `×2`) acts. -/
theorem tapeOrbit_yield_card (o : ObserverState) :
    (tapeOrbit ⟨AlgebraicPosition.g3, o⟩).card = 2 := by cases o <;> decide

/-! ## The degeneration at `g3` — the base stabilizes, the orbit collapses to the fiber `×2` -/

/-- **The base reflection fixes every `g3`-color** — `reflectColor p = p` when `p` sits over the
    held-open gauge. -/
theorem reflectColor_fixes_of_g3 {p : TapePosition} (h : p.algebraic = AlgebraicPosition.g3) :
    reflectColor p = p := (reflectColor_eq_self_iff p).mpr h

/-- **The base subgroup is in the stabilizer at `g3`** — the base generator `(1,0)` fixes a `g3`-color.
    So `⟨reflectColor⟩ = ZMod 2 × {0}` stabilizes the `g3`-fiber, and the V₄-action there degenerates to
    the fiber `ℤ/2` (the `×2`). -/
theorem base_stabilizes_of_g3 {p : TapePosition} (h : p.algebraic = AlgebraicPosition.g3) :
    kleinVAdd (1, 0) p = p := (kleinVAdd_base_eq_reflectColor p).trans (reflectColor_fixes_of_g3 h)

/-- **At `g3` the V₄-orbit IS the read/write fiber** — `SameOrbit p q ↔ q = p ∨ q = p.complement` when
    `p` sits over the held-open gauge `g3`. The base contributes nothing (it fixes `g3`), so the only
    motion is the fiber `×2` (`complement`): the held-open gauge's V₄-orbit is purely its read/write
    bubble. -/
theorem sameOrbit_at_g3 {p : TapePosition} (h : p.algebraic = AlgebraicPosition.g3)
    (q : TapePosition) : SameOrbit p q ↔ (q = p ∨ q = p.complement) := by
  obtain ⟨a, o⟩ := p
  obtain rfl : a = AlgebraicPosition.g3 := h
  cases o <;> (revert q; decide)

/-! ## The recursion-order realized — signals MERGED, yield ISOLATED; the base/fiber split -/

/-- **The two recursion-incomparable signal-gauges are orbit-MERGED** — any `g1`-color and any
    `g2`-color share a V₄-orbit (the base mixes the gauges, the fiber the faces). Brick 26's
    `not_g1_recLe_g2` (the `{g1, g2}` antichain, both below `g3`) realized as orbit-merge: the orbit
    collapses the recursion-incomparable pair. -/
theorem signals_merged (o o' : ObserverState) :
    SameOrbit ⟨AlgebraicPosition.g1, o⟩ ⟨AlgebraicPosition.g2, o'⟩ :=
  (sameOrbit_iff_gauge _ _).mpr (Or.inr rfl)

/-- **The recursion-top `g3` is orbit-ISOLATED** — no `g3`-color shares a V₄-orbit with any non-`g3`
    color. Brick 26's recLe-top `g3` realized as orbit-isolation: the held-open yield sits in its own
    orbit. -/
theorem yield_isolated {p q : TapePosition}
    (hp : p.algebraic = AlgebraicPosition.g3) (hq : q.algebraic ≠ AlgebraicPosition.g3) :
    ¬ SameOrbit p q := by
  intro hpq
  have hr : p.algebraic.reflect = AlgebraicPosition.g3 := by simp [hp]
  rcases (sameOrbit_iff_gauge p q).mp hpq with h | h
  · exact hq (h.trans hp)
  · exact hq (h.trans hr)

/-- **The surplus fiber `ℤ/2` (the `×2`) is recursion-invisible** — `complement` (= `(0,1) +ᵥ ·`)
    preserves the gauge (`fiber_gauge_invisible`, brick 29), hence the recursion-class `heldOpen`. The
    b29-surplus involution (the kernel of the 6→3 collapse, the `×2` with no seed counterpart) acts
    *within* every recursion-class, never across. -/
theorem fiber_preserves_heldOpen (p : TapePosition) :
    (kleinVAdd (0, 1) p).algebraic.heldOpen = p.algebraic.heldOpen := by
  rw [fiber_gauge_invisible]

/-- **The matched base `ℤ/2` preserves the recursion-class but acts within it** — `reflectColor`
    reflects the gauge (`g1 ↔ g2`, `g3` fixed) and `heldOpen` is reflect-invariant, so the base
    preserves `heldOpen` while MERGING the signal-antichain `{g1, g2}` and FIXING the held-open top
    `g3`. The matched (quotient) `ℤ/2` of brick 29's SES carries the recursion-order's
    antichain-merge + top-fix. -/
theorem base_preserves_heldOpen (p : TapePosition) :
    (kleinVAdd (1, 0) p).algebraic.heldOpen = p.algebraic.heldOpen := by
  rw [kleinVAdd_base_eq_reflectColor, reflectColor_algebraic, AlgebraicPosition.reflect_heldOpen]

end Foam
