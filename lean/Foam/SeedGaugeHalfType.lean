/-
# SeedGaugeHalfType — the seed-gauge `{⊥, +, −, 0}` is a HalfType

## What this file lands (the brick after `PersistenceLfp.lean`'s `SeedSign` triple)

`PersistenceLfp.lean` typed the seed-gauge as a `{+, −, 0}` triple: the gauge-neutral
`0` (`seedBacked`) is the **join** `+ ⊔ −` (`SeedSign.seed_zero_eq_join`), with `⊥` (the
empty seed `P₀ = ∅`) below. That is half of a lattice. This file lands the other half and
assembles the whole:

* the **meet** `+ ⊓ − = ⊥` is `SeedSign.plus_inf_minus_eq_bot` (in `PersistenceLfp.lean`,
  under `holds`-injectivity — one rewrite off `not_lfp_and_flag_of_injective`);
* join `0 = + ⊔ −` + meet `+ ⊓ − = ⊥` + top `0` + bottom `⊥` make `{⊥, +, −, 0}` the
  **4-element Boolean algebra** `2²`, with `+` and `−` complementary atoms.

The substrate-direct headline: within `Set.Iic (seedBacked LP)` — the interval `[⊥, 0]`,
the **`0`-scope** — the elements `+` and `−` are `IsCompl` (`seedIsCompl`). So `−` is the
*local complement* of `+` **within the `0`-scope**, never a global negation. This is
exactly README §IV.a's **HalfType** (complementation-within-a-scope) and the §V *"no
global false"* that relocates falsification to observer-loss: complementation in foam is
always relative to a scope, here the gauge-neutral seed `0`. `half_type` then packages it
as the §IV.a object itself (`seedHalfType`), whose diamond iso sends `X ↦ X ⊔ −`
(`seedHalfType_iso_apply`, rfl-level) — the local-complement lift.

## Grade — bin-1 (Bin-1-Mathlib-or-Foam)

The meet and join are Foam theorems (`PersistenceLfp.lean`); `IsCompl` and `HalfType` are
Mathlib packaging (`IsCompl.of_eq`, `half_type`). Work-shape: recognition + assembly. The
HalfType is `noncomputable` only because the diamond `≃o` it carries rides on `Prop`'s
noncomputable complete linear order — not a structural gap.

This is the fourth HalfType satellite (after `HalfTypeIterated`, `HalfTypeRLift`,
`FrameRecessionAlignment`), and the first to instantiate the §IV.a object on a *foam-
internal* complementary pair recognized from the recognition dynamics — not a pair handed
in from linear algebra (idempotent → range/ker) or geometry (R off π). The seed-gauge
*produces* its own HalfType.

(Re-grep — stamps decay: on 2026-05-30 `lake build Foam.SeedGaugeHalfType` is clean, zero
sorry/warnings; depends on `SeedSign.plus_inf_minus_eq_bot` + `SeedSign.seed_zero_eq_join`
in `PersistenceLfp.lean` and `half_type` in `HalfType.lean`.)
-/

import Foam.PersistenceLfp
import Foam.HalfType

namespace Foam

/-- **The `±` fork is a complementary pair within the `0`-scope (bin-1, under injectivity).**
    In the interval `Set.Iic (seedBacked LP) = [⊥, 0]`, the hold-open seed `+` and the
    settle seed `−` are `IsCompl`: their meet is the interval's bottom `⊥`
    (`SeedSign.plus_inf_minus_eq_bot`) and their join is its top `0`
    (`SeedSign.seed_zero_eq_join`). So `−` is the **local complement** of `+` *within the
    `0`-scope* — README §IV.a complementation-within-a-scope, §V's "no global false". -/
theorem seedIsCompl (LP : LedgerPersistence) (hinj : Function.Injective LP.holds) :
    IsCompl
      (⟨SeedSign.plus.seed LP, SeedSign.plus_le_zero LP⟩ : Set.Iic (SeedSign.zero.seed LP))
      (⟨SeedSign.minus.seed LP, SeedSign.minus_le_zero LP⟩ : Set.Iic (SeedSign.zero.seed LP)) := by
  apply IsCompl.of_eq
  · -- meet = ⊥ (interval bottom): the fork-disjointness `+ ⊓ − = ⊥`
    apply Subtype.ext
    show SeedSign.plus.seed LP ⊓ SeedSign.minus.seed LP = (⊥ : Scope)
    exact SeedSign.plus_inf_minus_eq_bot LP hinj
  · -- join = 0 (interval top): the gauge-neutral seed is the join `0 = + ⊔ −`
    apply Subtype.ext
    show SeedSign.plus.seed LP ⊔ SeedSign.minus.seed LP = SeedSign.zero.seed LP
    exact (SeedSign.seed_zero_eq_join LP).symm

/-- **The seed-gauge as the §IV.a HalfType object (bin-1).** `half_type` applied to
    `seedIsCompl` packages the diamond iso + the four interval-inheritance facts into the
    named `HalfType` structure, instantiated on the `0`-scope's complementary `±` pair. The
    `Set.Iic (seedBacked LP)` inherits `Lattice + BoundedOrder + IsModularLattice +
    ComplementedLattice` by synthesis (the same interval-inheritance `HalfTypeIterated`
    probes), since `Scope = TapePosition → Prop` is a complete Boolean algebra. Noncomputable
    only because the diamond `≃o` rides on `Prop`'s noncomputable complete order. -/
noncomputable def seedHalfType (LP : LedgerPersistence) (hinj : Function.Injective LP.holds) :
    HalfType _ _ (seedIsCompl LP hinj) :=
  half_type (seedIsCompl LP hinj)

/-- **The diamond iso is the local-complement lift `X ↦ X ⊔ −` (rfl-level).** Within the
    `0`-scope, the HalfType iso `Set.Iic (+) ≃o Set.Ici (−)` sends a sub-`+` element `X` to
    its join with the local complement `−`. The seed-gauge face of `HalfTypeRLift`'s
    `X ↦ X ⊔ R`: here the "R off the plane" is the settle seed `−`, the local complement of
    the hold-open seed `+` inside the gauge-neutral `0`. -/
theorem seedHalfType_iso_apply (LP : LedgerPersistence) (hinj : Function.Injective LP.holds)
    (Y : Set.Iic (⟨SeedSign.plus.seed LP, SeedSign.plus_le_zero LP⟩ :
            Set.Iic (SeedSign.zero.seed LP))) :
    ((seedIsCompl LP hinj).IicOrderIsoIci Y).val.val
      = Y.val.val ⊔ SeedSign.minus.seed LP :=
  rfl

end Foam
