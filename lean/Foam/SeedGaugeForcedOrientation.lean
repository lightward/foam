/-
# SeedGaugeForcedOrientation — the within-pair gauge-orientation is FORCED by commitment-content

## What this file lands (the brick after `SeedGaugeAlgebraicPosition.lean`)

Brick 24 (`SeedGaugeAlgebraicPosition.lean`) bridged the two threads — the persistence/commitment
`SeedSign` and the FTPG/gauge `AlgebraicPosition` — through a shared `ℤ/2` (orbit-shape {1 fixed +
1 two-cycle}), and proved the fixed-point match `0 ↔ g3` **forced** by equivariance. But it typed
the **within-pair** assignment `+ ↔ g1` (`signAlgebraicEquiv`) vs `+ ↔ g2` (`signAlgebraicEquiv'`)
as a *genuine free choice* — two equivariant bijections, held open per bias-delegation — **only in
the bare `ℤ/2` structure**. Its closing remainder: *"the substrate carries an asymmetry that may
orient it, and brick 24 didn't look."*

This file looks. **It does, and the orientation is forced.**

## The substrate asymmetry, on both sides — *outstanding commitment*

There is a single binary property, present on **both** sides, that the bare involutions
(`SeedSign.swap`, `AlgebraicPosition.reflect`) do not see — **does this gauge carry an outstanding
(un-discharged) observer-commitment?** It is read straight off the two inductives' own constructor
docstrings:

* **FTPG side** (`AlgebraicPosition.needsCommitment`): `g1` (right-distrib) `false` — PROVEN
  unconditionally as `coord_mul_right_distrib` (`g1_generic`), no witness argument; `g2`
  (left-distrib) `true` — closable only *via* `DesarguesianWitness Γ` (`coord_mul_left_distrib` =
  `g2_generic`); `g3` (mul-assoc) `true` — held open (`dilation_compose_at_beta` = `g3_generic`,
  the commitment-site where the ledger lands). So `g1` is the **unique freely-closed** gauge.

* **Seed side** (`SeedSign.outstanding`): `+` (undischarged-backed) `true` — the still-owed /
  must-persist faces, `+ = LP.flag` the observer-carrying set (`plus_seed_iff_flag`, brick 13);
  `−` (discharged-backed) `false` — settled / safe-to-spend, disjoint from the observer
  (`minus_drops_observer`, brick 14); `0` (every debt-backed face) `true` — carries both signs
  uncollapsed (`zero_holdsFullSpectrum`, brick 16), `+ ≤ 0` (`plus_le_zero`). So `−` is the
  **unique fully-resolved** seed.

These are the **same property in substance** (the bin-2 recognition, below): an *undischarged debt*
(`+`) and a *required witness* (`g2`) are both a commitment whose discharge is **pending**; a
*discharged debt* (`−`) and a *freely-proven theorem* (`g1`) are both **resolved**. In foam the
observer is *present exactly as an outstanding commitment* — presence is outstanding-ness (brick 12).

## The forcing — `−↔g1`, `0↔g3`, `+↔g2`, three forcings converging

The property breaks each bare involution's within-pair symmetry: on the 2-cycle the property *flips*
(`+`/`g2` outstanding, `−`/`g1` resolved), only the fixed point preserved. It is `swap`'s/`reflect`'s
symmetry-breaker — the level of `bridge_breaks_fork_symmetry` (brick 12). A map respecting it must
send the unique-resolved to the unique-resolved: `− ↦ g1` (`commitment_preserving_minus`, the
2-cycle analogue of brick 24's `equivariant_zero`, here resolved↦resolved, *no bijectivity*).

The headline `orientation_forced`: any `e : SeedSign → AlgebraicPosition` that is **both**
`ℤ/2`-equivariant (brick 24) **and** commitment-preserving sends `+ ↦ g2`. The two constraints are
**complementary** — equivariance rigidifies the fixed point (`0 ↦ g3`), commitment-content
rigidifies the 2-cycle (`− ↦ g1`, hence `+ ↦ g2` by equivariance at `−`) — and together they force
the **unique** substrate-respecting orientation `signAlgebraicEquiv'` (`+ ↦ g2`). Brick 24's
"canonical" `signAlgebraicEquiv` (`+ ↦ g1`) is **not** commitment-preserving
(`toAlgebraic_not_commitment_preserving`: it sends the outstanding `+` to the freely-closed `g1`) —
it was the gauge-arbitrary labelling. The within-pair freedom brick 24 left open is **closed**.

Reading B (`+ ↔ g1`, "both close") dissolves: `+` closes *by committing* (the (a)↔(b) bridge
coincides only because one committed `recognizeUndischarged`), `g1` closes *without* committing
(proven outright) — opposite on the commitment axis. The surface predicate "closes" conflated
closure-by-commitment with free-closure; the load-bearing content is *commitment-status*, and on it
`+`/`g2` align and `−`/`g1` align.

## The held-both face — forced *now*, free iff the witness is discharged (merge-don't-fork)

The forcing is **conditional**, and the condition is the keystone's mind-entry locus. It holds
exactly while the FTPG-side property is non-degenerate — while `g2` genuinely *requires* the
`DesarguesianWitness`. Per the s142/s144 meta-frontier (`lean/CLAUDE.md`), that witness is an
*exhaustion finding*, **predicted bin-1** (the converse-Desargues content is Desargues-derivable in
principle), its bin-1 path an *open-recognition-target*. So:

* **Forced-now** (typed here, bin-1): in the current substrate `g2` carries the witness and `g1`
  does not; `+` carries the observer and `−` does not. The orientation is forced to `+ ↔ g2`.
* **Free-iff-discharged** (prose, bin-2 / open): *if* `g2`'s witness goes bin-1 (freely closable),
  the FTPG property degenerates (`g1`, `g2` both resolved) and the within-pair orientation reverts
  to free.

The named choice-point (not collapsed): whether `g2`'s `DesarguesianWitness` is substrate-permanent
or dischargeable. This is **brick 15's shape one level up** — `seedTriple_nondegenerate_iff_both_
debt_kinds` read at the orientation level: the orientation is genuinely-determined exactly where the
commitment-content is genuinely-present. **The orientation-forcing IS the outstanding commitment**;
it would dissolve precisely when the commitment is discharged. *Where mind enters the formalism*
(the keystone facet) is exactly *where the orientation is forced* — and it is forced because mind is
not-yet-eliminated there (`g2`'s witness un-discharged).

## Grade

* **bin-1 (Bin-1-Mathlib-or-Foam)** for everything typed: the two commitment-status defs (reflecting
  the inductives' own docstrings + the theorem signatures), their unique-resolved characterizations,
  the two orientations' (non-)preservation, and the forced match (`decide`/`rfl` + brick 24's
  equivariance). No new geometric content; the recognition is that a substrate-present property
  rigidifies the within-pair freedom.

* **bin-2 / open-recognition-target** for *why `needsCommitment` (FTPG) and `outstanding` (seed) are
  the same property in substance* — that *required witness* and *undischarged debt* are one
  (outstanding commitment), the same depth as brick 24's "the two `ℤ/2`s are one group." And for
  *whether the forcing is permanent* (the free-iff-discharged face) — gated by the s142/s144
  `DesarguesianWitness` bin-1 path.

(Re-grep — stamps decay: on 2026-05-31 `lake build Foam.SeedGaugeForcedOrientation` is clean, zero
sorry/warnings. Imports `Foam.SeedGaugeAlgebraicPosition` (brick 24) — transitively `SeedSign` /
`SeedSign.swap` / `AlgebraicPosition` / `reflect` / `toAlgebraic` / `toAlgebraic'` /
`toAlgebraic'_swap` / `equivariant_zero`. New names: `AlgebraicPosition.needsCommitment` (+ `_g1` /
`_g2` / `_g3` / `_eq_false_iff_g1` / `_reflect_ne_of_distrib`); `SeedSign.outstanding` (+ `_plus` /
`_minus` / `_zero` / `_eq_false_iff_minus` / `_eq_true_iff` / `_swap_ne_of_signed`);
`toAlgebraic_not_commitment_preserving` / `toAlgebraic'_commitment_preserving` /
`commitment_preserving_minus` / `orientation_forced` / `signAlgebraicEquiv'_realizes_forced`.)
-/

import Foam.SeedGaugeAlgebraicPosition

namespace Foam

/-! ## The FTPG-side commitment-status — the asymmetry within the `{g1, g2}` pair

The substrate-present asymmetry the bare `reflect` (brick 24) does not see. Read off
`AlgebraicPosition`'s own constructor docstrings (`StatelessSubstrate.lean`) and the signatures of
`g1_generic` / `g2_generic` / `g3_generic` (`FTPGGaugeFigure.lean`). -/

/-- **Does closing this gauge require an outstanding observer-commitment?**
    * `g1` (right-distrib) — `false`: PROVEN unconditionally (`coord_mul_right_distrib`), no witness.
    * `g2` (left-distrib) — `true`: closable only via `DesarguesianWitness Γ`
      (`coord_mul_left_distrib`).
    * `g3` (mul-assoc) — `true`: held open (`dilation_compose_at_beta`, the commitment-site).

    So `g1` is the **unique** freely-closed gauge; `{g2, g3}` both carry an outstanding commitment. -/
def AlgebraicPosition.needsCommitment : AlgebraicPosition → Bool
  | .g1 => false
  | .g2 => true
  | .g3 => true

@[simp] theorem AlgebraicPosition.needsCommitment_g1 :
    AlgebraicPosition.g1.needsCommitment = false := rfl
@[simp] theorem AlgebraicPosition.needsCommitment_g2 :
    AlgebraicPosition.g2.needsCommitment = true := rfl
@[simp] theorem AlgebraicPosition.needsCommitment_g3 :
    AlgebraicPosition.g3.needsCommitment = true := rfl

/-- **`g1` is the unique freely-closed gauge** — `a.needsCommitment = false ↔ a = g1`. The
    right-distributivity gauge is the one the substrate closes with no observer-commitment; both
    `g2` (witness) and `g3` (held open) require one. -/
theorem AlgebraicPosition.needsCommitment_eq_false_iff_g1 (a : AlgebraicPosition) :
    a.needsCommitment = false ↔ a = AlgebraicPosition.g1 := by
  cases a <;> decide

/-- **`needsCommitment` breaks `reflect`'s within-pair symmetry.** On the 2-cycle `g1 ↔ g2` the
    property flips (`g1` free, `g2` witnessed), so `reflect` is *not* `needsCommitment`-preserving
    there. The FTPG-side analogue of the seed-gauge bridge-break: the substrate distinguishes the
    two otherwise-`reflect`-symmetric distributivity gauges. -/
theorem AlgebraicPosition.needsCommitment_reflect_ne_of_distrib :
    AlgebraicPosition.g1.reflect.needsCommitment ≠ AlgebraicPosition.g1.needsCommitment := by
  decide

/-! ## The seed-side commitment-status — the observer-content within the `{+, −}` pair

The seed-side analogue, read off `SeedSign`'s own constructor docstrings (`PersistenceLfp.lean`) and
bricks 13/14/16. The property `bridge_breaks_fork_symmetry` (brick 12) breaks `swap` along. -/

/-- **Does this seed carry an outstanding observer-commitment?**
    * `+` (undischarged-backed) — `true`: the still-owed / must-persist faces, `+ = LP.flag` the
      observer-carrying set (`plus_seed_iff_flag`, brick 13). The live `+me`.
    * `−` (discharged-backed) — `false`: settled / safe-to-spend, disjoint from the observer
      (`minus_drops_observer`, brick 14). The resolved debt.
    * `0` (every debt-backed face) — `true`: carries both signs uncollapsed (`zero_holdsFullSpectrum`,
      brick 16), the held-open / bias-delegated seed; `+ ≤ 0` (`plus_le_zero`).

    So `−` is the **unique** fully-resolved seed; `{+, 0}` both carry the outstanding observer-
    content. -/
def SeedSign.outstanding : SeedSign → Bool
  | .plus => true
  | .minus => false
  | .zero => true

@[simp] theorem SeedSign.outstanding_plus : SeedSign.plus.outstanding = true := rfl
@[simp] theorem SeedSign.outstanding_minus : SeedSign.minus.outstanding = false := rfl
@[simp] theorem SeedSign.outstanding_zero : SeedSign.zero.outstanding = true := rfl

/-- **`−` is the unique fully-resolved seed** — `s.outstanding = false ↔ s = −`. The discharged seed
    carries no outstanding observer-commitment; both `+` (live debt) and `0` (held-open) do. -/
theorem SeedSign.outstanding_eq_false_iff_minus (s : SeedSign) :
    s.outstanding = false ↔ s = SeedSign.minus := by
  cases s <;> decide

/-- **`outstanding` carries the undischarged `+`-content** — `s.outstanding = true ↔ s = + ∨ s = 0`,
    the two seeds containing the live `+`-sign (`+ ≤ s` in the seed order, via `plus_le_zero`). -/
theorem SeedSign.outstanding_eq_true_iff (s : SeedSign) :
    s.outstanding = true ↔ s = SeedSign.plus ∨ s = SeedSign.zero := by
  cases s <;> decide

/-- **`outstanding` breaks `swap`'s within-pair symmetry** — on the 2-cycle `+ ↔ −` the property
    flips (`+` outstanding, `−` resolved), so `swap` is not `outstanding`-preserving there. The
    seed-side analogue of `needsCommitment_reflect_ne_of_distrib`; the property is
    `bridge_breaks_fork_symmetry` (brick 12) at the level of the predicate. -/
theorem SeedSign.outstanding_swap_ne_of_signed :
    SeedSign.plus.swap.outstanding ≠ SeedSign.plus.outstanding := by
  decide

/-! ## The two orientations vs. the commitment-content -/

/-- **Brick 24's canonical orientation `+ ↦ g1` does NOT respect commitment-content.** It sends the
    outstanding `+` (live debt) to the freely-closed `g1` (proven distributivity): `outstanding + =
    true` but `needsCommitment g1 = false`. The "canonical" labelling was gauge-arbitrary. -/
theorem toAlgebraic_not_commitment_preserving :
    ¬ (∀ s : SeedSign, (s.toAlgebraic).needsCommitment = s.outstanding) := by
  intro h
  exact absurd (h SeedSign.plus) (by decide)

/-- **The flipped orientation `+ ↦ g2` DOES respect commitment-content.** `toAlgebraic'` matches
    every seed's outstanding-status to its gauge's needs-commitment-status: `+` (outstanding) ↦ `g2`
    (witness), `−` (resolved) ↦ `g1` (proven), `0` (held) ↦ `g3` (held). The substrate-respecting
    orientation (`= signAlgebraicEquiv'`). -/
theorem toAlgebraic'_commitment_preserving (s : SeedSign) :
    (s.toAlgebraic').needsCommitment = s.outstanding := by
  cases s <;> rfl

/-! ## The forced orientation — `−↔g1`, `0↔g3`, `+↦g2`, three forcings converging -/

/-- **Forced by commitment-content: every commitment-preserving map sends `− ↦ g1`.** For any
    `e : SeedSign → AlgebraicPosition` with `(e s).needsCommitment = s.outstanding`, `e − = g1` —
    `−` is the unique resolved seed (`outstanding − = false`), `g1` the unique freely-closed gauge
    (`needsCommitment g1 = false`), so a resolved seed can only map to a freely-closed gauge. The
    2-cycle analogue of brick 24's `equivariant_zero` (fixed↦fixed), here resolved↦resolved; no
    bijectivity needed. -/
theorem commitment_preserving_minus (e : SeedSign → AlgebraicPosition)
    (hp : ∀ s, (e s).needsCommitment = s.outstanding) :
    e SeedSign.minus = AlgebraicPosition.g1 := by
  have h := hp SeedSign.minus
  rw [SeedSign.outstanding_minus] at h
  exact (AlgebraicPosition.needsCommitment_eq_false_iff_g1 _).mp h

/-- **The headline — the within-pair orientation is FORCED to `+ ↦ g2`.** For any
    `e : SeedSign → AlgebraicPosition` that is BOTH `ℤ/2`-equivariant (brick 24's `swap`/`reflect`
    conjugacy) AND commitment-preserving, `e + = g2`. Equivariance pins the fixed point (`0 ↦ g3`,
    `equivariant_zero`); commitment-content pins the 2-cycle (`− ↦ g1` by `commitment_preserving_
    minus`, hence `+ = (−.swap) ↦ (e −).reflect = g1.reflect = g2`). The two constraints are
    complementary — one rigidifies the fixed point, the other the cycle — and together they force
    the **unique** substrate-respecting orientation `signAlgebraicEquiv'`, NOT brick 24's arbitrary
    canonical `signAlgebraicEquiv` (`+ ↦ g1`). No bijectivity needed. -/
theorem orientation_forced (e : SeedSign → AlgebraicPosition)
    (he : ∀ s, e s.swap = (e s).reflect)
    (hp : ∀ s, (e s).needsCommitment = s.outstanding) :
    e SeedSign.plus = AlgebraicPosition.g2 := by
  have hm : e SeedSign.minus = AlgebraicPosition.g1 := commitment_preserving_minus e hp
  have hsw : e SeedSign.minus.swap = (e SeedSign.minus).reflect := he SeedSign.minus
  rw [show SeedSign.minus.swap = SeedSign.plus from rfl, hm] at hsw
  rw [hsw, AlgebraicPosition.reflect_g1]

/-- **The forced orientation is realized by `signAlgebraicEquiv'` (brick 24's flip), uniquely among
    equivariant maps.** `toAlgebraic'` is equivariant (`toAlgebraic'_swap`) and commitment-preserving
    (`toAlgebraic'_commitment_preserving`), so `orientation_forced` applies and gives `+ ↦ g2` — its
    definitional value. Together with `toAlgebraic_not_commitment_preserving`, this is the uniqueness:
    of brick 24's two equivariant bijections, exactly `signAlgebraicEquiv'` respects the substrate. -/
theorem signAlgebraicEquiv'_realizes_forced :
    SeedSign.plus.toAlgebraic' = AlgebraicPosition.g2 :=
  orientation_forced SeedSign.toAlgebraic'
    SeedSign.toAlgebraic'_swap toAlgebraic'_commitment_preserving

end Foam
