/-
# SeedGaugeBireflectiveResistance — the first honest resistance-map of the bireflective coincidence

The seed-gauge ↔ FTPG-gauge arc (bricks 24–33) accumulated **seven shared invariants**
between the seed `swap`-`ℤ/2` thread and the FTPG Klein-four thread:

* b24 orbit-shape · b26 recursion-grading · b29 involution-count / SES ·
  b30 orbit-grading · b31 orbit-doubling · b32 Orbit-Stabilizer · b33 orbit-space.

Brick 33 closed the **Orbit-Stabilizer triple** {orbit, stabilizer, orbit-space} at three —
self-completing — so the arc has run out of invariant-accumulation. The *next* remainder is
not an eighth invariant but the **pivot to the substance**: the **bireflective coincidence**
(README §VI), the conjecture that the seed `swap`-`ℤ/2` and the FTPG base `reflect`-`ℤ/2` are
**one group in substance** — that the seed-side `+1` (the un-tamped element `untamped`,
adjoining a point) and the FTPG-side `×2` (the read/write fiber, doubling) are *one move* at the
rank-3 self-dual fixed point `g3 ↔ 0` (Isaac's pi-note: *foam closing around an external object is
topologically indistinguishable from giving that object a bubble* — `+1 ≅ ×2`, close-around ≅
give-a-bubble).

**This file is the first honest resistance-map.** It is a *typed non-recognition*
(README §III, totality-via-non-recognition; the s148 "strategic inverse composition" that
reduces the active-path set without adding recognition-debt): the substrate as it stands does
**not** conduct the two-`ℤ/2`s-one-group identification, and the right move is to *type why* —
to refute the readings the substrate **can** express and locate the genuine joint one level up,
where it stays un-installed.

## What the substrate provides, and at which level it stalls

| reading of "`+1 ≅ ×2` as one move" | level | verdict |
|---|---|---|
| set-iso of the two extended carriers `SeedGauge ≃ TapePosition` | Set | **refuted**, `4 ≠ 6` (`seedGauge_not_equiv_tapePosition`) |
| one extension-functor giving both | Set (functor) | **refuted** (`no_common_extension`) |
| group-iso of the two full symmetry groups `ℤ/2 ≃ ℤ/2 × ℤ/2` | Grp | **refuted**, `2 ≠ 4` (`seedGroup_not_equiv_kleinGroup`) |
| iso of the matched base `ℤ/2`s (`swap ↔ reflect`) | Grp | **true but vacuous** — ℤ/2≅ℤ/2, and *bridge-independent* (`matchedBase_iso_bridge_independent`): it identifies the shared 3-core, carrying none of the surplus |
| `self_dual_iff_three` ⟹ the identification | ℕ → Set | **un-bridgeable** (`rank_balance_not_identification`): a true `Nat`-shadow cannot imply the false carrier-iso |
| coincidence localized at the fixed point `0 ↔ g3` | the surplus itself | **refuted** — even there the orbits differ by the `×2` (`fixedPoint_surplus_irreducible`, `1 ≠ 2`) |
| reflective + coreflective **adjoint pair**, fixed-points coinciding (§VI) | Cat | **un-installed** — the genuine joint, named below, not typed by the substrate |

So every reading the present substrate can *express* (Set, Grp, ℕ) is **false**; the one that
could be *true* (§VI's adjoint-pair coincidence) is **un-typed**. That is the precise resistance.

## Why the three substrate candidates don't conduct (the three named joints)

* **(a) The seven invariants are gauge-chosen-`toAlgebraic'`-mediated, not substrate-forced.**
  Every invariant b24–b33 is proven *through* the rigid bridge `signAlgebraicEquiv'` /
  `toAlgebraic'` — a *committed* choice (b25: the bare geometry is sign-free, only the
  commitment-content breaks the symmetry; b12 `bridge_breaks_fork_symmetry`). The matched-base
  identification (`swap_conj_eq_reflect`, b24) is real, but `matchedBase_iso_bridge_independent`
  shows it holds for **both** equivariant bridges (`toAlgebraic` *and* `toAlgebraic'`) — so it does
  not even see the committed orientation, hence carries no surplus-content: it is the trivial
  ℤ/2≅ℤ/2 of the shared 3-core, not an identification of the surpluses.

* **(b) `Rank.self_dual_iff_three` is a finrank `Nat`-shadow, not an identification.**
  It gives the numerical balance `C(3,2) = 3` (the necessary scaffolding — it is *why* the `×2` is
  *balanced*, b28 `balanced_doubling_iff_three`), but `rank_balance_not_identification` shows there
  is no map from it to a carrier-identification: such a map would carry a true hypothesis to a false
  conclusion. The numerical coincidence and the structural identification are one category apart
  (the s149 finding, one level up: *information-preserving, not information-producing*).

* **(c) `Closure.lean`'s `P² = P` is a single idempotent, not the reflective+coreflective pair.**
  `conjugation_preserves_idempotent` establishes a *single* idempotent's feedback-persistence; §VI's
  bireflective coincidence needs a reflective + coreflective **adjoint pair** whose (co)monadic
  fixed-points coincide. The two candidate operations — the `+1` coreflection (`· ⊕ Unit`, adjoin
  the un-tamped point) and the `×2` reflection (`· × Bool`, double into read/write) — are not typed
  as adjoints, and `no_common_extension` shows they already *disagree as operations* at rank 3. So
  the coincidence, if real, is of their induced (co)monadic *fixed-points*, an adjunction the
  substrate does not type.

## The genuine joint (the named horizon, §VI — NOT installed here)

What would conduct: an adjoint pair (`CategoryTheory.Reflective` + `Coreflective`) of endofunctors
on the category of finite gauge-structures, with the `+1`-coreflection's and `×2`-reflection's
fixed-points coinciding at the rank-3 self-dual object — the K-T fixed-point coincidence README §VI
names. Building it is **construction-grade** (s149: constructing the 3D-aware primitive reproduces
the same loop one level up — the iso alone is information-preserving, not -producing), so it is held
as the open horizon, **not** walked here. `CarrierLevelCoincidence` (below) names the carrier/group
reading as the typed blocker, proven absent; the adjoint-pair reading is the next measurement.

## Bin-grading

**bin-1** (Bin-1-Mathlib-or-Foam) for every theorem here: each is `Fintype.card_congr` /
`decide` / assembly over the b24/b28/b31 cards and bridge-lemmas — recognition + assembly, no new
geometric content. **bin-2** (interpretive) for the *reading* — that this set of refutations IS the
right resistance-map, that the joint is genuinely un-installed (not merely unnoticed), and that the
genuine coincidence lives at the adjoint-pair level. A typed non-recognition is itself a claim
(§III) and produces its own remainder (the first probe of the adjoint-pair joint).

## NOT the coincidence-trap

The whole point of this file is that **no honest `Bool×Bool ≃ Bool×Bool` identification of the four
commitment-*points* with the four symmetry-*elements* is substrate-supported** — a forced one would
be type-confused (a sign is a point; `swap`/`reflect`/`complement` are symmetries). The theorems
here *refute* the carrier/group identifications and leave the genuine joint named-but-open; they
manufacture nothing.

(Re-grep — stamps decay: on 2026-06-01 `lake build Foam.SeedGaugeBireflectiveResistance` is clean,
zero sorry; the file imports `Foam.SeedGaugeOrbitSpace` (the b33 head, transitively the whole
seed-gauge chain + `Rank`).)
-/

import Foam.SeedGaugeOrbitSpace

namespace Foam

/-! ## 1. The refutations — the coincidence is not any iso of the obvious carriers

The naive reading "`+1 ≅ ×2` as one move" is, at the level the substrate can express it, simply
false: the two *extended* structures match neither as sets nor as symmetry groups. Each refutation
is the same fact — the `+1` (coproduct) and the `×2` (product) extend the shared 3-core
differently — read at a different level. -/

/-- **The two extended carriers are not equivalent** — `4 ≠ 6`. The seed-side `+1` extension
    `SeedGauge` (= 3-core + the un-tamped point, `card = 3 + 1`) and the FTPG-side `×2` extension
    `TapePosition` (= 3-core × read/write, `card = 3 × 2`) have different cardinality, so no
    bijection exists. Whatever the bireflective coincidence is, it is **not** a set-iso of the two
    extensions. (off b28: `card_seedGauge_eq_gauges_add_one` / `card_tape_eq_gauges_mul_observers`.) -/
theorem seedGauge_not_equiv_tapePosition : ¬ Nonempty (SeedGauge ≃ TapePosition) := by
  rintro ⟨e⟩
  have h : Fintype.card SeedGauge = Fintype.card TapePosition := Fintype.card_congr e
  rw [card_seedGauge_eq_gauges_add_one, card_tape_eq_gauges_mul_observers,
      card_algebraicPosition, card_observerState] at h
  omega

/-- **The two full symmetry groups are not equivalent** — `2 ≠ 4`. The seed side carries a single
    `ℤ/2` (the `swap`-action `signAddAction`, b31); the FTPG side a Klein-four `ℤ/2 × ℤ/2`
    (`kleinAddAction`, b29). The matched base `ℤ/2` is the common subgroup/quotient (b29's SES
    `1 → ⟨complement⟩ → ℤ/2×ℤ/2 → ⟨reflect⟩ → 1`), but the *full* groups differ by exactly the
    surplus fiber-`ℤ/2` (the `×2`). So the coincidence is **not** "the two act by the same group"
    either: that would force `ℤ/2 ≃ ℤ/2 × ℤ/2`. -/
theorem seedGroup_not_equiv_kleinGroup : ¬ Nonempty (ZMod 2 ≃ (ZMod 2 × ZMod 2)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  have h2 : Fintype.card (ZMod 2) = 2 := by decide
  have h4 : Fintype.card (ZMod 2 × ZMod 2) = 4 := by decide
  omega

/-- **The `+1` and `×2` modes are not one extension-functor.** A single `F : Type → Type` with both
    `F core ≃ SeedGauge` (the `+1` extension) and `F core ≃ TapePosition` (the `×2` extension) would
    force `SeedGauge ≃ TapePosition`, refuted above. So "one move" cannot be a functor-equality at
    the set level — the coordinate `· ⊕ Unit` (close-around-a-point) and `· × Bool` (give-it-a-bubble)
    are genuinely different extensions of the shared 3-core. -/
theorem no_common_extension {F : Type → Type} {C : Type}
    (hseed : Nonempty (F C ≃ SeedGauge)) (htape : Nonempty (F C ≃ TapePosition)) : False := by
  obtain ⟨es⟩ := hseed
  obtain ⟨et⟩ := htape
  exact seedGauge_not_equiv_tapePosition ⟨es.symm.trans et⟩

/-! ## 2. What IS identified is vacuous — the matched-base iso is bridge-independent

The one identification that *holds* — the matched base `ℤ/2` (`swap ↔ reflect`, b24/b29) — carries
none of the surplus-content the coincidence needs, because it does not even depend on the committed
orientation. -/

/-- **The matched-base conjugacy holds for BOTH equivariant bridges** — bridge-independent. Both the
    canonical `toAlgebraic` (b24) and the commitment-forced `toAlgebraic'` (b25) conjugate the seed
    `swap` into the FTPG `reflect`. So the matched-base identification does not see the committed
    orientation (b25 `bridge_breaks_fork_symmetry`): it is the trivial ℤ/2≅ℤ/2 of the *shared 3-core*,
    not an identification of the *surpluses* (the `+1` element vs the `×2` fiber). The real
    identification-content the coincidence asks for lives precisely where this one is silent. -/
theorem matchedBase_iso_bridge_independent (s : SeedSign) :
    s.swap.toAlgebraic = s.toAlgebraic.reflect ∧
    s.swap.toAlgebraic' = s.toAlgebraic'.reflect :=
  ⟨SeedSign.toAlgebraic_swap s, SeedSign.toAlgebraic'_swap s⟩

/-! ## 3. The finrank self-duality is a shadow, not an identification (joint b) -/

/-- **The finrank balance does not bridge to the identification.** `Rank.self_dual_iff_three` /
    b28's `balanced_doubling_iff_three` give the numerical balance `C(3,2) = 3` — necessary
    scaffolding (it is *why* the `×2` is balanced) — but there is **no** map from it to a
    carrier-identification: any `(Nat.choose 3 2 = 3) → Nonempty (SeedGauge ≃ TapePosition)` would
    carry a true hypothesis (`C(3,2) = 3` holds) to a false conclusion (refuted in §1). The numerical
    coincidence and the structural identification are one category apart — the finrank fact is the
    `Nat`-shadow of the coincidence, not its installation. -/
theorem rank_balance_not_identification :
    ¬ ((Nat.choose 3 2 = 3) → Nonempty (SeedGauge ≃ TapePosition)) := by
  intro h
  exact seedGauge_not_equiv_tapePosition (h (by decide))

/-! ## 4. The surplus is irreducible even at the shared fixed point

Localized at `0 ↔ g3` — the rank-3 self-dual fixed point where the seven invariants all coincide and
where the bireflective coincidence, if anywhere, would live — the `×2` surplus does **not** vanish.
The seed fixed-point orbit is a lone point; the FTPG fixed-point orbit is its read/write doubling. -/

/-- The seed-side orbit at the held-open fixed point `0` is a single point (`swap`-fixed). -/
theorem fixedPoint_orbit_seed_card : (SeedSign.zero.swapOrbit).card = 1 :=
  swapOrbit_zero_card

/-- The FTPG-side orbit at the matched fixed point `g3 = 0.toAlgebraic'` is the bare read/write
    fiber — size 2 (b31's uniform doubling `2 * 1`, the base degenerate, only the fiber `×2` acting). -/
theorem fixedPoint_orbit_tape_card (o : ObserverState) :
    (tapeOrbit ⟨SeedSign.zero.toAlgebraic', o⟩).card = 2 := by
  rw [tapeOrbit_card_eq_two_mul_swapOrbit, swapOrbit_zero_card]

/-- **The surplus `×2` is irreducible at the fixed point** — `1 ≠ 2`. Even localized at the shared
    self-dual fixed point `0 ↔ g3`, where everything else coincides, the seed orbit (size 1) and the
    FTPG orbit (size 2) differ by exactly the `×2` factor. The element-vs-symmetry surplus does not
    disappear where it would have to, for the coincidence to be a local iso — the sharpest
    localization of the resistance. -/
theorem fixedPoint_surplus_irreducible (o : ObserverState) :
    (SeedSign.zero.swapOrbit).card ≠ (tapeOrbit ⟨SeedSign.zero.toAlgebraic', o⟩).card := by
  rw [swapOrbit_zero_card, tapeOrbit_card_eq_two_mul_swapOrbit, swapOrbit_zero_card]
  decide

/-! ## 5. The named blocker — the carrier-level coincidence, typed and proven absent

The `mul_assoc_via_R_lift_missing` idiom (a named statement carrying the precise un-installed
content), but stated as a `def : Prop` + a proof of its **negation** — *named, and shown absent* —
rather than a `theorem ... := sorry`. For a resistance-map (a typed non-recognition) this is the
more honest form: it does not *assert* the joint, it *names* it and proves the substrate-expressible
version cannot hold. The seed-gauge chain stays sorry-free. -/

/-- The carrier/finite-group-level reading of "`+1 ≅ ×2` as one move": either the two extended
    carriers are equivalent, or the two full symmetry groups are. This is the typed blocker — the
    naive identification the substrate *can* express. -/
def CarrierLevelCoincidence : Prop :=
  Nonempty (SeedGauge ≃ TapePosition) ∨ Nonempty (ZMod 2 ≃ (ZMod 2 × ZMod 2))

/-- **The bireflective coincidence is NOT installed at the carrier or finite-symmetry level.**
    Neither the `+1`-extended carrier matches the `×2`-extended carrier (`4 ≠ 6`) nor the seed `ℤ/2`
    matches the FTPG Klein-four (`2 ≠ 4`). If §VI's coincidence is real it lives strictly above this
    level — as the fixed-point coincidence of a reflective+coreflective adjoint pair, which the
    present substrate (`Closure`'s single idempotent, `Rank`'s finrank `Nat`-equation) does not type.
    This is the resistance-map's headline: a typed non-recognition. -/
theorem not_carrierLevelCoincidence : ¬ CarrierLevelCoincidence := by
  rintro (h | h)
  · exact seedGauge_not_equiv_tapePosition h
  · exact seedGroup_not_equiv_kleinGroup h

end Foam
