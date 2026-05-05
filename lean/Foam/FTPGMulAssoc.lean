/-
# Multiplication associativity (Part VIII) — DESIGN STUB

`coord_mul_assoc`: (a·b)·c = a·(b·c)

## Status (session 133)

Architecture only. Zero proof content. This file establishes
the named sub-lemma + headline signature with `sorry` bodies,
so the next session has a compile-checked starting point rather
than a blank page.

## Why this file exists

Session 132 found an algebraic shortcut for `coord_mul_left_inv`:
the standard Mac Lane semigroup argument
(assoc + right-ID + right-inverse ⇒ left-inverse, ~20 lines)
bypasses the geometrically-circular `axis_to_sigma_a_le` entirely.
The shortcut depends on `coord_mul_assoc`, which became the
critical-path geometric lemma. This file is that critical path.

## Proof architecture (proposed, by analogy with `coord_add_assoc`)

The additive precedent (`coord_add_assoc` in FTPGAssocCapstone.lean,
~1450 lines) routes through *translations as a group under
composition*:

  1. `coord_add_eq_translation` (FTPGAssoc.lean) — coord_add a b
     equals a parallelogram-completion expression in the translation
     primitive. The "operation = composition" bridge.
  2. `key_identity` (FTPGAssoc.lean) — τ_a(C_b) = C_{a+b}, where
     C_x = pc(O, x, C, m) is x's β-image.
  3. `translation_determined_by_param` (FTPGAssocCapstone.lean:38) —
     pc(C, C₁, P, m) = pc(C, C₂, P, m) ⇒ C₁ = C₂ (via
     perspectivity_injective from q to P⊔U through e_P).
  4. `coord_add_assoc` (FTPGAssocCapstone.lean:186) — assembles via
     four `key_identity` applications + cross_parallelism + the
     determined-by-param uniqueness.

The multiplicative analogue has most pieces ALREADY PROVEN
in FTPGDilation.lean and FTPGMulKeyIdentity.lean:

  * `dilation_ext` (FTPGDilation:25) — the universal σ_c primitive
  * `dilation_preserves_direction` (FTPGDilation:419, ~500 lines,
    PROVEN) — analog of `cross_parallelism`. Three cases: c=I, P, Q
    collinear with I, generic-via-Desargues-center-O.
  * `dilation_ext_identity` (FTPGDilation:937, PROVEN) — σ_I = id
  * `dilation_ext_fixes_m` (FTPGDilation:982, PROVEN) — σ_a fixes
    m pointwise (the multiplicative analog of "translation fixes
    the line at infinity")
  * `dilation_ext_C` (FTPGDilation:406, PROVEN) — σ_c(C) =
    (O⊔C)⊓(c⊔E_I), agrees with the first perspectivity in
    coord_mul's definition (so coord_mul a b is essentially
    "join σ_b(C) with d_a, project to l")
  * `beta_atom`, `beta_not_l`, `beta_plane` (FTPGMulKeyIdentity)
    — β(a) = (U⊔C)⊓(a⊔E) is an atom off l in π
  * `dilation_mul_key_identity` (FTPGMulKeyIdentity:141, PROVEN) —
    σ_c(β(a)) = (σ⊔U)⊓(a·c ⊔ E), the multiplicative key identity

What this file needs to add:

  * `dilation_determined_by_param` (NEW, sorry'd below) — analog of
    `translation_determined_by_param`. If σ_a₁(P) = σ_a₂(P) for
    some witness P off l (and possibly off m, off O⊔C), then a₁ = a₂.
    Likely route: dilation_ext(a, P) is a perspectivity from O⊔C
    onto O⊔P through some center; perspectivity injectivity.

  * `coord_mul_assoc` (NEW, sorry'd below, headline) — assembles
    via four `dilation_mul_key_identity` applications + a
    composition-of-dilations argument + dilation_determined_by_param.

## The witness question (s132 device-shape conjecture)

Session 132's "device-shaped" pattern-match suggested there might
be a peer to `DesarguesianWitness Γ` (left distrib's residue from
session 114). The first candidate (`axis_to_sigma_a_le`'s
self-circular forward-Desargues design) was sidestepped by the
algebraic shortcut.

**Prediction (session 133):** `coord_mul_assoc` does NOT need a
fresh `DesarguesianWitness`-style commitment. Reasoning:

  * The Desargues investment for the multiplicative branch was
    already paid: `dilation_preserves_direction` (forward Desargues
    with center O, three cases) and `dilation_mul_key_identity`
    (forward Desargues with center C). Both PROVEN, no witness.
  * The capstone assembly should be modular-law juggling +
    four key-identity applications + dilation uniqueness — no
    fresh Desargues call. This matches the additive precedent:
    `coord_add_assoc`'s body uses `cross_parallelism` and
    `key_identity` extensively but makes no direct Desargues call.
  * Right multiplication x↦x·a IS a collineation (it's the dilation
    σ_a — see `dilation_preserves_direction`), unlike left
    multiplication which broke the symmetry that left distrib relied
    on. So the structural reason left-distrib needed an observer
    commitment doesn't apply here.

**If this prediction is wrong** — if assembling four key identities
into associativity hits a converse-Desargues residue — that IS the
third point Isaac flagged in s132, and the device-shape becomes
designable as a typed pluggable interface alongside
`DesarguesianWitness`. In that case: name the residue with its own
typed structure (analogous to `DesarguesianWitness`'s
`concurrence` field), thread it through `coord_mul_assoc` as an
explicit parameter, and proceed. The two-witness pattern would then
be available as evidence for or against the device-shape conjecture
when the third operation (probably mul-comm or some derived law)
gets formalized.

## Open frontier from here

  * Land `coord_mul_assoc` (this file's two sorries).
  * Add `coord_mul_left_inv` to FTPGInverse.lean as ~20 lines of
    Mac Lane chain (b·a = (b·a)·I = (b·a)·(b·c) = b·((a·b)·c) =
    b·(I·c) = b·c = I).
  * DivisionRing instance + vector space construction + lattice
    iso L ≃o Sub(D, V) — replaces `axiom ftpg` in Bridge.lean.

## Best-guess signature note

The signature for `dilation_determined_by_param` below is a
starting point. In particular, the precise hypotheses on the
witness P (off l? off m? off O⊔C? plane-bounded?) may need
adjustment as the proof structure clarifies. The additive
precedent requires P off q and off m; the multiplicative analog
likely requires P off l and off m (and possibly off O⊔C, since
O⊔C is the multiplicative bridge line).
-/

import Foam.FTPGMulKeyIdentity

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-- **A dilation is determined by its parameter.**

    If `σ_a₁(P) = σ_a₂(P)` for some witness atom P that is
    off l, off m, off O⊔C, and not equal to I, then `a₁ = a₂`.

    Multiplicative analog of `translation_determined_by_param`
    (FTPGAssocCapstone.lean:38). Likely route: `dilation_ext Γ a P`
    factors as a perspectivity from O⊔C onto O⊔P through some
    center (probably the m-direction of I⊔P); perspectivity
    is injective; equal images force equal parameters.

    Best-guess signature — refine during the proof attempt. -/
theorem dilation_determined_by_param (Γ : CoordSystem L)
    {a₁ a₂ P : L} (ha₁ : IsAtom a₁) (ha₂ : IsAtom a₂)
    (ha₁_on : a₁ ≤ Γ.O ⊔ Γ.U) (ha₂_on : a₂ ≤ Γ.O ⊔ Γ.U)
    (ha₁_ne_O : a₁ ≠ Γ.O) (ha₂_ne_O : a₂ ≠ Γ.O)
    (ha₁_ne_U : a₁ ≠ Γ.U) (ha₂_ne_U : a₂ ≠ Γ.U)
    (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_ne_I : P ≠ Γ.I)
    (h_agree : dilation_ext Γ a₁ P = dilation_ext Γ a₂ P) :
    a₁ = a₂ := by
  sorry

/-- **Associativity of coordinate multiplication.**

    `(a·b)·c = a·(b·c)`

    Proof strategy (proposed, by analogy with `coord_add_assoc`):

    1. Apply `dilation_mul_key_identity` four times — at (a, b),
       (b, c), (s, c) where `s = a·b`, and (a, t) where `t = b·c`.
       This gives β-image equations for both sides:
         σ_c(β(s)) = (σ_s⊔U) ⊓ ((s·c) ⊔ E) = (σ_s⊔U) ⊓ ((a·b)·c ⊔ E)
         σ_a(β(t)) = (σ_a⊔U) ⊓ ((a·t) ⊔ E) = (σ_a⊔U) ⊓ (a·(b·c) ⊔ E)

    2. Show that σ_c ∘ σ_b applied to β(a) (or to some chosen
       witness point) agrees with σ_(b·c) applied to the same
       witness — i.e., dilation composition. The two-lines
       argument and `dilation_preserves_direction` should suffice
       (parallel to how `coord_add_assoc` uses cross_parallelism).

    3. Apply `dilation_determined_by_param` (or perspectivity
       injectivity at the appropriate stage) to conclude
       `(a·b)·c = a·(b·c)`.

    Witness parameters `R, hR, hR_not, h_irred` thread through
    just as in `coord_add_assoc` — they discharge the irreducibility
    requirement for any `desargues_*` calls upstream. -/
theorem coord_mul_assoc (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (_hab : a ≠ b) (_hbc : b ≠ c) (_hac : a ≠ c)
    -- Non-degeneracy of intermediate products.
    (_hs_ne_O : coord_mul Γ a b ≠ Γ.O) (_hs_ne_U : coord_mul Γ a b ≠ Γ.U)
    (_ht_ne_O : coord_mul Γ b c ≠ Γ.O) (_ht_ne_U : coord_mul Γ b c ≠ Γ.U)
    (_hsc : coord_mul Γ a b ≠ c) (_hat : a ≠ coord_mul Γ b c)
    (_R : L) (_hR : IsAtom _R) (_hR_not : ¬ _R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (_h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_mul Γ (coord_mul Γ a b) c = coord_mul Γ a (coord_mul Γ b c) := by
  sorry

end Foam.FTPGExplore
