/-
# Multiplication associativity (Part VIII) — DESIGN STUB

`coord_mul_assoc`: (a·b)·c = a·(b·c)

## Status (session 133)

  * `dilation_determined_by_param` — **PROVEN** (~150 lines).
    Factors `dilation_ext Γ a P` as a perspectivity from
    `l = O⊔U` to `O⊔P` through center `d_P = (I⊔P)⊓m`,
    then applies `perspectivity_injective`. Signature held
    against contact with the proof — no architectural surprises.
    Mild scope-trim: hypotheses `_ha₁_ne_O`, `_ha₂_ne_O`,
    `_ha₁_ne_U`, `_ha₂_ne_U`, `_hP_not_OC`, `_hP_ne_I` turn out
    not to be needed for the proof and are underscored;
    callers from `coord_mul_assoc` will already have them, so
    they're kept in the signature for API parity with
    `translation_determined_by_param`.
  * `coord_mul_assoc` — **OPEN** (single remaining `sorry`).
    Architecture and proposed proof strategy in the theorem's
    docstring below. The helper landing means the assembly
    has all its named pieces.

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
    (_ha₁_ne_O : a₁ ≠ Γ.O) (_ha₂_ne_O : a₂ ≠ Γ.O)
    (_ha₁_ne_U : a₁ ≠ Γ.U) (_ha₂_ne_U : a₂ ≠ Γ.U)
    (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (_hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (_hP_ne_I : P ≠ Γ.I)
    (h_agree : dilation_ext Γ a₁ P = dilation_ext Γ a₂ P) :
    a₁ = a₂ := by
  set l := Γ.O ⊔ Γ.U
  set m := Γ.U ⊔ Γ.V
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set d_P := (Γ.I ⊔ P) ⊓ m
  -- ═══ Setup ═══
  have hP_ne_O : P ≠ Γ.O := fun h => hP_not_l (h ▸ le_sup_left)
  have hP_ne_I : P ≠ Γ.I := fun h => hP_not_l (h ▸ Γ.hI_on)
  have hm_le_π : m ≤ π :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  -- ═══ d_P is an atom ═══
  have hd_P_atom : IsAtom d_P :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  -- Reusable: I⊔P covers I (atom_covBy_join)
  have hI_covBy_IP : Γ.I ⋖ Γ.I ⊔ P := atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)
  have hI_lt_l : Γ.I < l := by
    show Γ.I < Γ.O ⊔ Γ.U
    exact lt_of_le_of_ne Γ.hI_on
      (fun h => Γ.hOI ((Γ.hI.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left Γ.hO.1))
  -- Helper: any extension of I to l (via O ≤ I⊔X or U ≤ I⊔X) forces P on l. Used twice below.
  -- ═══ d_P ≠ U (else U ≤ I⊔P, then I⊔U=l ≤ I⊔P, then l = I⊔P (covering), then P ≤ l ✗) ═══
  have hd_P_ne_U : d_P ≠ Γ.U := by
    intro h
    have hU_le_IP : Γ.U ≤ Γ.I ⊔ P := h.symm.le.trans inf_le_left
    have hIU_le_IP : Γ.I ⊔ Γ.U ≤ Γ.I ⊔ P := sup_le le_sup_left hU_le_IP
    have hIU_eq_l : Γ.I ⊔ Γ.U = l := by
      show Γ.I ⊔ Γ.U = Γ.O ⊔ Γ.U
      have hU_lt : Γ.U < Γ.I ⊔ Γ.U := lt_of_le_of_ne le_sup_right
        (fun h => Γ.hUI ((Γ.hU.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left Γ.hI.1).symm)
      have hU_covBy_l : Γ.U ⋖ Γ.O ⊔ Γ.U := by
        rw [sup_comm]; exact atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm
      exact (hU_covBy_l.eq_or_eq hU_lt.le (sup_le Γ.hI_on le_sup_right)).resolve_left
        (ne_of_gt hU_lt)
    have hl_le_IP : l ≤ Γ.I ⊔ P := hIU_eq_l ▸ hIU_le_IP
    have hl_eq_IP : l = Γ.I ⊔ P :=
      (hI_covBy_IP.eq_or_eq hI_lt_l.le hl_le_IP).resolve_left (ne_of_gt hI_lt_l)
    exact hP_not_l (le_sup_right.trans hl_eq_IP.symm.le)
  -- ═══ d_P not on l: if d_P ≤ l, then d_P ≤ l ⊓ m = U, then d_P = U ✗ ═══
  have hd_P_not_l : ¬ d_P ≤ l := by
    intro h
    have hd_le_U : d_P ≤ Γ.U := by
      have h_meet : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := Γ.l_inf_m_eq_U
      exact h_meet ▸ le_inf h inf_le_right
    exact hd_P_ne_U ((Γ.hU.le_iff.mp hd_le_U).resolve_left hd_P_atom.1)
  -- ═══ d_P not on O⊔P: I⊔P ≠ O⊔P (else l ≤ I⊔P, P on l ✗); modular_intersection gives
  --     (P⊔I) ⊓ (P⊔O) = P; d_P ≤ both, so d_P ≤ P, d_P = P, P ≤ m ✗.  ═══
  have hd_P_not_OP : ¬ d_P ≤ Γ.O ⊔ P := by
    intro h
    have hO_not_IP : ¬ Γ.O ≤ Γ.I ⊔ P := by
      intro hO_le
      have hOI_le_IP : Γ.O ⊔ Γ.I ≤ Γ.I ⊔ P := sup_le hO_le le_sup_left
      have hOI_eq_l : Γ.O ⊔ Γ.I = l := by
        show Γ.O ⊔ Γ.I = Γ.O ⊔ Γ.U
        have hO_lt : Γ.O < Γ.O ⊔ Γ.I := lt_of_le_of_ne le_sup_left
          (fun h => Γ.hOI ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hI.1).symm)
        exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
          (sup_le le_sup_left Γ.hI_on)).resolve_left (ne_of_gt hO_lt)
      have hl_le_IP : l ≤ Γ.I ⊔ P := hOI_eq_l ▸ hOI_le_IP
      have hl_eq_IP : l = Γ.I ⊔ P :=
        (hI_covBy_IP.eq_or_eq hI_lt_l.le hl_le_IP).resolve_left (ne_of_gt hI_lt_l)
      exact hP_not_l (le_sup_right.trans hl_eq_IP.symm.le)
    have hPI_PO_eq_P : (P ⊔ Γ.I) ⊓ (P ⊔ Γ.O) = P :=
      modular_intersection hP Γ.hI Γ.hO hP_ne_I hP_ne_O Γ.hOI.symm
        (fun h => hO_not_IP (sup_comm P Γ.I ▸ h))
    have hd_le_meet : d_P ≤ (P ⊔ Γ.I) ⊓ (P ⊔ Γ.O) := by
      rw [show P ⊔ Γ.I = Γ.I ⊔ P from sup_comm _ _,
          show P ⊔ Γ.O = Γ.O ⊔ P from sup_comm _ _]
      exact le_inf inf_le_left h
    have hd_le_P : d_P ≤ P := hd_le_meet.trans hPI_PO_eq_P.le
    have hd_eq_P : d_P = P := (hP.le_iff.mp hd_le_P).resolve_left hd_P_atom.1
    exact hP_not_m (hd_eq_P ▸ (inf_le_right : d_P ≤ m))
  -- ═══ Coplanarity: l ⊔ d_P = (O⊔P) ⊔ d_P (both = π) ═══
  have hl_covBy_π : l ⋖ π := by
    show Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V
    have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
      (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
    have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
    rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
  have hOP_covBy_π : Γ.O ⊔ P ⋖ π := by
    have hU_not_OP : ¬ Γ.U ≤ Γ.O ⊔ P := by
      intro h
      have hOU_le_OP : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ P := sup_le le_sup_left h
      have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
      have hO_lt_l : Γ.O < l :=
        (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
      have hl_eq_OP : l = Γ.O ⊔ P :=
        (hO_covBy_OP.eq_or_eq hO_lt_l.le hOU_le_OP).resolve_left (ne_of_gt hO_lt_l)
      exact hP_not_l (le_sup_right.trans hl_eq_OP.symm.le)
    have hOPU_eq : Γ.O ⊔ P ⊔ Γ.U = π := by
      show Γ.O ⊔ P ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V
      rw [show Γ.O ⊔ P ⊔ Γ.U = (Γ.O ⊔ Γ.U) ⊔ P from by ac_rfl]
      have hl_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ P := lt_of_le_of_ne le_sup_left
        (fun h => hP_not_l (le_sup_right.trans h.symm.le))
      exact (hl_covBy_π.eq_or_eq hl_lt.le
        (sup_le hl_covBy_π.le hP_plane)).resolve_left (ne_of_gt hl_lt)
    rw [← hOPU_eq]
    exact line_covBy_plane Γ.hO hP Γ.hU (Ne.symm hP_ne_O) Γ.hOU
      (fun h => hU_not_OP (h ▸ le_sup_right)) hU_not_OP
  have hl_d_eq : l ⊔ d_P = π := by
    have hl_lt : l < l ⊔ d_P := lt_of_le_of_ne le_sup_left
      (fun h => hd_P_not_l (le_sup_right.trans h.symm.le))
    exact (hl_covBy_π.eq_or_eq hl_lt.le
      (sup_le hl_covBy_π.le ((inf_le_right : d_P ≤ m).trans hm_le_π))).resolve_left
      (ne_of_gt hl_lt)
  have hOP_d_eq : (Γ.O ⊔ P) ⊔ d_P = π := by
    have hOP_lt : Γ.O ⊔ P < (Γ.O ⊔ P) ⊔ d_P := lt_of_le_of_ne le_sup_left
      (fun h => hd_P_not_OP (le_sup_right.trans h.symm.le))
    exact (hOP_covBy_π.eq_or_eq hOP_lt.le
      (sup_le hOP_covBy_π.le ((inf_le_right : d_P ≤ m).trans hm_le_π))).resolve_left
      (ne_of_gt hOP_lt)
  have h_coplanar : Γ.O ⊔ Γ.U ⊔ d_P = (Γ.O ⊔ P) ⊔ d_P := by rw [hl_d_eq, hOP_d_eq]
  -- ═══ Translate h_agree into perspectivity image equality ═══
  have h_persp_eq : (a₁ ⊔ d_P) ⊓ (Γ.O ⊔ P) = (a₂ ⊔ d_P) ⊓ (Γ.O ⊔ P) := by
    have h1 : dilation_ext Γ a₁ P = (a₁ ⊔ d_P) ⊓ (Γ.O ⊔ P) := by
      show (Γ.O ⊔ P) ⊓ (a₁ ⊔ (Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V)) = (a₁ ⊔ d_P) ⊓ (Γ.O ⊔ P)
      exact inf_comm _ _
    have h2 : dilation_ext Γ a₂ P = (a₂ ⊔ d_P) ⊓ (Γ.O ⊔ P) := by
      show (Γ.O ⊔ P) ⊓ (a₂ ⊔ (Γ.I ⊔ P) ⊓ (Γ.U ⊔ Γ.V)) = (a₂ ⊔ d_P) ⊓ (Γ.O ⊔ P)
      exact inf_comm _ _
    rw [← h1, ← h2]; exact h_agree
  -- ═══ Conclusion: perspectivity_injective ═══
  by_contra h_ne
  have hp₁ : (⟨a₁, ha₁, ha₁_on⟩ : AtomsOn (Γ.O ⊔ Γ.U)) ≠ ⟨a₂, ha₂, ha₂_on⟩ :=
    fun h => h_ne (congrArg Subtype.val h)
  exact perspectivity_injective hd_P_atom Γ.hO Γ.hU Γ.hO hP Γ.hOU
    (Ne.symm hP_ne_O) hd_P_not_l hd_P_not_OP h_coplanar hp₁ (Subtype.ext h_persp_eq)

/-! ## Bridge identities: β-cast and recovery-via-E (s135)

### Why this section exists

The s134 docstring's proposed Desargues setup for
`dilation_compose_at_witness` (triangles `(P, σ_x(P), σ_y(σ_x(P)))` and
`(I, x, x·y)` with center O, sides on m) **fails as a triangle setup**:
T1's three vertices are all on the single line `O⊔P` (because dilations
with center O preserve lines through O). The natural-looking setup is
collinear, not a Desargues configuration.

s135 takes a different path: factor `dilation_compose_at_witness` through
the β-line `q = U⊔C` (the **bridge world** between off-l witnesses and
on-l multiplicative structure; see `framing/vocabulary.md` "bridge")
using E as the projection center fixed by all dilations.

  * **`beta_cast Γ P = q ⊓ (P⊔E)`**: project a witness P to a β-image on
    q via center E. (PROVEN — definitional + atom-on-q verification
    inside `recovery_via_E`'s prologue.)
  * **`recovery_via_E`**: `σ_c(P) = (σ_c(beta_cast Γ P) ⊔ E) ⊓ (O⊔P)`.
    (Step 1 PROVEN: P' atomicity. Steps 2-5 OPEN — see `sorry`.)
    Routes through `dilation_preserves_direction` (PROVEN). E is fixed
    by σ_c (E ≤ m, dilations fix m pointwise), so collinearity of P, P',
    E on the line P⊔E is preserved by σ_c, giving E on σ_c(P)⊔σ_c(P').
    The unique-atom argument on (σ_c(P')⊔E) ⊓ (O⊔P) recovers σ_c(P).

These let `dilation_compose_at_witness` reduce to β-image arithmetic
where `dilation_mul_key_identity` (PROVEN) applies. The system-shift
question (whether σ_y applied to a σ_x-shifted β-image needs a fresh
"shifted-key-identity" lemma) becomes localized and can be answered by
either re-bridging through E or by re-deriving the key identity at the
shifted system — both workable, both at the architecture's permitted
scale.

### s135 status (partial; clean handoff)

Step 1 lands: `beta_cast Γ P` is verified as an atom on q with the full
witness conditions (off l, off m, off O⊔C, ≠ I, ≠ O, ≠ U, ≠ C). The
modular juggling for these conditions runs ~100 lines and is a real
contribution — the next session inherits this verification rather than
rebuilding it.

Steps 2-5 remain (estimated ~250-350 lines):
  * **Step 2**: `(P⊔P')⊓m = E` via `P' ≤ P⊔E` and `(P⊔E)⊓m = E`
    (P off m, line meets m at single atom = E).
  * **Step 3**: apply `dilation_preserves_direction` at the pair (P, P')
    to lift Step 2 to `(σP⊔σP')⊓m = E`. This requires verifying P' as
    a witness for the lemma's preconditions (atom, in π, off l, off m,
    ≠ O, ≠ I; plus σP ≠ σP', which needs its own short argument from
    P ≠ P' and the directions being distinct).
  * **Step 4**: from `(σP⊔σP')⊓m = E`, derive `E ≤ σP⊔σP'`, hence the
    line `σP⊔σP'` equals `σP⊔E` (covering on σP), so `σP' ≤ σP⊔E`,
    equivalently `σP ≤ σP'⊔E`.
  * **Step 5**: `σP ≤ O⊔P` (definition); combined with Step 4,
    `σP ≤ (σP'⊔E) ⊓ (O⊔P)`. The right side is an atom (two distinct
    lines in π — distinct because E ∉ O⊔P, see hE_not_OP in the
    prologue). Atom equality concludes.
-/

/-- The β-cast of a witness P to the bridge line q = U⊔C, projected
    through center E. Maps `π`-atoms to atoms on q. -/
noncomputable def beta_cast (Γ : CoordSystem L) (P : L) : L :=
  (Γ.U ⊔ Γ.C) ⊓ (P ⊔ Γ.E)

/-- **Recovery via E.**

    For a witness atom `P` (in π, off l, off m, off O⊔C, ≠ I) and a
    non-degenerate dilation parameter `c`, the dilation σ_c(P) is
    recoverable from σ_c(beta_cast Γ P) via the line through E and the
    original ray O⊔P:

      `σ_c(P) = (σ_c(beta_cast Γ P) ⊔ E) ⊓ (O⊔P)`

    Proof structure:
      1. `P' := beta_cast Γ P` is a witness on q (atom, off l/m/O⊔C, ≠ I/O).
      2. Collinearity through E: P, P', E lie on the line P⊔E, so
         `(P⊔P')⊓m = E`. By `dilation_preserves_direction`,
         `(σ_c(P)⊔σ_c(P'))⊓m = E`, hence E ≤ σ_c(P)⊔σ_c(P').
      3. The line σ_c(P)⊔σ_c(P') equals σ_c(P')⊔E (CovBy on the line),
         so σ_c(P) ≤ σ_c(P')⊔E.
      4. σ_c(P) ≤ O⊔P by definition. So σ_c(P) ≤ (σ_c(P')⊔E) ⊓ (O⊔P).
      5. The right side is an atom (two distinct lines in π meet at one
         atom). Atom equality concludes. -/
theorem recovery_via_E (Γ : CoordSystem L)
    (c : L) (hc : IsAtom c) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (hc_ne_O : c ≠ Γ.O) (hc_ne_U : c ≠ Γ.U) (hc_ne_I : c ≠ Γ.I)
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_ne_I : P ≠ Γ.I)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ c P =
      (dilation_ext Γ c (beta_cast Γ P) ⊔ Γ.E) ⊓ (Γ.O ⊔ P) := by
  set m := Γ.U ⊔ Γ.V
  set q := Γ.U ⊔ Γ.C
  set π := Γ.O ⊔ Γ.U ⊔ Γ.V
  set P' := beta_cast Γ P with hP'_def
  set σP := dilation_ext Γ c P
  set σP' := dilation_ext Γ c P'
  -- Reusable distinctness for hypotheses
  have hP_ne_O : P ≠ Γ.O := fun h => hP_not_l (h ▸ le_sup_left)
  have hOC_ne : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUC_ne : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  -- ═══ Step 1: P' = beta_cast Γ P is a witness on q ═══
  -- Compute C⊔E = O⊔C (CovBy: C ⋖ O⊔C, C < C⊔E ≤ O⊔C)
  have hC_ne_E : Γ.C ≠ Γ.E := fun h => Γ.hC_not_m (h ▸ Γ.hE_on_m)
  have hCE_eq_OC : Γ.C ⊔ Γ.E = Γ.O ⊔ Γ.C := by
    have hC_lt : Γ.C < Γ.C ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h => hC_ne_E ((Γ.hC.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have hC_covBy : Γ.C ⋖ Γ.O ⊔ Γ.C := by
      rw [sup_comm]; exact atom_covBy_join Γ.hC Γ.hO hOC_ne.symm
    exact (hC_covBy.eq_or_eq hC_lt.le (sup_le le_sup_right CoordSystem.hE_le_OC)).resolve_left
      (ne_of_gt hC_lt)
  -- P off C⊔E (since C⊔E = O⊔C and P off O⊔C)
  have hP_not_CE : ¬ P ≤ Γ.C ⊔ Γ.E := fun h => hP_not_OC (hCE_eq_OC ▸ h)
  -- U⊔E = m (CovBy: E < U⊔E ≤ m, E ⋖ m via E_sup_EI_eq_m... actually let me just use covering)
  have hU_ne_E : Γ.U ≠ Γ.E := fun h => Γ.hE_not_l (h ▸ le_sup_right)
  have hUE_le_m : Γ.U ⊔ Γ.E ≤ m := sup_le le_sup_left Γ.hE_on_m
  -- P off U⊔E (P off m, U⊔E ≤ m)
  have hP_not_UE : ¬ P ≤ Γ.U ⊔ Γ.E := fun h => hP_not_m (h.trans hUE_le_m)
  -- P ≠ E (E on m, P off m)
  have hP_ne_E : P ≠ Γ.E := fun h => hP_not_m (h ▸ Γ.hE_on_m)
  -- P⊔E covers P (atom_covBy_join P E with P ≠ E)
  have hPE_covBy_P : P ⋖ P ⊔ Γ.E := atom_covBy_join hP Γ.hE_atom hP_ne_E
  -- Distinct lines q and P⊔E (in π); their meet is an atom = P'.
  -- q ⋖ π: standard lemma (q is the β-line)
  have hq_covBy_π : q ⋖ π := by
    -- Reuse the structure: q = U⊔C, q⊓m = U, V ⋖ m gives V⊓q ⋖ V; then V⊔q = m⊔C = π.
    -- Or use line_covBy_plane directly.
    have hq_inf_m : q ⊓ m = Γ.U := by
      change (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
      rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
      have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
        (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
      rw [this, sup_bot_eq]
    -- m⊔q = m⊔C = π (since C off m, m ⋖ m⊔C = π)
    have hUV_ne : Γ.U ≠ Γ.V := fun h => Γ.hV_off (h ▸ le_sup_right)
    have h_inf : m ⊓ q ⋖ m := by
      rw [inf_comm, hq_inf_m]; exact atom_covBy_join Γ.hU Γ.hV hUV_ne
    have h1 := covBy_sup_of_inf_covBy_left h_inf
    have hmq : m ⊔ q = m ⊔ Γ.C := by
      change m ⊔ (Γ.U ⊔ Γ.C) = m ⊔ Γ.C
      rw [← sup_assoc, sup_eq_left.mpr (le_sup_left : Γ.U ≤ m)]
    have hmC : m ⊔ Γ.C = π :=
      (Γ.m_covBy_π.eq_or_eq (le_sup_left : m ≤ m ⊔ Γ.C)
        (sup_le Γ.m_covBy_π.le Γ.hC_plane)).resolve_left
        (ne_of_gt (lt_of_le_of_ne le_sup_left
          (fun h => Γ.hC_not_m (le_sup_right.trans h.symm.le))))
    rwa [hmq, hmC] at h1
  -- P⊔E is in π (P, E both in π)
  have hPE_le_π : P ⊔ Γ.E ≤ π :=
    sup_le hP_plane (Γ.hE_on_m.trans Γ.m_covBy_π.le)
  -- P⊔E ⋖ π: P, E coplanar in π; line_covBy_plane needs O off P⊔E
  have hPE_covBy_π : P ⊔ Γ.E ⋖ π := by
    -- O ∉ P⊔E: if O ≤ P⊔E, then O⊔P ≤ P⊔E. O ⋖ O⊔P (P ≠ O), O < P⊔E.
    -- Then O⊔P ≤ P⊔E. P⊔E covers P; so P⊔E = O⊔P or P⊔E = P. But E ∉ {P, O⊔P}.
    -- E ≠ P (hP_ne_E), and E ∉ O⊔P (since E ≤ O⊔C, P off O⊔C, O⊔C ≠ O⊔P).
    have hE_not_OP : ¬ Γ.E ≤ Γ.O ⊔ P := by
      intro h
      -- O⊔E = O⊔C (CovBy on O⊔C, since O < O⊔E ≤ O⊔C)
      have hO_ne_E : Γ.O ≠ Γ.E := fun h' => Γ.hO_not_m (h' ▸ Γ.hE_on_m)
      have hOE_le_OC : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left CoordSystem.hE_le_OC
      have hO_lt_OE : Γ.O < Γ.O ⊔ Γ.E := lt_of_le_of_ne le_sup_left
        (fun h' => hO_ne_E ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
          Γ.hE_atom.1).symm)
      have hO_covBy_OC : Γ.O ⋖ Γ.O ⊔ Γ.C := atom_covBy_join Γ.hO Γ.hC hOC_ne
      have hOE_eq_OC : Γ.O ⊔ Γ.E = Γ.O ⊔ Γ.C :=
        (hO_covBy_OC.eq_or_eq hO_lt_OE.le hOE_le_OC).resolve_left (ne_of_gt hO_lt_OE)
      -- O⊔E ≤ O⊔P (from h)
      have hOE_le_OP : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ P := sup_le le_sup_left h
      have hOC_le_OP : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ P := hOE_eq_OC ▸ hOE_le_OP
      -- O⊔P covers O, O⊔C strictly above O, so O⊔C = O⊔P, hence P on O⊔C ✗
      have hO_lt_OC : Γ.O < Γ.O ⊔ Γ.C := hO_covBy_OC.lt
      have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
      have hOC_eq_OP : Γ.O ⊔ Γ.C = Γ.O ⊔ P :=
        (hO_covBy_OP.eq_or_eq hO_lt_OC.le hOC_le_OP).resolve_left (ne_of_gt hO_lt_OC)
      exact hP_not_OC (le_sup_right.trans hOC_eq_OP.symm.le)
    have hO_not_PE : ¬ Γ.O ≤ P ⊔ Γ.E := by
      intro h
      -- P⊔E meets m: hPE_le_π gives P⊔E ≤ π. (P⊔E)⊓m = E (E ≤ both, atom).
      -- If O ≤ P⊔E, then O,P,E ≤ P⊔E. covering forces P⊔E = O⊔P or O⊔E or...
      -- Direct: if O ≤ P⊔E, then E ∈ O⊔P (modular: E ≤ (P⊔E) ⊓ (O⊔E)... hmm).
      -- Cleaner: O,P,E ≤ P⊔E (height 2), so O ≤ P⊔E with P,E spanning the line.
      -- Then O⊔E ≤ P⊔E (line containment), and since O ⋖ O⊔E, P⊔E = O⊔E unless O=O⊔E.
      -- Actually: if O ≤ P⊔E and P⊔E is a line (covers P), then either O = P (no, O ≠ P)
      -- or O⊔P = P⊔E (covering: P < O⊔P ≤ P⊔E, P ⋖ P⊔E gives equality).
      have hOP_le : Γ.O ⊔ P ≤ P ⊔ Γ.E := sup_le h le_sup_left
      have hP_lt : P < Γ.O ⊔ P := lt_of_le_of_ne le_sup_right
        (fun h' => hP_ne_O ((hP.le_iff.mp (le_sup_left.trans h'.symm.le)).resolve_left
          Γ.hO.1).symm)
      have hPE_eq : P ⊔ Γ.E = Γ.O ⊔ P :=
        (hPE_covBy_P.eq_or_eq hP_lt.le hOP_le).resolve_left (ne_of_gt hP_lt) |>.symm
      exact hE_not_OP (le_sup_right.trans hPE_eq.le)
    have hPEO_eq : P ⊔ Γ.E ⊔ Γ.O = π := by
      -- P⊔E ⋖ ? gives P⊔E < P⊔E⊔O ≤ π, with line_covBy_plane.
      -- But we want = π. Use: l ≤ P⊔E⊔O via O,P joined, then plane covering.
      -- Actually simpler: P⊔E⊔O ≥ O⊔P (subset). O⊔P ⋖ π via earlier. O⊔P < P⊔E⊔O.
      -- Hmm need to verify. Let me just compute upper bound and use covering.
      have hOP_covBy_π : Γ.O ⊔ P ⋖ π := by
        have hU_not_OP : ¬ Γ.U ≤ Γ.O ⊔ P := by
          intro h
          have hOU_le_OP : Γ.O ⊔ Γ.U ≤ Γ.O ⊔ P := sup_le le_sup_left h
          have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
          have hO_lt_l : Γ.O < Γ.O ⊔ Γ.U := (atom_covBy_join Γ.hO Γ.hU Γ.hOU).lt
          have hl_eq_OP : Γ.O ⊔ Γ.U = Γ.O ⊔ P :=
            (hO_covBy_OP.eq_or_eq hO_lt_l.le hOU_le_OP).resolve_left (ne_of_gt hO_lt_l)
          exact hP_not_l (le_sup_right.trans hl_eq_OP.symm.le)
        have hOPU_eq : Γ.O ⊔ P ⊔ Γ.U = π := by
          show Γ.O ⊔ P ⊔ Γ.U = Γ.O ⊔ Γ.U ⊔ Γ.V
          have hl_covBy_π : Γ.O ⊔ Γ.U ⋖ Γ.O ⊔ Γ.U ⊔ Γ.V := by
            have hV_disj : Γ.V ⊓ (Γ.O ⊔ Γ.U) = ⊥ :=
              (Γ.hV.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hV_off (h ▸ inf_le_right))
            have := covBy_sup_of_inf_covBy_left (hV_disj ▸ Γ.hV.bot_covBy)
            rwa [show Γ.V ⊔ (Γ.O ⊔ Γ.U) = Γ.O ⊔ Γ.U ⊔ Γ.V from by rw [sup_comm]] at this
          rw [show Γ.O ⊔ P ⊔ Γ.U = (Γ.O ⊔ Γ.U) ⊔ P from by ac_rfl]
          have hl_lt : Γ.O ⊔ Γ.U < (Γ.O ⊔ Γ.U) ⊔ P := lt_of_le_of_ne le_sup_left
            (fun h => hP_not_l (le_sup_right.trans h.symm.le))
          exact (hl_covBy_π.eq_or_eq hl_lt.le
            (sup_le hl_covBy_π.le hP_plane)).resolve_left (ne_of_gt hl_lt)
        rw [← hOPU_eq]
        exact line_covBy_plane Γ.hO hP Γ.hU (Ne.symm hP_ne_O) Γ.hOU
          (fun h => hU_not_OP (h ▸ le_sup_right)) hU_not_OP
      have hOP_lt : Γ.O ⊔ P < P ⊔ Γ.E ⊔ Γ.O := by
        apply lt_of_le_of_ne
        · rw [show P ⊔ Γ.E ⊔ Γ.O = Γ.O ⊔ P ⊔ Γ.E from by ac_rfl]
          exact le_sup_left
        · intro h
          -- O⊔P = P⊔E⊔O means E ≤ O⊔P, contradicting hE_not_OP
          have hE_le : Γ.E ≤ Γ.O ⊔ P := by
            rw [h]; exact le_sup_right.trans le_sup_left
          exact hE_not_OP hE_le
      exact (hOP_covBy_π.eq_or_eq hOP_lt.le
        (sup_le hPE_le_π (le_sup_left.trans le_sup_left))).resolve_left (ne_of_gt hOP_lt)
    have hE_ne_O : Γ.E ≠ Γ.O := fun h => Γ.hO_not_m (h ▸ Γ.hE_on_m)
    rw [← hPEO_eq]
    exact line_covBy_plane hP Γ.hE_atom Γ.hO hP_ne_E hP_ne_O hE_ne_O hO_not_PE
  -- Distinctness q ≠ P⊔E: q goes through U,C; P⊔E goes through P,E.
  -- If equal, then P,E ≤ q. P off l, q⊓l = U, but q ⊓ l = U is on q;
  -- E ≤ q would force E ≤ q⊓m = U, E = U, ✗. So q ≠ P⊔E.
  have hE_not_q : ¬ Γ.E ≤ q := by
    intro h
    have hE_le_U : Γ.E ≤ Γ.U := by
      have hqm : q ⊓ m = Γ.U := by
        change (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
        rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
        have : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
          (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h' => Γ.hC_not_m (h' ▸ inf_le_right))
        rw [this, sup_bot_eq]
      exact hqm ▸ le_inf h Γ.hE_on_m
    exact hU_ne_E ((Γ.hU.le_iff.mp hE_le_U).resolve_left Γ.hE_atom.1).symm
  have hq_ne_PE : q ≠ P ⊔ Γ.E := fun h => hE_not_q (h ▸ le_sup_right)
  -- P' = q ⊓ (P⊔E) is an atom (planes_meet_covBy + line_height_two on q)
  have h_meet := planes_meet_covBy hq_covBy_π hPE_covBy_π hq_ne_PE
  have hP'_atom : IsAtom P' := by
    show IsAtom (q ⊓ (P ⊔ Γ.E))
    -- meet ⋖ q (height 2 in q). It's nonzero because if it were ⊥, then q ⊔ (P⊔E) wouldn't
    -- cover-up to π via planes_meet_covBy's left side. But h_meet.1 directly says
    -- meet ⋖ q; combined with C ≤ q (so q strictly above ⊥), meet is at height 1 = atom.
    -- Use line_height_two: requires ⊥ < meet < q. The strict-below is the missing piece.
    have h_ne_bot : q ⊓ (P ⊔ Γ.E) ≠ ⊥ := by
      intro h_eq
      have h_bot_covBy : ⊥ ⋖ q := h_eq ▸ h_meet.1
      have hC_pos : ⊥ < Γ.C := Γ.hC.bot_lt
      have hC_le_q : Γ.C ≤ q := le_sup_right
      have hC_lt_q : ⊥ < q := lt_of_lt_of_le hC_pos hC_le_q
      -- ⊥ ⋖ q says nothing strictly between. But we don't have anything strictly between.
      -- Use that q is a line (height 2), so ⊥ < q gives an atom strictly below q.
      -- Actually the ⊥ ⋖ q would force q to be an atom; but q is a line so q has height 2.
      -- Concretely: U ≤ q, U is an atom, ⊥ < U < q (since q ≠ U: q has C off l).
      have hU_lt_q : Γ.U < q := lt_of_le_of_ne le_sup_left
        (fun h => hUC_ne ((Γ.hU.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
          Γ.hC.1).symm)
      exact h_bot_covBy.2 Γ.hU.bot_lt hU_lt_q
    exact line_height_two Γ.hU Γ.hC hUC_ne (bot_lt_iff_ne_bot.mpr h_ne_bot) h_meet.1.lt
  -- TODO(s135): finish steps 2-5 once Step 1's structure is verified.
  sorry

/-! ## Capstone: `coord_mul_assoc`

The s133 stub's recipe (using `dilation_mul_key_identity` four times +
a "composition step") was a first-attempt sketch. **s134 found a
cleaner architecture**: the substantive geometric content concentrates
into a single named lemma, `dilation_compose_at_witness` (below), and
`coord_mul_assoc` becomes a thin algebraic assembly using it three
times + `dilation_determined_by_param`. The four `dilation_mul_key_identity`
applications turn out not to be needed for the capstone.

The s133 prediction (no fresh `DesarguesianWitness` needed) becomes a
prediction about `dilation_compose_at_witness` specifically — the
witness-detection question is now localized to that one lemma.
-/

/-- **Dilation composition law at a witness.**

    For atoms `x, y` on `l` (non-degenerate) and a witness atom `P`
    in π but off `l`, `m`, `O⊔C`, with `P ≠ I`:

      `σ_(x·y)(P) = σ_y(σ_x(P))`

    i.e., `dilation_ext Γ (coord_mul Γ x y) P = dilation_ext Γ y (dilation_ext Γ x P)`.

    This is the substantive geometric content of `coord_mul_assoc` —
    everything above this lemma in the multiplicative chain
    (`dilation_ext`, `dilation_preserves_direction`,
    `dilation_mul_key_identity`, `dilation_determined_by_param`) is
    setup; everything below it (`coord_mul_assoc`,
    `coord_mul_left_inv`, the DivisionRing instance) is algebraic
    consequence. The s132 "device-shape" question — whether the
    multiplicative branch needs a third `DesarguesianWitness`-style
    observer commitment — is concentrated here.

    ## Why this is the substantive content

    `coord_mul_assoc` is `(x·y)·z = x·(y·z)`. Applied at a witness `P`:

      `σ_((x·y)·z)(P) = σ_z(σ_(x·y)(P)) = σ_z(σ_y(σ_x(P)))`     [3 applications]
      `σ_(x·(y·z))(P) = σ_(y·z)(σ_x(P)) = σ_z(σ_y(σ_x(P)))`     [3 applications]

    so `σ_LHS(P) = σ_RHS(P)`, hence `LHS = RHS` by
    `dilation_determined_by_param`. The capstone is ~30 lines once
    this lemma lands.

    ## Proof sketch (proposed)

    Both `σ_(x·y)(P)` and `σ_y(σ_x(P))` lie on `O⊔P`:
      * `σ_(x·y)(P) = (O⊔P) ⊓ ((x·y) ⊔ d_P)` where `d_P = (I⊔P)⊓m`.
      * `σ_x(P) ≤ O⊔P`, so `σ_y(σ_x(P)) ≤ O⊔σ_x(P) = O⊔P`.

    To show two atoms on `O⊔P` are equal: distinguish them by a
    second line meeting `O⊔P` at a single atom. The natural Desargues
    setup: triangle `(P, σ_x(P), σ_y(σ_x(P)))` perspective from `O` to
    triangle `(I, x, x·y)` (each pair of corresponding vertices on a
    ray through `O`). Sides meet on `m` (the axis of dilation).

    **Witness-detection point (s132 device-shape conjecture):** if
    this proof needs a fresh `desargues_planar` call whose center or
    axis hypothesis reduces to associativity itself, that's the third
    witness — name as a typed structure analogous to
    `DesarguesianWitness`, thread through this lemma as an explicit
    parameter. The s133 prediction is that the existing
    `dilation_preserves_direction` (a forward Desargues with center O,
    PROVEN) suffices; this lemma's proof attempt is the test. -/
theorem dilation_compose_at_witness (Γ : CoordSystem L)
    (x y : L) (hx : IsAtom x) (hy : IsAtom y)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U)
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_ne_I : P ≠ Γ.I)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ (coord_mul Γ x y) P =
      dilation_ext Γ y (dilation_ext Γ x P) := by
  sorry

/-- **Witness preservation under dilation.**

    If `P` is a valid witness for `dilation_compose_at_witness` and
    `dilation_determined_by_param` (atom in π, off l, off m, off O⊔C,
    ≠ I), and `x` is a non-degenerate dilation parameter (atom on l,
    ≠ O, ≠ U, ≠ I), then `dilation_ext Γ x P` is also a valid
    witness. Used to chain `dilation_compose_at_witness` calls in
    `coord_mul_assoc`.

    Sub-claims, decomposed:
      * `σ_x(P)` atom — `dilation_ext_atom`, PROVEN
      * `σ_x(P) ≤ π` — `dilation_ext_plane`, PROVEN
      * `σ_x(P) ∉ m` — `dilation_ext_not_m`, PROVEN
      * `σ_x(P) ∉ l` — short modular argument; appears inline at
        FTPGDilation:646 inside `dilation_preserves_direction`
      * `σ_x(P) ∉ O⊔C` — needs proof (similar modular shape)
      * `σ_x(P) ≠ I` — needs proof; uses dilation injectivity at I
        (`σ_x(I) = x ≠ I`, so if `σ_x(P) = I` then `P = I` ✗) -/
theorem dilation_witness_preservation (Γ : CoordSystem L)
    (x : L) (hx : IsAtom x) (hx_on : x ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hx_ne_U : x ≠ Γ.U) (hx_ne_I : x ≠ Γ.I)
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_ne_I : P ≠ Γ.I)
    (hP_ne_O : P ≠ Γ.O) :
    IsAtom (dilation_ext Γ x P) ∧
    dilation_ext Γ x P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V ∧
    ¬ dilation_ext Γ x P ≤ Γ.O ⊔ Γ.U ∧
    ¬ dilation_ext Γ x P ≤ Γ.U ⊔ Γ.V ∧
    ¬ dilation_ext Γ x P ≤ Γ.O ⊔ Γ.C ∧
    dilation_ext Γ x P ≠ Γ.I := by
  set m := Γ.U ⊔ Γ.V
  set l := Γ.O ⊔ Γ.U
  set σ := dilation_ext Γ x P
  set d_P := (Γ.I ⊔ P) ⊓ m
  -- ═══ Sub-claim 1: σ atom (existing lemma) ═══
  have hσ_atom : IsAtom σ :=
    dilation_ext_atom Γ hP hx hx_on hx_ne_O hx_ne_U hP_plane hP_not_l hP_ne_O hP_ne_I hP_not_m
  -- ═══ Sub-claim 2: σ ≤ π (existing lemma) ═══
  have hσ_plane : σ ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := dilation_ext_plane Γ hP hx hx_on hP_plane
  -- ═══ Sub-claim 3: σ ∉ m (existing lemma) ═══
  have hσ_not_m : ¬ σ ≤ m :=
    dilation_ext_not_m Γ hP hx hx_on hx_ne_O hx_ne_U hP_plane hP_not_m hP_not_l hP_ne_O
      hP_ne_I hx_ne_I
  -- ═══ Helpers shared across remaining sub-claims ═══
  have hx_not_m : ¬ x ≤ m := fun h => hx_ne_U (Γ.atom_on_both_eq_U hx hx_on h)
  have hOC : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hUC : Γ.U ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_right)
  have hOx_eq_l : Γ.O ⊔ x = l := by
    show Γ.O ⊔ x = Γ.O ⊔ Γ.U
    have hO_lt : Γ.O < Γ.O ⊔ x := by
      apply lt_of_le_of_ne le_sup_left; intro h
      exact hx_ne_O ((Γ.hO.le_iff.mp (h ▸ le_sup_right)).resolve_left hx.1)
    exact ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt.le
      (sup_le le_sup_left hx_on)).resolve_left (ne_of_gt hO_lt)
  have hd_P_atom : IsAtom d_P :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  have hσ_le_OP : σ ≤ Γ.O ⊔ P := inf_le_left
  -- ═══ Key sub-claim: σ ≠ O ═══
  -- If σ = O, then O ≤ x ⊔ d_P (since σ ≤ x ⊔ d_P).
  -- Then O ⊔ x = l ≤ x ⊔ d_P. So U ≤ l ⊓ m ≤ (x ⊔ d_P) ⊓ m = d_P (line_direction).
  -- So U = d_P (atoms). Then U ≤ I ⊔ P, so I ⊔ U = l ≤ I ⊔ P, so P ≤ l. ✗
  have hσ_ne_O : σ ≠ Γ.O := by
    intro h_eq
    have hO_le_xdP : Γ.O ≤ x ⊔ d_P := h_eq ▸ (inf_le_right : σ ≤ x ⊔ d_P)
    have hl_le_xdP : l ≤ x ⊔ d_P :=
      hOx_eq_l.symm.le.trans (sup_le hO_le_xdP le_sup_left)
    have hxdP_inf_m : (x ⊔ d_P) ⊓ m = d_P :=
      line_direction hx hx_not_m (inf_le_right : d_P ≤ m)
    have hU_le_dP : Γ.U ≤ d_P := by
      have h1 : Γ.U ≤ (x ⊔ d_P) ⊓ m :=
        le_inf ((le_sup_right : Γ.U ≤ l).trans hl_le_xdP) (le_sup_left : Γ.U ≤ m)
      exact hxdP_inf_m ▸ h1
    have hU_eq_dP : Γ.U = d_P := IsAtom.eq_of_le Γ.hU hd_P_atom hU_le_dP
    -- U = d_P = (I⊔P)⊓m, so U ≤ I⊔P
    have hU_le_IP : Γ.U ≤ Γ.I ⊔ P := hU_eq_dP ▸ (inf_le_left : d_P ≤ Γ.I ⊔ P)
    -- I⊔U covers I (atom_covBy_join with I ≠ U)
    have hIU_covBy : Γ.I ⋖ Γ.I ⊔ Γ.U := atom_covBy_join Γ.hI Γ.hU Γ.hUI.symm
    -- I⊔U ≤ I⊔P (U ≤ I⊔P, I ≤ I⊔P)
    have hIU_le_IP : Γ.I ⊔ Γ.U ≤ Γ.I ⊔ P := sup_le le_sup_left hU_le_IP
    -- I < I⊔U (cover relation)
    have hI_lt_IU : Γ.I < Γ.I ⊔ Γ.U := hIU_covBy.lt
    -- I ⋖ I⊔P (atom_covBy_join with P ≠ I)
    have hI_covBy_IP : Γ.I ⋖ Γ.I ⊔ P := atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)
    -- I⊔U = I⊔P (by covering on I⊔P, since I⊔U strictly above I and ≤ I⊔P)
    have hIU_eq_IP : Γ.I ⊔ Γ.U = Γ.I ⊔ P :=
      (hI_covBy_IP.eq_or_eq hI_lt_IU.le hIU_le_IP).resolve_left (ne_of_gt hI_lt_IU)
    -- I⊔U = l (covering on U ⋖ l with I < I⊔U, both ≤ l)
    have hIU_eq_l : Γ.I ⊔ Γ.U = l := by
      show Γ.I ⊔ Γ.U = Γ.O ⊔ Γ.U
      have hI_le_l : Γ.I ≤ Γ.O ⊔ Γ.U := Γ.hI_on
      have hIU_le_l : Γ.I ⊔ Γ.U ≤ Γ.O ⊔ Γ.U := sup_le hI_le_l le_sup_right
      have hU_lt : Γ.U < Γ.I ⊔ Γ.U := lt_of_le_of_ne le_sup_right
        (fun h => Γ.hUI ((Γ.hU.le_iff.mp (le_sup_left.trans h.symm.le)).resolve_left Γ.hI.1).symm)
      have hU_covBy_l : Γ.U ⋖ Γ.O ⊔ Γ.U := by
        rw [sup_comm]; exact atom_covBy_join Γ.hU Γ.hO Γ.hOU.symm
      exact (hU_covBy_l.eq_or_eq hU_lt.le hIU_le_l).resolve_left (ne_of_gt hU_lt)
    -- So I⊔P = l, hence P ≤ l. Contradiction.
    exact hP_not_l (le_sup_right.trans (hIU_eq_IP.symm.trans hIU_eq_l).le)
  -- ═══ Sub-claim 4: σ ∉ l ═══
  -- σ ≤ O⊔P. If σ ≤ l, then σ ≤ l ⊓ (O⊔P) = O (modular). So σ = O. ✗
  have hOP_l_eq_O : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ P) = Γ.O :=
    modular_intersection Γ.hO Γ.hU hP Γ.hOU (Ne.symm hP_ne_O)
      (fun h' => hP_not_l (h' ▸ le_sup_right)) hP_not_l
  have hσ_not_l : ¬ σ ≤ l := by
    intro h
    have hσ_le_O : σ ≤ Γ.O := hOP_l_eq_O ▸ le_inf h hσ_le_OP
    exact hσ_ne_O ((Γ.hO.le_iff.mp hσ_le_O).resolve_left hσ_atom.1)
  -- ═══ Sub-claim 5: σ ∉ O⊔C ═══
  -- σ ≤ O⊔P. If σ ≤ O⊔C, then σ ≤ (O⊔P) ⊓ (O⊔C) = O (modular, since P ∉ O⊔C).
  -- Need: ¬ C ≤ O⊔P (else O⊔C ≤ O⊔P, covering forces O⊔C = O⊔P, P ≤ O⊔C ✗)
  have hC_not_OP : ¬ Γ.C ≤ Γ.O ⊔ P := by
    intro h
    have hOC_le : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ P := sup_le le_sup_left h
    have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
    have hO_lt_OC : Γ.O < Γ.O ⊔ Γ.C := lt_of_le_of_ne le_sup_left
      (fun h' => hOC ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left Γ.hC.1).symm)
    have hOC_eq_OP : Γ.O ⊔ Γ.C = Γ.O ⊔ P :=
      (hO_covBy_OP.eq_or_eq hO_lt_OC.le hOC_le).resolve_left (ne_of_gt hO_lt_OC)
    exact hP_not_OC (le_sup_right.trans hOC_eq_OP.symm.le)
  have hP_ne_C : P ≠ Γ.C := fun h => hP_not_OC (h ▸ le_sup_right)
  have hOP_OC_eq_O : (Γ.O ⊔ P) ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
    modular_intersection Γ.hO hP Γ.hC (Ne.symm hP_ne_O) hOC hP_ne_C hC_not_OP
  have hσ_not_OC : ¬ σ ≤ Γ.O ⊔ Γ.C := by
    intro h
    have hσ_le_O : σ ≤ Γ.O := hOP_OC_eq_O ▸ le_inf hσ_le_OP h
    exact hσ_ne_O ((Γ.hO.le_iff.mp hσ_le_O).resolve_left hσ_atom.1)
  -- ═══ Sub-claim 6: σ ≠ I ═══
  -- σ ≤ O⊔P. If σ = I, then I ≤ O⊔P, then O⊔I = l ≤ O⊔P (covering), so P ≤ l. ✗
  have hσ_ne_I : σ ≠ Γ.I := by
    intro h_eq
    have hI_le_OP : Γ.I ≤ Γ.O ⊔ P := h_eq ▸ hσ_le_OP
    have hOI_le_OP : Γ.O ⊔ Γ.I ≤ Γ.O ⊔ P := sup_le le_sup_left hI_le_OP
    have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
    have hO_lt_OI : Γ.O < Γ.O ⊔ Γ.I := lt_of_le_of_ne le_sup_left
      (fun h => Γ.hOI ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hI.1).symm)
    have hOI_eq_OP : Γ.O ⊔ Γ.I = Γ.O ⊔ P :=
      (hO_covBy_OP.eq_or_eq hO_lt_OI.le hOI_le_OP).resolve_left (ne_of_gt hO_lt_OI)
    -- O⊔I = l (covering)
    have hOI_eq_l : Γ.O ⊔ Γ.I = l := by
      show Γ.O ⊔ Γ.I = Γ.O ⊔ Γ.U
      have hO_covBy_l : Γ.O ⋖ Γ.O ⊔ Γ.U := atom_covBy_join Γ.hO Γ.hU Γ.hOU
      exact (hO_covBy_l.eq_or_eq hO_lt_OI.le (sup_le le_sup_left Γ.hI_on)).resolve_left
        (ne_of_gt hO_lt_OI)
    -- l = O⊔P, so P ≤ l. ✗
    -- chain: P ≤ O⊔P = O⊔I (hOI_eq_OP.symm) = l (hOI_eq_l)
    exact hP_not_l (le_sup_right.trans (hOI_eq_OP.symm.trans hOI_eq_l).le)
  exact ⟨hσ_atom, hσ_plane, hσ_not_l, hσ_not_m, hσ_not_OC, hσ_ne_I⟩

/-- **Associativity of coordinate multiplication.**

    `(a·b)·c = a·(b·c)`

    ## Proof architecture (s134)

    Capstone assembly using `dilation_compose_at_witness` (the
    substantive lemma) three times plus `dilation_determined_by_param`:

      1. Take a witness `P` off `l`, `m`, `O⊔C`, `≠ I`. (Threaded as
         an explicit hypothesis here — the construction of such a
         `P` from `R`, `h_irred` is a separate task; it parallels
         `coord_add_assoc`'s `P = (b ⊔ E) ⊓ (a ⊔ C)` move.)
      2. Apply `dilation_compose_at_witness` at `(s, c, P)`:
           `σ_(s·c)(P) = σ_c(σ_s(P))`     where `s = a·b`
      3. Apply `dilation_compose_at_witness` at `(a, b, P)`:
           `σ_s(P) = σ_(a·b)(P) = σ_b(σ_a(P))`
         Substitute into (2):
           `σ_(s·c)(P) = σ_c(σ_b(σ_a(P)))`            [LHS evaluated]
      4. Apply `dilation_compose_at_witness` at `(a, t, P)`:
           `σ_(a·t)(P) = σ_t(σ_a(P))`     where `t = b·c`
      5. Apply `dilation_compose_at_witness` at `(b, c, σ_a(P))`:
           `σ_t(σ_a(P)) = σ_(b·c)(σ_a(P)) = σ_c(σ_b(σ_a(P)))`
         Substitute into (4):
           `σ_(a·t)(P) = σ_c(σ_b(σ_a(P)))`            [RHS evaluated]
      6. From (3) and (5): `σ_(s·c)(P) = σ_(a·t)(P)`.
      7. `dilation_determined_by_param` gives `s·c = a·t`. ∎

    Hypothesis preservation at step 5 — `σ_a(P)` is a valid witness
    for the next call — is `dilation_witness_preservation` (above).

    Per the s134 architecture: the only **substantive** sorry is
    `dilation_compose_at_witness`. `dilation_witness_preservation`
    is mechanical lattice algebra (the inline proof from
    `dilation_preserves_direction:646` covers most of it).
    The capstone is ~30 lines of clean assembly.

    Witness parameters `R, hR, hR_not, h_irred` thread through to
    `dilation_compose_at_witness` (which makes Desargues calls
    inside its proof). -/
theorem coord_mul_assoc (Γ : CoordSystem L)
    (a b c : L) (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (ha_on : a ≤ Γ.O ⊔ Γ.U) (hb_on : b ≤ Γ.O ⊔ Γ.U) (hc_on : c ≤ Γ.O ⊔ Γ.U)
    (ha_ne_O : a ≠ Γ.O) (hb_ne_O : b ≠ Γ.O) (hc_ne_O : c ≠ Γ.O)
    (ha_ne_U : a ≠ Γ.U) (hb_ne_U : b ≠ Γ.U) (hc_ne_U : c ≠ Γ.U)
    (ha_ne_I : a ≠ Γ.I)
    (_hab : a ≠ b) (_hbc : b ≠ c) (_hac : a ≠ c)
    -- Non-degeneracy of intermediate products.
    (hs_ne_O : coord_mul Γ a b ≠ Γ.O) (hs_ne_U : coord_mul Γ a b ≠ Γ.U)
    (ht_ne_O : coord_mul Γ b c ≠ Γ.O) (ht_ne_U : coord_mul Γ b c ≠ Γ.U)
    (_hsc : coord_mul Γ a b ≠ c) (_hat : a ≠ coord_mul Γ b c)
    (hsc_ne_O : coord_mul Γ (coord_mul Γ a b) c ≠ Γ.O)
    (hsc_ne_U : coord_mul Γ (coord_mul Γ a b) c ≠ Γ.U)
    (hat_ne_O : coord_mul Γ a (coord_mul Γ b c) ≠ Γ.O)
    (hat_ne_U : coord_mul Γ a (coord_mul Γ b c) ≠ Γ.U)
    -- Witness atom P in the plane π, off l, m, O⊔C, ≠ I.
    -- Constructible from R + h_irred via a perspect_atom-style move
    -- (parallel to coord_add_assoc's P = (b⊔E)⊓(a⊔C)). Threaded
    -- as a hypothesis here to keep the capstone tight; the
    -- construction is a separate task below this lemma.
    {P : L} (hP : IsAtom P) (hP_plane : P ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (hP_not_l : ¬ P ≤ Γ.O ⊔ Γ.U) (hP_not_m : ¬ P ≤ Γ.U ⊔ Γ.V)
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_ne_I : P ≠ Γ.I) (hP_ne_O : P ≠ Γ.O)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    coord_mul Γ (coord_mul Γ a b) c = coord_mul Γ a (coord_mul Γ b c) := by
  set s := coord_mul Γ a b with hs_def
  set t := coord_mul Γ b c with ht_def
  -- ═══ Atomicity + on-l for intermediate products ═══
  have hs_atom : IsAtom s := coord_mul_atom Γ a b ha hb ha_on hb_on ha_ne_O hb_ne_O ha_ne_U hb_ne_U
  have ht_atom : IsAtom t := coord_mul_atom Γ b c hb hc hb_on hc_on hb_ne_O hc_ne_O hb_ne_U hc_ne_U
  have hs_on : s ≤ Γ.O ⊔ Γ.U := by show coord_mul Γ a b ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have ht_on : t ≤ Γ.O ⊔ Γ.U := by show coord_mul Γ b c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hsc_atom : IsAtom (coord_mul Γ s c) :=
    coord_mul_atom Γ s c hs_atom hc hs_on hc_on hs_ne_O hc_ne_O hs_ne_U hc_ne_U
  have hat_atom : IsAtom (coord_mul Γ a t) :=
    coord_mul_atom Γ a t ha ht_atom ha_on ht_on ha_ne_O ht_ne_O ha_ne_U ht_ne_U
  have hsc_on : coord_mul Γ s c ≤ Γ.O ⊔ Γ.U := by
    show coord_mul Γ (coord_mul Γ a b) c ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  have hat_on : coord_mul Γ a t ≤ Γ.O ⊔ Γ.U := by
    show coord_mul Γ a (coord_mul Γ b c) ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  -- ═══ Hypothesis preservation: σ_a(P) is a valid witness ═══
  obtain ⟨hσaP_atom, hσaP_plane, hσaP_not_l, hσaP_not_m, hσaP_not_OC, hσaP_ne_I⟩ :=
    dilation_witness_preservation Γ a ha ha_on ha_ne_O ha_ne_U ha_ne_I
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I hP_ne_O
  -- ═══ Step 1: σ_(s·c)(P) = σ_c(σ_s(P)) ═══   [LHS = s·c]
  have h_LHS_step : dilation_ext Γ (coord_mul Γ s c) P =
      dilation_ext Γ c (dilation_ext Γ s P) :=
    dilation_compose_at_witness Γ s c hs_atom hc hs_on hc_on
      hs_ne_O hc_ne_O hs_ne_U hc_ne_U
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I R hR hR_not h_irred
  -- ═══ Step 2: σ_s(P) = σ_b(σ_a(P)) ═══   [s = a·b]
  have h_s_decomp : dilation_ext Γ s P = dilation_ext Γ b (dilation_ext Γ a P) :=
    dilation_compose_at_witness Γ a b ha hb ha_on hb_on
      ha_ne_O hb_ne_O ha_ne_U hb_ne_U
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I R hR hR_not h_irred
  -- ═══ Step 3: σ_(a·t)(P) = σ_t(σ_a(P)) ═══   [RHS = a·t]
  have h_RHS_step : dilation_ext Γ (coord_mul Γ a t) P =
      dilation_ext Γ t (dilation_ext Γ a P) :=
    dilation_compose_at_witness Γ a t ha ht_atom ha_on ht_on
      ha_ne_O ht_ne_O ha_ne_U ht_ne_U
      hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I R hR hR_not h_irred
  -- ═══ Step 4: σ_t(σ_a(P)) = σ_c(σ_b(σ_a(P))) ═══   [t = b·c]
  have h_t_decomp : dilation_ext Γ t (dilation_ext Γ a P) =
      dilation_ext Γ c (dilation_ext Γ b (dilation_ext Γ a P)) :=
    dilation_compose_at_witness Γ b c hb hc hb_on hc_on
      hb_ne_O hc_ne_O hb_ne_U hc_ne_U
      hσaP_atom hσaP_plane hσaP_not_l hσaP_not_m hσaP_not_OC hσaP_ne_I
      R hR hR_not h_irred
  -- ═══ Step 5: σ_(s·c)(P) = σ_(a·t)(P) ═══
  have h_agree : dilation_ext Γ (coord_mul Γ s c) P =
      dilation_ext Γ (coord_mul Γ a t) P := by
    rw [h_LHS_step, h_s_decomp, h_RHS_step, h_t_decomp]
  -- ═══ Step 6: dilation_determined_by_param → s·c = a·t ═══
  exact dilation_determined_by_param Γ hsc_atom hat_atom hsc_on hat_on
    hsc_ne_O hat_ne_O hsc_ne_U hat_ne_U
    hP hP_plane hP_not_l hP_not_m hP_not_OC hP_ne_I h_agree

end Foam.FTPGExplore
