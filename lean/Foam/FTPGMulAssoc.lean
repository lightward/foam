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
    (Steps 1-5 PROVEN as of session 137. The proof discharges the
    P' witness conditions, derives σP ≠ σP' via modular_intersection
    on (O⊔P) ⊓ (O⊔P') = O, applies `dilation_preserves_direction`,
    then closes via atom equality on (σP'⊔E) ⊓ (O⊔P) using
    `meet_of_lines_is_atom`.)
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

### s137 status (recovery_via_E PROVEN)

`recovery_via_E` is closed — Steps 1-5 all land. The s135 P' verification
(Step 1, ~100 lines) and the s136 Step 2a (`(P⊔P')⊓m = E` via the
covering chain on `P⊔E`, ~25 lines) are joined by s137's discharge of
Steps 2b-5 (~250 lines). The architecture s135 predicted holds: the
β-cast bridge factors `dilation_compose_at_witness` cleanly through
`dilation_preserves_direction`, no fresh `*Witness` interface needed
for this reduction step.

Two pieces of structural cleanup landed in s137 to make Steps 2b-5
work:
  * `hE_not_OP` and `hO_not_PE` lifted out of the `hPE_covBy_π` proof
    body into outer scope of `recovery_via_E`. They're used in s137's
    Step 5 distinctness argument (`E ∉ O⊔P` powers `meet_of_lines_is_atom`
    on `(σP'⊔E) ⊓ (O⊔P)`); having them at outer scope avoids re-deriving
    them.
  * P' witness conditions (off l, off m, ≠ O, ≠ I, ≠ U) cluster around
    a single keystone: `P' ≠ U`, derived via the contradiction U ≤ P⊔E
    ⇒ E ≤ U through (P⊔U)⊓m = U. Once `P' ≠ U` lands, the rest fall out
    via `q⊓l = U` and `q⊓m = U` projections.

#### Subtleties resolved in s137

  * `dilation_preserves_direction`'s `h_images_ne` precondition
    (σP ≠ σP'): not derivable from generic dilation injectivity (no
    such lemma exists at this level). Adapted from
    `FTPGMulKeyIdentity:hσ_ne_DE` pattern: σP = σP' ⇒ σP ≤ (O⊔P)⊓(O⊔P')
    = O via modular_intersection (uses P' ⊄ O⊔P from `hPE_OP_eq_P`),
    then σP ⊄ l contradiction. The σP ⊄ l proof itself uses
    line_direction twice: σP ≤ l ⇒ σP = O via (O⊔P)⊓l = O, then σP = O
    ⇒ O ≤ c⊔d_P ⇒ O ≤ c via (c⊔d_P)⊓l = c, contradicting c ≠ O.
  * `d_P ⊄ l` (needed for the second line_direction above): if
    d_P ≤ l, then d_P ≤ l⊓m = U, so d_P = U. d_P = U ⇒ U ≤ I⊔P ⇒
    I⊔U = I⊔P (covering on I⊔P over I), hence P ≤ I⊔U = l, ✗.

### Historical context (s135 partial handoff)

Step 1 (P' as witness on q) and the modular juggling for its
conditions remain a real contribution from s135 — the s137 work
inherits all of it. The s135 docstring's predicted pieces:
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

    For a witness atom `P` (in π, off l, off m, off O⊔C, off q = U⊔C,
    ≠ I) and a non-degenerate dilation parameter `c`, the dilation
    σ_c(P) is recoverable from σ_c(beta_cast Γ P) via the line through
    E and the original ray O⊔P:

      `σ_c(P) = (σ_c(beta_cast Γ P) ⊔ E) ⊓ (O⊔P)`

    The `hP_not_q` hypothesis (P off q = U⊔C) narrows scope to the
    non-degenerate case. When P ≤ q, P is itself on the bridge line
    and `beta_cast Γ P = P`, so the recovery is trivial — but the
    proof argument via `(P⊔P')⊓m = E` degenerates (becomes ⊥). Callers
    that may face P ≤ q should case-split: in the on-q branch, P is a
    β-image and `dilation_mul_key_identity` applies directly without
    going through `recovery_via_E`.

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
    (hP_not_OC : ¬ P ≤ Γ.O ⊔ Γ.C) (hP_not_q : ¬ P ≤ Γ.U ⊔ Γ.C)
    (hP_ne_I : P ≠ Γ.I)
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
  -- E ∉ O⊔P (lifted to outer scope; reused in hPE_covBy_π below and in steps 4-5)
  have hE_not_OP : ¬ Γ.E ≤ Γ.O ⊔ P := by
    intro h
    have hO_ne_E : Γ.O ≠ Γ.E := fun h' => Γ.hO_not_m (h' ▸ Γ.hE_on_m)
    have hOE_le_OC : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left CoordSystem.hE_le_OC
    have hO_lt_OE : Γ.O < Γ.O ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h' => hO_ne_E ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have hO_covBy_OC : Γ.O ⋖ Γ.O ⊔ Γ.C := atom_covBy_join Γ.hO Γ.hC hOC_ne
    have hOE_eq_OC : Γ.O ⊔ Γ.E = Γ.O ⊔ Γ.C :=
      (hO_covBy_OC.eq_or_eq hO_lt_OE.le hOE_le_OC).resolve_left (ne_of_gt hO_lt_OE)
    have hOE_le_OP : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ P := sup_le le_sup_left h
    have hOC_le_OP : Γ.O ⊔ Γ.C ≤ Γ.O ⊔ P := hOE_eq_OC ▸ hOE_le_OP
    have hO_lt_OC : Γ.O < Γ.O ⊔ Γ.C := hO_covBy_OC.lt
    have hO_covBy_OP : Γ.O ⋖ Γ.O ⊔ P := atom_covBy_join Γ.hO hP (Ne.symm hP_ne_O)
    have hOC_eq_OP : Γ.O ⊔ Γ.C = Γ.O ⊔ P :=
      (hO_covBy_OP.eq_or_eq hO_lt_OC.le hOC_le_OP).resolve_left (ne_of_gt hO_lt_OC)
    exact hP_not_OC (le_sup_right.trans hOC_eq_OP.symm.le)
  -- O ∉ P⊔E (lifted; reused in hPE_covBy_π below and step 5 distinctness)
  have hO_not_PE : ¬ Γ.O ≤ P ⊔ Γ.E := by
    intro h
    have hOP_le : Γ.O ⊔ P ≤ P ⊔ Γ.E := sup_le h le_sup_left
    have hP_lt : P < Γ.O ⊔ P := lt_of_le_of_ne le_sup_right
      (fun h' => hP_ne_O ((hP.le_iff.mp (le_sup_left.trans h'.symm.le)).resolve_left
        Γ.hO.1).symm)
    have hPE_eq : P ⊔ Γ.E = Γ.O ⊔ P :=
      (hPE_covBy_P.eq_or_eq hP_lt.le hOP_le).resolve_left (ne_of_gt hP_lt) |>.symm
    exact hE_not_OP (le_sup_right.trans hPE_eq.le)
  -- P⊔E ⋖ π: P, E coplanar in π; line_covBy_plane needs O off P⊔E
  have hPE_covBy_π : P ⊔ Γ.E ⋖ π := by
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
  -- ═══ Step 2a: (P ⊔ P') ⊓ m = E ═══
  -- The load-bearing geometric fact for Steps 2b-5: P, P', E are
  -- collinear on the line P ⊔ E, which meets m at exactly E.
  -- Argument: P off q ⇒ P' ≠ P (P' ≤ q), hence P ⊔ P' = P ⊔ E by
  -- covering on hPE_covBy_P; then (P ⊔ E) ⊓ m = E by modular law
  -- (E ≤ m, P off m so P ⊓ m = ⊥, sup_inf_assoc_of_le).
  have hP'_le_q : P' ≤ q := inf_le_left
  have hP'_le_PE : P' ≤ P ⊔ Γ.E := inf_le_right
  have hP_ne_P' : P ≠ P' := fun h => hP_not_q (h ▸ hP'_le_q)
  have hP_lt_PP' : P < P ⊔ P' := lt_of_le_of_ne le_sup_left
    (fun h => hP_ne_P' ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left
      hP'_atom.1).symm)
  have hPP'_le_PE : P ⊔ P' ≤ P ⊔ Γ.E := sup_le le_sup_left hP'_le_PE
  have hPP'_eq_PE : P ⊔ P' = P ⊔ Γ.E :=
    (hPE_covBy_P.eq_or_eq hP_lt_PP'.le hPP'_le_PE).resolve_left (ne_of_gt hP_lt_PP')
  have hP_inf_m : P ⊓ m = ⊥ :=
    (hP.le_iff.mp inf_le_left).resolve_right (fun h => hP_not_m (h ▸ inf_le_right))
  have hPE_inf_m : (P ⊔ Γ.E) ⊓ m = Γ.E := by
    rw [sup_comm P Γ.E, sup_inf_assoc_of_le P Γ.hE_on_m, hP_inf_m, sup_bot_eq]
  have hPP'_inf_m : (P ⊔ P') ⊓ m = Γ.E := hPP'_eq_PE ▸ hPE_inf_m
  -- ═══ Step 2b: Apply dilation_preserves_direction at (P, P') ═══
  -- Build the P' witness conditions, then derive σP ≠ σP', then DPD.
  set l := Γ.O ⊔ Γ.U with hl_def
  -- q meets l and m at U (used repeatedly to project P' onto axes)
  have hq_inf_l : q ⊓ l = Γ.U := by
    show (Γ.U ⊔ Γ.C) ⊓ (Γ.O ⊔ Γ.U) = Γ.U
    rw [sup_comm Γ.U Γ.C]
    exact line_direction Γ.hC Γ.hC_not_l (le_sup_right : Γ.U ≤ Γ.O ⊔ Γ.U)
  have hq_inf_m : q ⊓ m = Γ.U := by
    show (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have hCm : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [hCm, sup_bot_eq]
  -- ─── P' ≠ U (keystone): U ⊄ P⊔E (else U⊔E line forces P ≤ m). ───
  have hU_ne_P : Γ.U ≠ P := fun h => hP_not_l (h ▸ le_sup_right)
  have hP'_ne_U : P' ≠ Γ.U := by
    intro h_eq
    -- If P' = U then U ≤ P⊔E.
    have hU_le_PE : Γ.U ≤ P ⊔ Γ.E := h_eq ▸ hP'_le_PE
    have hP_lt_PU : P < P ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h => hU_ne_P
        ((hP.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hU.1))
    have hPU_le_PE : P ⊔ Γ.U ≤ P ⊔ Γ.E := sup_le le_sup_left hU_le_PE
    have hPU_eq_PE : P ⊔ Γ.U = P ⊔ Γ.E :=
      (hPE_covBy_P.eq_or_eq hP_lt_PU.le hPU_le_PE).resolve_left (ne_of_gt hP_lt_PU)
    have hPU_inf_m : (P ⊔ Γ.U) ⊓ m = Γ.U :=
      line_direction hP hP_not_m (le_sup_left : Γ.U ≤ m)
    have hE_le_PU : Γ.E ≤ P ⊔ Γ.U := hPU_eq_PE.symm ▸ le_sup_right
    have hE_le_U : Γ.E ≤ Γ.U := hPU_inf_m ▸ le_inf hE_le_PU Γ.hE_on_m
    exact hU_ne_E ((Γ.hU.le_iff.mp hE_le_U).resolve_left Γ.hE_atom.1).symm
  -- ─── P' ≤ π (via P' ≤ q ≤ π) ───
  have hP'_plane : P' ≤ π := hP'_le_q.trans hq_covBy_π.le
  -- ─── P' ∉ m, P' ∉ l (P' ≤ q, q⊓m = U, q⊓l = U; if either, P' = U ✗) ───
  have hP'_not_m : ¬ P' ≤ m := by
    intro h; apply hP'_ne_U
    exact (Γ.hU.le_iff.mp (hq_inf_m ▸ le_inf hP'_le_q h)).resolve_left hP'_atom.1
  have hP'_not_l : ¬ P' ≤ l := by
    intro h; apply hP'_ne_U
    exact (Γ.hU.le_iff.mp (hq_inf_l ▸ le_inf hP'_le_q h)).resolve_left hP'_atom.1
  -- ─── P' ≠ O, P' ≠ I (both are on l, P' off l) ───
  have hP'_ne_O : P' ≠ Γ.O :=
    fun h => hP'_not_l (h ▸ (le_sup_left : Γ.O ≤ l))
  have hP'_ne_I : P' ≠ Γ.I :=
    fun h => hP'_not_l (h ▸ Γ.hI_on)
  -- ─── P' ⊄ O⊔P (P' on P⊔E and P⊔E ⊓ (O⊔P) = P, so P' ≤ P ⇒ P' = P ✗) ───
  have hP'_not_OP : ¬ P' ≤ Γ.O ⊔ P := by
    intro h
    -- (P⊔E) ⊓ (O⊔P) = P via modular_intersection (P, E, O pairwise distinct, O ⊄ P⊔E)
    have hPE_OP_eq_P : (P ⊔ Γ.E) ⊓ (P ⊔ Γ.O) = P :=
      modular_intersection hP Γ.hE_atom Γ.hO hP_ne_E hP_ne_O
        (fun heq => Γ.hO_not_m (heq ▸ Γ.hE_on_m)) hO_not_PE
    have hP'_le_P : P' ≤ P := by
      have := le_inf hP'_le_PE (sup_comm Γ.O P ▸ h : P' ≤ P ⊔ Γ.O)
      rwa [hPE_OP_eq_P] at this
    exact hP_ne_P' ((hP.le_iff.mp hP'_le_P).resolve_left hP'_atom.1).symm
  -- ─── σP ≤ O⊔P, σP' ≤ O⊔P' (definitional from dilation_ext) ───
  have hσP_le_OP : σP ≤ Γ.O ⊔ P :=
    show (Γ.O ⊔ P) ⊓ (c ⊔ (Γ.I ⊔ P) ⊓ m) ≤ Γ.O ⊔ P from inf_le_left
  have hσP'_le_OP' : σP' ≤ Γ.O ⊔ P' :=
    show (Γ.O ⊔ P') ⊓ (c ⊔ (Γ.I ⊔ P') ⊓ m) ≤ Γ.O ⊔ P' from inf_le_left
  -- ─── σP atom, σP' atom (dilation_ext_atom) ───
  have hσP_atom : IsAtom σP := dilation_ext_atom Γ hP hc hc_on hc_ne_O hc_ne_U
    hP_plane hP_not_l hP_ne_O hP_ne_I hP_not_m
  have hσP'_atom : IsAtom σP' := dilation_ext_atom Γ hP'_atom hc hc_on hc_ne_O hc_ne_U
    hP'_plane hP'_not_l hP'_ne_O hP'_ne_I hP'_not_m
  -- ─── σP ⊄ l (σP ≤ O⊔P, (O⊔P)⊓l = O, σP = O ⇒ O ≤ c⊔d_P, (c⊔d_P)⊓l = c, c = O ✗) ───
  have hd_P_atom : IsAtom ((Γ.I ⊔ P) ⊓ m) :=
    line_meets_m_at_atom Γ.hI hP (Ne.symm hP_ne_I)
      (sup_le (Γ.hI_on.trans le_sup_left) hP_plane) Γ.m_covBy_π.le Γ.m_covBy_π Γ.hI_not_m
  have hd_P_ne_U : (Γ.I ⊔ P) ⊓ m ≠ Γ.U := by
    intro h
    -- d_P = U means U ≤ I⊔P, then I⊔U = l ≤ I⊔P (CovBy on I⊔P over I), so P ≤ l ✗
    have hU_le_IP : Γ.U ≤ Γ.I ⊔ P := h ▸ inf_le_left
    have hI_lt : Γ.I < Γ.I ⊔ Γ.U := lt_of_le_of_ne le_sup_left
      (fun h' => Γ.hUI ((Γ.hI.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
        Γ.hU.1).symm.symm)
    have hI_covBy_IP : Γ.I ⋖ Γ.I ⊔ P := atom_covBy_join Γ.hI hP (Ne.symm hP_ne_I)
    have hIU_le_IP : Γ.I ⊔ Γ.U ≤ Γ.I ⊔ P := sup_le le_sup_left hU_le_IP
    have hIU_eq_IP : Γ.I ⊔ Γ.U = Γ.I ⊔ P :=
      (hI_covBy_IP.eq_or_eq hI_lt.le hIU_le_IP).resolve_left (ne_of_gt hI_lt)
    have hP_le_l : P ≤ l :=
      le_sup_right.trans (hIU_eq_IP.symm.le.trans (sup_le Γ.hI_on le_sup_right))
    exact hP_not_l hP_le_l
  have hd_P_not_l : ¬ (Γ.I ⊔ P) ⊓ m ≤ l := by
    intro h
    apply hd_P_ne_U
    have h_meet : (Γ.O ⊔ Γ.U) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := Γ.l_inf_m_eq_U
    exact (Γ.hU.le_iff.mp (h_meet ▸ le_inf h inf_le_right)).resolve_left hd_P_atom.1
  have hσP_not_l : ¬ σP ≤ l := by
    intro h
    -- σP ≤ (O⊔P) ⊓ l = O via line_direction
    have hOP_inf_l : (Γ.O ⊔ P) ⊓ l = Γ.O := by
      rw [sup_comm Γ.O P]
      exact line_direction hP hP_not_l (le_sup_left : Γ.O ≤ l)
    have hσP_le_O : σP ≤ Γ.O := hOP_inf_l ▸ le_inf hσP_le_OP h
    have hσP_eq_O : σP = Γ.O := (Γ.hO.le_iff.mp hσP_le_O).resolve_left hσP_atom.1
    -- σP ≤ c ⊔ d_P (def); σP = O means O ≤ c ⊔ d_P
    have hσP_le_cd : σP ≤ c ⊔ (Γ.I ⊔ P) ⊓ m :=
      show (Γ.O ⊔ P) ⊓ (c ⊔ (Γ.I ⊔ P) ⊓ m) ≤ c ⊔ (Γ.I ⊔ P) ⊓ m from inf_le_right
    have hO_le_cd : Γ.O ≤ c ⊔ (Γ.I ⊔ P) ⊓ m := hσP_eq_O ▸ hσP_le_cd
    -- (c ⊔ d_P) ⊓ l = c via line_direction (sup_comm to put d_P on the left)
    have hcd_inf_l : (c ⊔ (Γ.I ⊔ P) ⊓ m) ⊓ l = c := by
      rw [sup_comm c]
      exact line_direction hd_P_atom hd_P_not_l hc_on
    have hO_le_c : Γ.O ≤ c := hcd_inf_l ▸ le_inf hO_le_cd (le_sup_left : Γ.O ≤ l)
    exact hc_ne_O.symm ((hc.le_iff.mp hO_le_c).resolve_left Γ.hO.1)
  -- ─── σP ≠ σP' via modular_intersection (σP ≤ (O⊔P)⊓(O⊔P') = O ⇒ σP = O, σP ⊄ l) ───
  have hσP_ne_σP' : σP ≠ σP' := by
    intro h_eq
    have hσP_le_OP' : σP ≤ Γ.O ⊔ P' := h_eq ▸ hσP'_le_OP'
    have hOP_OP'_eq : (Γ.O ⊔ P) ⊓ (Γ.O ⊔ P') = Γ.O :=
      modular_intersection Γ.hO hP hP'_atom (Ne.symm hP_ne_O) (Ne.symm hP'_ne_O)
        hP_ne_P' (fun h => hP'_not_OP h)
    have hσP_le_O : σP ≤ Γ.O := hOP_OP'_eq ▸ le_inf hσP_le_OP hσP_le_OP'
    have hσP_eq_O : σP = Γ.O := (Γ.hO.le_iff.mp hσP_le_O).resolve_left hσP_atom.1
    exact hσP_not_l (hσP_eq_O ▸ (le_sup_left : Γ.O ≤ l))
  -- ─── Apply dilation_preserves_direction ───
  have hDPD : (P ⊔ P') ⊓ m = (σP ⊔ σP') ⊓ m :=
    dilation_preserves_direction Γ hP hP'_atom c hc hc_on hc_ne_O hc_ne_U
      hP_plane hP'_plane hP_not_m hP'_not_m hP_not_l hP'_not_l
      hP_ne_O hP'_ne_O hP_ne_P' hP_ne_I hP'_ne_I hσP_ne_σP'
      R hR hR_not h_irred
  -- ═══ Step 3: σP ≤ σP'⊔E ═══
  -- (σP⊔σP')⊓m = E ⇒ E ≤ σP⊔σP'. Then σP'⊔E ≤ σP⊔σP', and σP'⊔E covers σP'
  -- (E ≠ σP' since σP' ⊄ m, E ≤ m); σP⊔σP' covers σP'; so σP'⊔E = σP⊔σP'.
  -- Hence σP ≤ σP⊔σP' = σP'⊔E.
  have hσσ'_inf_m : (σP ⊔ σP') ⊓ m = Γ.E := hDPD ▸ hPP'_inf_m
  have hE_le_σσ' : Γ.E ≤ σP ⊔ σP' := hσσ'_inf_m ▸ inf_le_left
  have hσP'_not_m : ¬ σP' ≤ m := dilation_ext_not_m Γ hP'_atom hc hc_on hc_ne_O hc_ne_U
    hP'_plane hP'_not_m hP'_not_l hP'_ne_O hP'_ne_I hc_ne_I
  have hσP'_ne_E : σP' ≠ Γ.E := fun h => hσP'_not_m (h ▸ Γ.hE_on_m)
  -- σP'⊔E covers σP' (atom_covBy_join)
  have hσP'_covBy_σP'E : σP' ⋖ σP' ⊔ Γ.E :=
    atom_covBy_join hσP'_atom Γ.hE_atom hσP'_ne_E
  -- σP'⊔σP covers σP' (atom_covBy_join)
  have hσP'_covBy_σP'σP : σP' ⋖ σP' ⊔ σP :=
    atom_covBy_join hσP'_atom hσP_atom (Ne.symm hσP_ne_σP')
  -- σP'⊔E ≤ σP'⊔σP (from E ≤ σP⊔σP' = σP'⊔σP)
  have hσP'E_le_σP'σP : σP' ⊔ Γ.E ≤ σP' ⊔ σP := by
    refine sup_le le_sup_left ?_
    exact hE_le_σσ'.trans (sup_comm σP σP' ▸ le_rfl)
  -- σP' < σP'⊔E
  have hσP'_lt_σP'E : σP' < σP' ⊔ Γ.E := lt_of_le_of_ne le_sup_left
    (fun h => hσP'_ne_E
      ((hσP'_atom.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left Γ.hE_atom.1).symm)
  -- σP'⊔E = σP'⊔σP (covering)
  have hσP'E_eq : σP' ⊔ Γ.E = σP' ⊔ σP :=
    (hσP'_covBy_σP'σP.eq_or_eq hσP'_lt_σP'E.le hσP'E_le_σP'σP).resolve_left
      (ne_of_gt hσP'_lt_σP'E)
  -- σP ≤ σP' ⊔ E (rewrite σP ≤ σP'⊔σP via hσP'E_eq)
  have hσP_le_σP'E : σP ≤ σP' ⊔ Γ.E := hσP'E_eq.symm ▸ (le_sup_right : σP ≤ σP' ⊔ σP)
  -- ═══ Step 4: σP ≤ (σP'⊔E) ⊓ (O⊔P) ═══
  have hσP_le_meet : σP ≤ (σP' ⊔ Γ.E) ⊓ (Γ.O ⊔ P) := le_inf hσP_le_σP'E hσP_le_OP
  -- ═══ Step 5: RHS is an atom (two distinct lines: E ∉ O⊔P) ═══
  have hRHS_atom : IsAtom ((σP' ⊔ Γ.E) ⊓ (Γ.O ⊔ P)) :=
    meet_of_lines_is_atom hσP'_atom Γ.hE_atom Γ.hO hP hσP'_ne_E (Ne.symm hP_ne_O)
      (fun h => hE_not_OP (le_sup_right.trans h))
      (fun h => hσP_atom.1 (le_bot_iff.mp (h ▸ hσP_le_meet)))
  -- Atom equality: σP ≤ RHS atom ⇒ σP = RHS
  exact (hRHS_atom.le_iff.mp hσP_le_meet).resolve_left hσP_atom.1

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

/-! ## Bridge composition: σ-composition at a β-image (s138)

The s135 architectural prediction, with `recovery_via_E` now PROVEN
(s137), is that `dilation_compose_at_witness` reduces to a smaller
substantive claim: **σ-composition restricted to β-images** (atoms on
the bridge line `q = U⊔C`). The reduction shape:

  * **LHS via recovery_via_E (P off q):**
      `σ_(x·y)(P) = (σ_(x·y)(P') ⊔ E) ⊓ (O⊔P)`
    where `P' = beta_cast Γ P`.

  * **RHS via the same outer shape, NOT by recovery applied to σ_x(P):**
      `σ_y(σ_x(P)) = (σ_y(σ_x(P')) ⊔ E) ⊓ (O⊔P)`
    derived from the geometric fact that σ_x and σ_y both fix E (E on m,
    dilations fix m pointwise), so they preserve lines through E:
    σ_x maps `P⊔E` to `σ_x(P)⊔E`, then σ_y maps `σ_x(P)⊔E` to
    `σ_y(σ_x(P))⊔E`. Applied to the β-image P' on the input line,
    σ_y(σ_x(P')) lies on `σ_y(σ_x(P))⊔E`. Combined with
    `σ_y(σ_x(P)) ≤ O⊔σ_x(P) = O⊔P` (lines through O preserved by
    dilations), we get σ_y(σ_x(P)) at the two-line meet.

Both expressions share the `(O⊔P)` factor. Equality reduces to:

      `σ_(x·y)(P') ⊔ E = σ_y(σ_x(P')) ⊔ E`

— a line-equality statement about how σ composes on β-images. The
stronger **atom equality**

      `σ_(x·y)(P') = σ_y(σ_x(P'))`

is the form stated below and is sufficient (line equality follows).

### Why this is now the substantive remaining content

The s137 open question framing — "does `dilation_witness_preservation`
need extending with `¬ σ_x(P) ≤ q`?" — was asking about a *different*
proof shape (apply recovery_via_E to σ_x(P) on RHS, requiring σ_x(P)
off q). That shape is structurally blocked: σ_x does NOT preserve
off-q in general — there is a single critical x*(P) for which σ_x(P)
lands on q, so no unconditional preservation extension is available.

The recovery-once + geometric-collinearity-through-E shape above
sidesteps this entirely. It needs only P off q on the LHS;
the RHS uses σ_y's preservation of lines through E (a property already
implicit in `dilation_preserves_direction`, since E is on the axis m).

### Device-shape question (s132, now localized)

`dilation_mul_key_identity` (PROVEN) gives:

      `σ_c(β(a)) = (σ_c(C) ⊔ U) ⊓ (a·c ⊔ E)`

The output lies on the line `σ_c(C) ⊔ U` through U — for c ≠ I, this is
*not* q. So the β-line is **not closed under σ_c**; one application of
σ_c moves a β-image onto a "shifted" line through U. To compute σ_y of
that shifted-line atom and equate with one σ_(x·y) application
directly via key identity, two routes:

  * **(α) shifted key identity.** Prove a generalization of
    `dilation_mul_key_identity` for inputs on `σ_c(C) ⊔ U` (the
    σ_c-shifted bridge line), arbitrary non-degenerate c, not just q.
    A new typed lemma in the same complexity-class as the original key
    identity, following a known shape.

  * **(β) re-bridging.** Apply `recovery_via_E` to `σ_x(P')` (which is
    off-q for non-degenerate x, by key identity's output structure),
    yielding
      `σ_y(σ_x(P')) = (σ_y(beta_cast(σ_x(P'))) ⊔ E) ⊓ (O ⊔ σ_x(P'))`.
    The inner `beta_cast` projects back to q where
    `dilation_mul_key_identity` applies directly. Two bridge traversals
    composed; no new key-identity needed.

Both routes are workable in principle. (β) is more compositional and
reuses proven infrastructure (`recovery_via_E` + `dilation_mul_key_identity`,
both PROVEN); (α) is more direct.

**Test of the (β) prediction (s142):** the s133/s134/s139 prediction —
"(β) lands without surfacing a third `*Witness` interface" — was tested
by carrying (β) through Steps 1–4 of `dilation_compose_at_beta` and
inspecting the closing equality at Step 5+. **The prediction is
falsified.**

Take ⊔E of both sides of `σ_y(σ_x(β(a))) = σ_(x·y)(β(a))`:

  * LHS = σ_y(σ_x(β(a))). By `h_inner_unfold`, σ_x(β(a)) ≤ a·x ⊔ E,
    so after `recovery_via_E` and atom-cover at E,
    σ_y(σ_x(β(a))) ⊔ E = (a·x)·y ⊔ E.
  * RHS = σ_(x·y)(β(a)). By `dilation_mul_key_identity`,
    σ_(x·y)(β(a)) ≤ a·(x·y) ⊔ E, so RHS ⊔ E = a·(x·y) ⊔ E.

If LHS = RHS as atoms, then (a·x)·y ⊔ E = a·(x·y) ⊔ E, hence by
atom-cover (both atoms ≠ E, on l) **`(a·x)·y = a·(x·y)`** — i.e.,
`coord_mul_assoc` applied to atoms `a, x, y`.

So `dilation_compose_at_beta` *contains* `coord_mul_assoc-at-atoms` as
a logical consequence of its atom equality. The s134 architecture is
therefore **circular through Lean's dependency graph**:

      coord_mul_assoc
        ←  dilation_compose_at_witness (×4)
        ←  dilation_compose_at_beta
        ⟹  coord_mul_assoc-at-atoms

This is not "(β) is harder than thought" — it is "(β) cannot close on
its own infrastructure." The closure expresses the same content the
chain was trying to derive (loop-as-content shape).

**Three exits, none yet walked:**

  * **(A) Architecture inversion via dimensional lift (bin-1).** Prove
    `coord_mul_assoc` directly via a Desargues argument that uses the
    `R` witness (the height-≥-4 atom off π, already threaded through
    the lemma signatures) to lift the planar associativity question
    into 3-space. The lift exists by the height-≥-4 axiom; residents
    on the higher substrate do the proof work that the planar level
    cannot close on itself (the s142 loop showed that the planar-only
    attempt is circular). The s134 thin-assembly via
    `dilation_compose_at_witness` then becomes downstream of
    `coord_mul_assoc`, not its proof. **Bundling shape:** HalfType
    template (`lean/Foam/HalfType.lean`) — construct
    `DimLifted_MulAssoc Γ` (or similar) that bundles R with the
    lift's projection content, so the structure's inhabitation IS the
    theorem.

  * **(B) Named Witness (bin-2).** Surface `MulComposeWitness Γ` (or
    `AssociativityWitness Γ`) as a typed observer commitment,
    parameterizing `dilation_compose_at_beta` (and `coord_mul_assoc`
    downstream). Same shape as `DesarguesianWitness Γ` for left-distrib.
    Note: see `lean/CLAUDE.md`'s "Meta-frontier: bin-2 Witnesses as
    exhaustion findings" — bin-2 commitments in this project have been
    found to be exhaustion-based, not irreducibility-proven, and admit
    bin-1 bundlings in principle.

  * **(C) Fresh Desargues at this level (bin-1).** Find a triangle
    setup that proves `σ_y(σ_x(β(a))) = σ_(x·y)(β(a))` directly via a
    single Desargues call (not routing through `coord_mul_assoc`). New
    geometric argument; the (α) shifted-key-identity route above may
    be the cleanest version.

The s132 device-shape question is now sharp: which exit closes the
multiplicative branch?
-/

/-- **σ-composition at a β-image: dilations compose on the bridge line.**

    For atoms `x, y, a` on `l` non-degenerate, applying σ_y ∘ σ_x and
    σ_(x·y) to the β-image `β(a) = (U⊔C) ⊓ (a⊔E)` give the same atom:

        `σ_y(σ_x(β(a))) = σ_(x·y)(β(a))`

    This is the substantive remaining content of
    `dilation_compose_at_witness` after the `recovery_via_E` bridge
    reduction (see section docstring above). A witness P in the larger
    theorem reduces to its β-cast P'; P' is a β-image; the off-q
    witness's σ-composition follows once σ-composition is established
    here on β-images.

    See section docstring for the (α) shifted-key-identity and (β)
    re-bridging routes. -/
theorem dilation_compose_at_beta (Γ : CoordSystem L)
    (x y a : L) (hx : IsAtom x) (hy : IsAtom y) (ha : IsAtom a)
    (hx_on : x ≤ Γ.O ⊔ Γ.U) (hy_on : y ≤ Γ.O ⊔ Γ.U) (ha_on : a ≤ Γ.O ⊔ Γ.U)
    (hx_ne_O : x ≠ Γ.O) (hy_ne_O : y ≠ Γ.O) (ha_ne_O : a ≠ Γ.O)
    (hx_ne_U : x ≠ Γ.U) (hy_ne_U : y ≠ Γ.U) (ha_ne_U : a ≠ Γ.U)
    (hx_ne_I : x ≠ Γ.I) (hy_ne_I : y ≠ Γ.I)
    -- Non-degeneracy of the product (paralleling `coord_mul_assoc`).
    (hxy_ne_O : coord_mul Γ x y ≠ Γ.O) (hxy_ne_U : coord_mul Γ x y ≠ Γ.U)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    dilation_ext Γ y (dilation_ext Γ x ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E))) =
      dilation_ext Γ (coord_mul Γ x y) ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) := by
  -- Non-degeneracy of x·y as an atom on l (the ne_O/ne_U pieces are hypotheses;
  -- the atomicity + on-l facts follow from `coord_mul_atom`).
  have hxy_atom : IsAtom (coord_mul Γ x y) :=
    coord_mul_atom Γ x y hx hy hx_on hy_on hx_ne_O hy_ne_O hx_ne_U hy_ne_U
  have hxy_on : coord_mul Γ x y ≤ Γ.O ⊔ Γ.U := by
    show coord_mul Γ x y ≤ Γ.O ⊔ Γ.U; exact inf_le_right
  -- ═══ Step 1: apply `dilation_mul_key_identity` to the RHS (c = x·y) ═══
  -- σ_(x·y)(β(a)) = (σ_(x·y)(C) ⊔ U) ⊓ (a·(x·y) ⊔ E)
  have h_RHS_unfold :
      dilation_ext Γ (coord_mul Γ x y) ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) =
        (dilation_ext Γ (coord_mul Γ x y) Γ.C ⊔ Γ.U) ⊓
          (coord_mul Γ a (coord_mul Γ x y) ⊔ Γ.E) :=
    dilation_mul_key_identity Γ a (coord_mul Γ x y) ha hxy_atom
      ha_on hxy_on ha_ne_O hxy_ne_O ha_ne_U hxy_ne_U R hR hR_not h_irred
  -- ═══ Step 2: apply `dilation_mul_key_identity` to σ_x(β(a)) (inner of LHS) ═══
  -- σ_x(β(a)) = (σ_x(C) ⊔ U) ⊓ (a·x ⊔ E)
  have h_inner_unfold :
      dilation_ext Γ x ((Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E)) =
        (dilation_ext Γ x Γ.C ⊔ Γ.U) ⊓ (coord_mul Γ a x ⊔ Γ.E) :=
    dilation_mul_key_identity Γ a x ha hx ha_on hx_on ha_ne_O hx_ne_O ha_ne_U hx_ne_U
      R hR hR_not h_irred
  -- ═══ Step 3: prepare witness conditions on Q for recovery_via_E ═══
  -- Six of the seven conditions on Q := σ_x(β(a)) discharge via
  -- `dilation_witness_preservation` applied at x, P := β(a). β(a)'s
  -- own witness conditions: `beta_atom`/`beta_plane`/`beta_not_l` are
  -- PROVEN imports; we derive `⊄ m`, `⊄ O⊔C`, `≠ I`, `≠ O` inline.
  -- The seventh, `¬ Q ≤ q`, is genuinely new and PROVEN (s141) via the
  -- key identity's output structure: Q ≤ σ_x(C)⊔U; σ_x(C) ⊄ q (from
  -- σ_x(C) ≤ O⊔C, (O⊔C)⊓q = C, and σ_x(C) ≠ C); so the two lines
  -- σ_x(C)⊔U and q are distinct lines through U, meeting at U; Q ≤ q
  -- would force Q ≤ U ≤ m, contradicting Q ⊄ m. No extra hypothesis
  -- needed beyond hx_ne_I (already in the signature).
  --
  -- TODO (s139+): extract `beta_not_m` and `beta_not_OC` as named
  -- theorems in FTPGMulKeyIdentity for reuse — the derivations below
  -- inline the existing argument at MulKeyIdentity:233-240 (hCa_not_m)
  -- and a modular_intersection-at-E variant for `⊄ O⊔C` (cleaner than
  -- the longer `hCa_ne_C → not_OC` route at MulKeyIdentity:245-289).
  set βa := (Γ.U ⊔ Γ.C) ⊓ (a ⊔ Γ.E) with hβa_def
  -- ─── β(a) atom/plane/not_l from named lemmas ───
  have hβa_atom : IsAtom βa := beta_atom Γ ha ha_on ha_ne_O ha_ne_U
  have hβa_plane : βa ≤ Γ.O ⊔ Γ.U ⊔ Γ.V := beta_plane Γ ha_on
  have hβa_not_l : ¬ βa ≤ Γ.O ⊔ Γ.U := beta_not_l Γ ha ha_on ha_ne_O ha_ne_U
  -- ─── ≠ O / ≠ I / ≠ U from `⊄ l` ───
  have hβa_ne_O : βa ≠ Γ.O := fun h => hβa_not_l (h ▸ le_sup_left)
  have hβa_ne_I : βa ≠ Γ.I := fun h => hβa_not_l (h ▸ Γ.hI_on)
  have hβa_ne_U : βa ≠ Γ.U := fun h => hβa_not_l (h ▸ le_sup_right)
  -- ─── Shared infrastructure for ⊄ m and ⊄ O⊔C ───
  have hβa_le_q : βa ≤ Γ.U ⊔ Γ.C := inf_le_left
  have hβa_le_aE : βa ≤ a ⊔ Γ.E := inf_le_right
  have ha_not_m : ¬ a ≤ Γ.U ⊔ Γ.V :=
    fun h => ha_ne_U (Γ.atom_on_both_eq_U ha ha_on h)
  have ha_ne_E : a ≠ Γ.E := fun h => ha_not_m (h ▸ Γ.hE_on_m)
  have hqm_eq_U : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V) = Γ.U := by
    rw [sup_inf_assoc_of_le Γ.C (le_sup_left : Γ.U ≤ Γ.U ⊔ Γ.V)]
    have hCm : Γ.C ⊓ (Γ.U ⊔ Γ.V) = ⊥ :=
      (Γ.hC.le_iff.mp inf_le_left).resolve_right (fun h => Γ.hC_not_m (h ▸ inf_le_right))
    rw [hCm, sup_bot_eq]
  -- Reusable: β(a) = E ⇒ ✗ (since E ≤ q would force E ≤ q⊓m = U, but E ≠ U).
  have hβa_ne_E : βa ≠ Γ.E := by
    intro h
    have hE_le_q : Γ.E ≤ Γ.U ⊔ Γ.C := h ▸ hβa_le_q
    exact Γ.hEU ((Γ.hU.le_iff.mp (le_inf hE_le_q Γ.hE_on_m |>.trans hqm_eq_U.le))
      |>.resolve_left Γ.hE_atom.1)
  -- ─── β(a) ⊄ m: β(a) ≤ a⊔E and ≤ m ⇒ β(a) ≤ (a⊔E)⊓m = E ⇒ β(a) = E ✗ ───
  have hβa_not_m : ¬ βa ≤ Γ.U ⊔ Γ.V := by
    intro h
    apply hβa_ne_E
    exact (Γ.hE_atom.le_iff.mp (le_inf hβa_le_aE h |>.trans
      (line_direction ha ha_not_m Γ.hE_on_m).le)).resolve_left hβa_atom.1
  -- ─── β(a) ⊄ O⊔C: β(a) ≤ a⊔E and ≤ O⊔C ⇒ β(a) ≤ (a⊔E)⊓(O⊔C) = E
  --     (modular_intersection at E with O⊔E = O⊔C). Then β(a) = E ✗.
  have hO_ne_E : Γ.O ≠ Γ.E := fun h => Γ.hO_not_m (h ▸ Γ.hE_on_m)
  have hOC_ne : Γ.O ≠ Γ.C := fun h => Γ.hC_not_l (h ▸ le_sup_left)
  have hO_not_aE : ¬ Γ.O ≤ a ⊔ Γ.E := by
    intro hO_le
    have hO_lt_Oa : Γ.O < Γ.O ⊔ a := lt_of_le_of_ne le_sup_left
      (fun h => ha_ne_O ((Γ.hO.le_iff.mp (le_sup_right.trans h.symm.le)).resolve_left ha.1))
    have hOa_eq_l : Γ.O ⊔ a = Γ.O ⊔ Γ.U :=
      ((atom_covBy_join Γ.hO Γ.hU Γ.hOU).eq_or_eq hO_lt_Oa.le
        (sup_le le_sup_left ha_on)).resolve_left (ne_of_gt hO_lt_Oa)
    have hl_le : Γ.O ⊔ Γ.U ≤ a ⊔ Γ.E := hOa_eq_l ▸ sup_le hO_le le_sup_left
    have ha_lt_l : a < Γ.O ⊔ Γ.U :=
      (line_covers_its_atoms Γ.hO Γ.hU Γ.hOU ha ha_on).lt
    exact Γ.hE_not_l (le_sup_right.trans
      (((atom_covBy_join ha Γ.hE_atom ha_ne_E).eq_or_eq ha_on hl_le).resolve_left
        (ne_of_gt ha_lt_l)).symm.le)
  have hβa_not_OC : ¬ βa ≤ Γ.O ⊔ Γ.C := by
    intro h
    -- O⊔E = O⊔C (E ≠ O, E ≤ O⊔C, covering O ⋖ O⊔C)
    have hO_lt_OE : Γ.O < Γ.O ⊔ Γ.E := lt_of_le_of_ne le_sup_left
      (fun h' => hO_ne_E ((Γ.hO.le_iff.mp (le_sup_right.trans h'.symm.le)).resolve_left
        Γ.hE_atom.1).symm)
    have hOE_le_OC : Γ.O ⊔ Γ.E ≤ Γ.O ⊔ Γ.C := sup_le le_sup_left CoordSystem.hE_le_OC
    have hO_covBy_OC : Γ.O ⋖ Γ.O ⊔ Γ.C := atom_covBy_join Γ.hO Γ.hC hOC_ne
    have hOE_eq_OC : Γ.O ⊔ Γ.E = Γ.O ⊔ Γ.C :=
      (hO_covBy_OC.eq_or_eq hO_lt_OE.le hOE_le_OC).resolve_left (ne_of_gt hO_lt_OE)
    -- (E⊔a) ⊓ (E⊔O) = E
    have hmod : (Γ.E ⊔ a) ⊓ (Γ.E ⊔ Γ.O) = Γ.E :=
      modular_intersection Γ.hE_atom ha Γ.hO ha_ne_E.symm hO_ne_E.symm ha_ne_O
        (show ¬ Γ.O ≤ Γ.E ⊔ a from sup_comm a Γ.E ▸ hO_not_aE)
    -- β(a) ≤ (E⊔a) ⊓ (E⊔O)
    have hβa_le_meet : βa ≤ (Γ.E ⊔ a) ⊓ (Γ.E ⊔ Γ.O) := by
      refine le_inf ?_ ?_
      · exact sup_comm a Γ.E ▸ hβa_le_aE
      · have hβa_le_OE : βa ≤ Γ.O ⊔ Γ.E := h.trans hOE_eq_OC.symm.le
        exact sup_comm Γ.O Γ.E ▸ hβa_le_OE
    apply hβa_ne_E
    exact (Γ.hE_atom.le_iff.mp (hβa_le_meet.trans hmod.le)).resolve_left hβa_atom.1
  -- ─── Apply `dilation_witness_preservation` at x, P := β(a) ───
  -- Apply dilation_witness_preservation (relocated above this section) at x, P := β(a)
  -- to discharge 6 of the 7 sub-witness conditions on Q := σ_x(β(a)).
  set Q := dilation_ext Γ x βa with hQ_def
  obtain ⟨hQ_atom, hQ_plane, hQ_not_l, hQ_not_m, hQ_not_OC, hQ_ne_I⟩ :=
    dilation_witness_preservation Γ x hx hx_on hx_ne_O hx_ne_U hx_ne_I
      hβa_atom hβa_plane hβa_not_l hβa_not_m hβa_not_OC hβa_ne_I hβa_ne_O
  -- Seventh condition (genuinely new): `¬ Q ≤ q`.
  -- Proof via the key identity's output structure:
  --   Q = σ_x(β(a)) = (σ_x(C) ⊔ U) ⊓ (a·x ⊔ E)   [h_inner_unfold]
  -- so Q ≤ σ_x(C) ⊔ U. Combined with σ_x(C) ⊄ q (via σ_x(C) ≤ O⊔C,
  -- (O⊔C)⊓q = C, and σ_x(C) ≠ C from `dilation_ext_ne_P`), the two
  -- lines σ_x(C)⊔U and q are distinct lines through U, meeting at U.
  -- Then Q ≤ q would force Q ≤ U ≤ m, contradicting hQ_not_m.
  have hQ_not_q : ¬ Q ≤ Γ.U ⊔ Γ.C := by
    intro hQ_le_q
    -- σ_x(C) = (O⊔C) ⊓ (x ⊔ E_I); in particular σ_x(C) ≤ O⊔C.
    set σxC := dilation_ext Γ x Γ.C with hσxC_def
    have hσxC_eq : σxC = (Γ.O ⊔ Γ.C) ⊓ (x ⊔ Γ.E_I) :=
      dilation_ext_C Γ x hx hx_on hx_ne_O hx_ne_U
    have hσxC_le_OC : σxC ≤ Γ.O ⊔ Γ.C := hσxC_eq ▸ inf_le_left
    -- σ_x(C) ≠ C via `dilation_ext_ne_P` at P := C (x ≠ I).
    have hC_ne_I : Γ.C ≠ Γ.I := fun h => Γ.hC_not_l (h ▸ Γ.hI_on)
    have hσxC_ne_C : σxC ≠ Γ.C :=
      dilation_ext_ne_P Γ Γ.hC hx hx_on hx_ne_O hx_ne_U
        Γ.hC_plane Γ.hC_not_m Γ.hC_not_l hOC_ne.symm hC_ne_I hx_ne_I
    -- Standard fact (derived inline): ¬ U ≤ O⊔C.
    -- If U ≤ O⊔C, then U ≤ (O⊔U)⊓(O⊔C) = O (modular at O, U ≠ C, C ⊄ O⊔U).
    have hU_not_OC : ¬ Γ.U ≤ Γ.O ⊔ Γ.C := by
      intro hU_le
      have hC_ne_U : Γ.C ≠ Γ.U := fun h => Γ.hC_not_l (h ▸ le_sup_right)
      have hOU_OC_eq_O : (Γ.O ⊔ Γ.U) ⊓ (Γ.O ⊔ Γ.C) = Γ.O :=
        modular_intersection Γ.hO Γ.hU Γ.hC Γ.hOU hOC_ne hC_ne_U.symm Γ.hC_not_l
      have hU_le_O : Γ.U ≤ Γ.O := hOU_OC_eq_O ▸ le_inf le_sup_right hU_le
      exact Γ.hOU ((Γ.hO.le_iff.mp hU_le_O).resolve_left Γ.hU.1).symm
    -- σ_x(C) ⊄ q: σ_x(C) ≤ q and ≤ O⊔C gives σ_x(C) ≤ (O⊔C)⊓q = C ✗.
    have hC_ne_U : Γ.C ≠ Γ.U := fun h => Γ.hC_not_l (h ▸ le_sup_right)
    have hOC_q_eq_C : (Γ.C ⊔ Γ.O) ⊓ (Γ.C ⊔ Γ.U) = Γ.C :=
      modular_intersection Γ.hC Γ.hO Γ.hU hOC_ne.symm hC_ne_U Γ.hOU
        (fun h => hU_not_OC (h.trans (sup_comm Γ.C Γ.O).le))
    -- σ_x(C) is an atom (named lemma: `dilation_ext_atom` at C).
    have hσxC_atom : IsAtom σxC :=
      dilation_ext_atom Γ Γ.hC hx hx_on hx_ne_O hx_ne_U
        Γ.hC_plane Γ.hC_not_l hOC_ne.symm hC_ne_I Γ.hC_not_m
    have hσxC_not_q : ¬ σxC ≤ Γ.U ⊔ Γ.C := by
      intro h
      apply hσxC_ne_C
      have hσxC_le_meet : σxC ≤ (Γ.C ⊔ Γ.O) ⊓ (Γ.C ⊔ Γ.U) :=
        le_inf (sup_comm Γ.O Γ.C ▸ hσxC_le_OC) (sup_comm Γ.U Γ.C ▸ h)
      exact (Γ.hC.le_iff.mp (hσxC_le_meet.trans hOC_q_eq_C.le)).resolve_left hσxC_atom.1
    -- (U ⊔ C) ⊓ (U ⊔ σ_x(C)) = U (two distinct lines through U).
    have hσxC_ne_U : σxC ≠ Γ.U := by
      intro h
      apply hU_not_OC
      exact h ▸ hσxC_le_OC
    have hmeetU : (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ σxC) = Γ.U :=
      modular_intersection Γ.hU Γ.hC hσxC_atom hC_ne_U.symm hσxC_ne_U.symm
        hσxC_ne_C.symm hσxC_not_q
    -- Q ≤ σ_x(C) ⊔ U (factor of the key identity output).
    have hQ_le_σxCU : Q ≤ σxC ⊔ Γ.U :=
      h_inner_unfold.le.trans inf_le_left
    -- Q ≤ U via the meet at U.
    have hQ_le_U : Q ≤ Γ.U := by
      have hQ_le : Q ≤ (Γ.U ⊔ Γ.C) ⊓ (Γ.U ⊔ σxC) :=
        le_inf hQ_le_q (sup_comm σxC Γ.U ▸ hQ_le_σxCU)
      exact hQ_le.trans hmeetU.le
    -- Q ≤ U ≤ m contradicts Q ⊄ m.
    exact hQ_not_m (hQ_le_U.trans le_sup_left)
  -- ═══ Step 4: apply `recovery_via_E` to σ_y(Q) ═══
  have h_recovery : dilation_ext Γ y Q =
      (dilation_ext Γ y (beta_cast Γ Q) ⊔ Γ.E) ⊓ (Γ.O ⊔ Q) :=
    recovery_via_E Γ y hy hy_on hy_ne_O hy_ne_U hy_ne_I
      hQ_atom hQ_plane hQ_not_l hQ_not_m hQ_not_OC hQ_not_q hQ_ne_I
      R hR hR_not h_irred
  -- ═══ Step 5+ (open): close via `dilation_mul_key_identity` on σ_y(β(b)) ═══
  -- `beta_cast Γ Q = (U⊔C) ⊓ (Q⊔E)`. Since Q⊔E = b⊔E for b := (Q⊔E)⊓l
  -- (both lines pass through E and through b; lines in π through two
  -- distinct atoms are unique), `beta_cast Γ Q = β(b)`. So
  --   σ_y(beta_cast Γ Q) = σ_y(β(b)) = (σ_y(C) ⊔ U) ⊓ (b·y ⊔ E)
  -- via `dilation_mul_key_identity`. Substituting into `h_recovery`:
  --   σ_y(Q) = (((σ_y(C) ⊔ U) ⊓ (b·y ⊔ E)) ⊔ E) ⊓ (O⊔Q).
  -- The closing modular argument equates this with `h_RHS_unfold`'s form:
  --   (σ_(x·y)(C) ⊔ U) ⊓ (a·(x·y) ⊔ E).
  -- s142 finding: `b = a·x` is forced (from Q ≤ a·x ⊔ E via
  -- `h_inner_unfold`, giving Q⊔E = a·x ⊔ E, so b := (Q⊔E)⊓l = a·x).
  -- Therefore the closing equality requires
  --   `b·y = (a·x)·y = a·(x·y)`  —  `coord_mul_assoc` at atoms.
  -- The s134 architecture loops through this content:
  --   coord_mul_assoc ← dilation_compose_at_witness ← dilation_compose_at_beta
  --   ⟹ coord_mul_assoc-at-atoms.
  -- Step 5+ cannot close on its own infrastructure. See section docstring
  -- above the theorem for the falsification of the s139 (β) prediction
  -- and the three exits (A inversion / B Witness / C fresh Desargues).
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

    ## Proof architecture (s138, post-recovery_via_E)

    The s134 docstring's Desargues setup (triangles `(P, σ_x(P),
    σ_y(σ_x(P)))` and `(I, x, x·y)`, center O) **fails as a triangle
    setup** — T1's three vertices all lie on the single line O⊔P
    (dilations with center O preserve lines through O). s135 replaced
    that with a bridge-identity factoring through `q = U⊔C`; s137 made
    that viable by proving `recovery_via_E`. The capstone reduction:

    **Case split on P ≤ q vs P ⊄ q.**

    * **(P ⊄ q):**
      - LHS: `σ_(x·y)(P) = (σ_(x·y)(P')⊔E) ⊓ (O⊔P)` via `recovery_via_E`.
      - RHS: `σ_y(σ_x(P)) = (σ_y(σ_x(P'))⊔E) ⊓ (O⊔P)` via the
        geometric fact that σ_x and σ_y fix E, hence preserve lines
        through E, hence map the β-image P' through to where it lands
        collinear with the dilation outputs via E.
      - Both share `(O⊔P)`; equality reduces to
        `σ_(x·y)(P')⊔E = σ_y(σ_x(P'))⊔E`, which follows from atom
        equality `σ_(x·y)(P') = σ_y(σ_x(P'))` — i.e.,
        `dilation_compose_at_beta`.

    * **(P ≤ q):** P is itself a β-image, P = β(a) for a determined by
      P. The claim becomes `σ_y(σ_x(β(a))) = σ_(x·y)(β(a))` —
      `dilation_compose_at_beta` applied directly.

    Either branch lands once `dilation_compose_at_beta` (above) lands.

    See the section docstring above `dilation_compose_at_beta` for the
    (α) shifted-key-identity vs (β) re-bridging routes to that lemma,
    and for why the alternative "extend `dilation_witness_preservation`
    with `¬ σ_x(P) ≤ q`" route is structurally blocked.

    **Witness-detection point (s132 device-shape conjecture):**
    concentrated in `dilation_compose_at_beta`, not here. The prediction
    is that route (β) — `recovery_via_E` + `dilation_mul_key_identity`,
    both PROVEN — composes to discharge `dilation_compose_at_beta`
    without a fresh `*Witness` interface. Untested. -/
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
