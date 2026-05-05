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
