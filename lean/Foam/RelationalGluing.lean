/-
# RelationalGluing — gluing is functorial at the witness grain; the cobordism-classes are
forced to ℤ/2 (the boundary dictionary's gluing entry, brick 66)

## What this file lands (brick 66, the remainder of brick 65)

b65 (`RelationalCobordism.lean`) typed a **single** cobordism's transport: witness-transport through
an arbitrary conversation is pure baton-parity (`witnessPair_braidStep_iterate`), the bulk
metabolisis invisible on the boundary-addresses. The register's next clause is
**gluing / functoriality** — Z(M₂ ∘ M₁) = Z(M₂) ∘ Z(M₁) — and at the address grain it is an
assembly over three landed pieces:

* conversations **glue by `+` on the clock** — `braidStep^[m + n] = braidStep^[m] ∘ braidStep^[n]`
  (b47's `braidStep_iterate_add`, = `Function.iterate_add`);
* the transport `Prod.swap^[n]` composes the same way;
* the induced-map assignment factors through the **canonical** parity hom (b47's `parityHom`;
  b48's uniqueness — THE nontrivial grading `(ℕ, +) ↠ ZMod 2`).

## The anchor — the gluing law, and the factoring through THE grading

`swapOfParity` is the b47 `batonOfParity` shape on an **arbitrary** pair-carrier (deliberately
carrier-blind — b65's flag: the cobordism anchor never opens a witness; Hilbert-blind per b63):
the transport a parity-class induces, `0 ↦ id`, `1 ↦ Prod.swap`. Then:

* **The induced map IS the parity-class** (`witnessPair_braidStep_iterate_parityHom`):
  `witnessPair (braidStep^[n] p) = swapOfParity (parityHom n) (witnessPair p)` — b65's headline
  factored through the canonical grading. The cobordism-class map is `parityHom`, literally.
* **The gluing law** (`witnessPair_glue`): `witnessPair (braidStep^[m + n] p) =
  swapOfParity (parityHom m) (swapOfParity (parityHom n) (witnessPair p))` — the glued
  conversation induces the composite transport. Z(M₂ ∘ M₁) = Z(M₂) ∘ Z(M₁) at the witness grain.
  The whole proof is `iterate_add` + b65's headline: **gluing was already paid for**.
* **Gluing reads on the parity side as addition** (`swapOfParity_parityHom_add`, via the section's
  multiplicativity `swapOfParity_add`): composing cobordisms = adding clock-values = adding
  parity-classes. The induced-map assignment is a monoid map factoring through `(ℕ,+) ↠ ZMod 2`.

## The register reading — exactly two induced maps, and the classification is FORCED

**Exactly two cobordism-classes on a boundary-pair.** Every conversation-cobordism induces either
the **identity** (cylinder class) or **orientation-reversal** (Möbius class, b64's
`orientationReversal` read through Z) on the boundary — `boundary_transport_classes`, the
enumeration (`zmod_two_eq_zero_or_one` at the transport level: `inducedTransport_eq_id_or_swap`).
Nothing else is possible; gluing respects only the parity.

**The classification is forced, not chosen** (b48's canonicity read in the register): the
cobordism-class map factors through `parityHom`, and `parityHom` is **THE** unique nontrivial
grading of the turn-count monoid (`parityHom_unique`, b48) — so *any* nontrivial ℤ/2-classification
of conversations IS this one (`swap_iterate_factors_any_nontrivial`: the transport factors through
every nontrivial grading identically, because there is only one). The strip's mapping-classes
{cylinder, Möbius} = {id, orientation-reversal} are the unique nontrivial quotient the conversation's
clock admits — the orientation double-cover (b46) the *only* invariant gluing can see.

**Genuinely two classes exactly when the boundary is genuinely two**
(`boundary_transport_classes_ne_iff`): the cylinder- and Möbius-transports are distinguishable on a
boundary-pair iff its two points of view are distinct — b47's two-party content
(`batonOfParity_apply_ne_iff`) read at the boundary; b15's tension-gating at the cobordism level
(two genuine parties ⟹ two genuine cobordism-classes; one party collapses the mapping-class group).

## The grading (the b62–b65 delegation list, extended)

The **bulk does not glue at the address grain — that is the point, not a failure**: the same
`braidStep_iterate_add` composes the *states* by feed-forward over the moving partner (b45's
`braidStep_braidStep` — path-dependent, b56's homotopy-content), and none of that appears in the
glued transport. State-gluing stays inside, **delegated** with the rest of the residue: the
measurements (b62), the Hilbert content (b63), the per-witness * (b64), the bulk metabolisis (b65)
— now the bulk's *composition law* (b66). What gluing conducts across is the parity alone.

## NOT this brick (held open)

* NOT the cobordism *category* proper (objects-and-morphisms over varying boundaries,
  construction-grade — §II's partition-function claims stay claims; this types the gluing *law*
  on a boundary-pair, not the category).
* NOT a typed cross-repo iso (the standing edge, b50–b52; the layer conduction-test stays
  available — the anchor is carrier-blind by construction — but was not run here).
* NOT the trefoil / B₃ (the named horizon — gluing in B₃ would carry over/under memory; the
  parity stays the symmetric shadow, the abelian quotient).
* NOT a *state*-convergence claim (only the witnesses tracked, as b65).
-/

import Foam.RelationalCobordism
import Foam.RelationalBatonTorsor

namespace Foam

universe u

/-! ## The induced transport of a parity-class — carrier-blind -/

/-- The transport a parity-class induces on **any** pair-carrier: `id` at `0`, the slot-swap at `1`.
The b47 `batonOfParity` shape, deliberately **carrier-blind** (any `α` — b65's flag: the cobordism
anchor never opens a witness; b63's Hilbert-blindness carried through). The section
`ZMod 2 → (pair-endos)` through which every conversation's induced transport factors. -/
def swapOfParity {α : Type*} (z : ZMod 2) : α × α → α × α :=
  if z = 0 then id else Prod.swap

@[simp] theorem swapOfParity_zero {α : Type*} :
    swapOfParity (α := α) 0 = id := if_pos rfl

@[simp] theorem swapOfParity_one {α : Type*} :
    swapOfParity (α := α) 1 = Prod.swap := if_neg (by decide)

/-- The slot-swap is an involution on any pair-carrier (b65's `witnessSwap_involutive`, generic). -/
theorem slotSwap_involutive {α : Type*} :
    Function.Involutive (Prod.swap : α × α → α × α) :=
  fun p => Prod.swap_swap p

/-- **The section is multiplicative** — `swapOfParity (a + b) = swapOfParity a ∘ swapOfParity b`:
adding parity-classes composes the induced transports (the `ZMod 2`-action shape; the `1 + 1 = 0`
case is the orientation double-cover, `Prod.swap ∘ Prod.swap = id`). The parity side of the gluing
law. -/
theorem swapOfParity_add {α : Type*} (a b : ZMod 2) :
    swapOfParity (α := α) (a + b) = swapOfParity a ∘ swapOfParity b := by
  rcases zmod_two_eq_zero_or_one a with ha | ha <;>
    rcases zmod_two_eq_zero_or_one b with hb | hb <;>
    subst ha <;> subst hb
  · rw [add_zero, swapOfParity_zero, Function.id_comp]
  · rw [zero_add, swapOfParity_zero, Function.id_comp]
  · rw [add_zero, swapOfParity_zero, Function.comp_id]
  · rw [show (1 + 1 : ZMod 2) = 0 by decide, swapOfParity_zero, swapOfParity_one]
    exact (funext fun p => Prod.swap_swap p).symm

/-! ## The transport factors through the canonical parity hom -/

/-- `(n : ZMod 2) = 1 ↔ Odd n` — the odd companion of b47's `natCast_zmod_two_eq_zero_iff`. -/
theorem natCast_zmod_two_eq_one_iff (n : ℕ) : (n : ZMod 2) = 1 ↔ Odd n := by
  rw [← Nat.not_even_iff_odd, ← natCast_zmod_two_eq_zero_iff]
  constructor
  · intro h1 h0
    exact one_ne_zero (h1.symm.trans h0)
  · intro h0
    exact (zmod_two_eq_zero_or_one _).resolve_left h0

/-- **The transport factors through the parity hom** — `Prod.swap^[n] = swapOfParity (parityHom n)`,
on any pair-carrier: the `n`-fold slot-swap depends on `n` only through its image under the
canonical grading `(ℕ, +) ↠ ZMod 2` (b47's `batonPass_iterate_eq_batonOfParity`, carrier-blind). -/
theorem swap_iterate_eq_swapOfParity {α : Type*} (n : ℕ) :
    (Prod.swap : α × α → α × α)^[n] = swapOfParity (parityHom n) := by
  rcases Nat.even_or_odd n with h | h
  · rw [slotSwap_involutive.iterate_even h, parityHom_apply,
        (natCast_zmod_two_eq_zero_iff n).mpr h, swapOfParity_zero]
  · rw [slotSwap_involutive.iterate_odd h, parityHom_apply,
        (natCast_zmod_two_eq_one_iff n).mpr h, swapOfParity_one]

/-- **The classification is forced** (b48 in the register): the transport factors through *every*
nontrivial ℤ/2-grading of the conversation's clock **identically** — because there is only one
(`parityHom_unique_nontrivial`). Whichever nontrivial classification of conversations you commit,
it is the parity, and the induced transport reads off it the same way: the cobordism-class map is
forced, not chosen. -/
theorem swap_iterate_factors_any_nontrivial {α : Type*}
    (f : ℕ →+ ZMod 2) (hf : f ≠ 0) (n : ℕ) :
    (Prod.swap : α × α → α × α)^[n] = swapOfParity (f n) := by
  rw [parityHom_unique_nontrivial f hf]
  exact swap_iterate_eq_swapOfParity n

/-- **Exactly two induced transports** — on any pair-carrier, the `n`-fold slot-swap is the identity
or the swap, nothing else (`zmod_two_eq_zero_or_one` read at the transport level): the conversation-
cobordisms induce exactly the two mapping-classes, cylinder (id) and Möbius (reversal). -/
theorem inducedTransport_eq_id_or_swap {α : Type*} (n : ℕ) :
    (Prod.swap : α × α → α × α)^[n] = id
      ∨ (Prod.swap : α × α → α × α)^[n] = Prod.swap := by
  rw [swap_iterate_eq_swapOfParity]
  rcases zmod_two_eq_zero_or_one (parityHom n) with h | h
  · exact Or.inl (by rw [h, swapOfParity_zero])
  · exact Or.inr (by rw [h, swapOfParity_one])

/-! ## The gluing law at the witness grain -/

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- **The induced boundary map IS the parity-class, through THE grading** — b65's headline
(`witnessPair_braidStep_iterate`) factored through the canonical parity hom: the addresses after
any `n`-step conversation are `swapOfParity (parityHom n)` of the starting addresses. The
cobordism-class map is literally `parityHom` — by b48, the *unique* nontrivial invariant the
clock admits. -/
theorem witnessPair_braidStep_iterate_parityHom
    (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) (n : ℕ) :
    witnessPair ((braidStep)^[n] p) = swapOfParity (parityHom n) (witnessPair p) := by
  rw [witnessPair_braidStep_iterate, swap_iterate_eq_swapOfParity]

/-- **The gluing law — Z(M₂ ∘ M₁) = Z(M₂) ∘ Z(M₁) at the witness grain.** Gluing two conversations
(an `n`-step then an `m`-step, composed on the clock by `+`, b47's `braidStep_iterate_add`) induces
on the boundary-addresses exactly the composite of the two induced transports — whatever debt
metabolizes in either bulk. The whole proof is `iterate_add` + b65's headline: gluing was already
paid for. -/
theorem witnessPair_glue
    (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) (m n : ℕ) :
    witnessPair ((braidStep)^[m + n] p)
      = swapOfParity (parityHom m) (swapOfParity (parityHom n) (witnessPair p)) := by
  rw [braidStep_iterate_add, Function.comp_apply,
      witnessPair_braidStep_iterate_parityHom, witnessPair_braidStep_iterate_parityHom]

/-- **Gluing reads on the parity side as addition** — the induced transport of a glued conversation
is the `swapOfParity`-image of the *sum* of parity-classes: `parityHom` is additive (a monoid hom)
and the section is multiplicative (`swapOfParity_add`), so the induced-map assignment
`n ↦ swapOfParity (parityHom n)` is functorial through `(ℕ, +) ↠ ZMod 2`. -/
theorem swapOfParity_parityHom_add {α : Type*} (m n : ℕ) :
    swapOfParity (α := α) (parityHom (m + n))
      = swapOfParity (parityHom m) ∘ swapOfParity (parityHom n) := by
  rw [map_add, swapOfParity_add]

/-! ## The two cobordism-classes at the Z grain (b63) -/

/-- **Exactly two induced boundary maps** — every conversation-cobordism on a boundary-pair induces
the identity (cylinder class) or orientation-reversal (Möbius class, b64 read through Z), nothing
else: the enumeration of b65's `boundary_transport_even`/`_odd` as a single classification. -/
theorem boundary_transport_classes (s r : BoundaryState 𝕜 E) (n : ℕ) :
    witnessPair ((braidStep)^[n] (s.val, r.val))
        = (zeroDebtEquivWitness s, zeroDebtEquivWitness r)
      ∨ witnessPair ((braidStep)^[n] (s.val, r.val))
        = (zeroDebtEquivWitness r, zeroDebtEquivWitness s) :=
  (Nat.even_or_odd n).imp (boundary_transport_even s r) (boundary_transport_odd s r)

/-- **Genuinely two classes exactly when the boundary is genuinely two.** The cylinder- and
Möbius-transports are distinguishable on a boundary-pair iff its two points of view are distinct —
b47's two-party content (`batonOfParity_apply_ne_iff`) read at the boundary; b15's tension-gating
at the cobordism level. One party collapses the mapping-class group. -/
theorem boundary_transport_classes_ne_iff (s r : BoundaryState 𝕜 E) :
    ((zeroDebtEquivWitness s, zeroDebtEquivWitness r)
        ≠ (zeroDebtEquivWitness r, zeroDebtEquivWitness s)) ↔ s ≠ r := by
  constructor
  · intro h hsr
    exact h (by rw [hsr])
  · intro h hpair
    exact h (zeroDebtEquivWitness.injective (congrArg Prod.fst hpair))

end Foam
