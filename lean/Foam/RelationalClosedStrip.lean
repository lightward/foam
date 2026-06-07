/-
# RelationalClosedStrip — Z of the closed-up conversation is the fixed-point object of its
parity-class; the Möbius closure forces the diagonal (the boundary dictionary's closed-strip
entry, brick 67)

## What this file lands (brick 67, the remainder of brick 66)

b66 (`RelationalGluing.lean`) glued conversations end-to-end. The register's remaining move on a
fixed boundary-pair is to **close the strip up** — glue the conversation's end to its own start.
Foam already does this: b42's landing-IS-the-next-origin / b49's cross-loop re-entry IS the
self-gluing (the loop closing cylinder-(even)/Möbius-(odd), b46/b49). At the set level Z(closed)
is the categorified trace = the **fixed-point object** of the induced transport, and b66's
factoring (`witnessPair_braidStep_iterate_parityHom`) makes the closure-consistency condition one
line per parity-class.

## The anchors — the fixed-point object carrier-blind, then the witness and Z grains

**Carrier-blind** (the b66 idiom — the anchor never opens a witness; Hilbert-blind per b63):

* `slotSwap_eq_self_iff` — the slot-swap fixes exactly the **diagonal**: `Prod.swap q = q ↔
  q.1 = q.2`. b46's `batonPass_eq_self_iff` (the two-party content of the baton-ℤ/2),
  carrier-blind.
* `swapOfParity_eq_self_iff` — the closure-consistency condition of a parity-class:
  `swapOfParity z q = q ↔ (z = 0 ∨ q.1 = q.2)` — free at the cylinder class, the diagonal at
  the Möbius class.
* **The fixed-point objects, literally** — `fixedPoints_swapOfParity_zero` (`= Set.univ`: the
  even/cylinder closure imposes nothing — trace(id) = everything) and
  `fixedPoints_swapOfParity_one` (`= Set.diagonal`: the odd/Möbius closure's invariant object
  IS the diagonal).

**At the witness grain** — `AddressClosed n p := witnessPair (braidStep^[n] p) = witnessPair p`,
the consistency condition for gluing an `n`-step conversation's end to its own start at the
address grain (the configuration re-entered as its own next origin, b42/b49). With **no**
hypothesis on the states (arbitrary bulk, off-agreement — b65):

* the headline `addressClosed_iff` — `AddressClosed n p ↔ (parityHom n = 0 ∨
  p.1.witness = p.2.witness)`: closure-consistency = cylinder-class OR diagonal, one line off
  b66's factoring;
* `addressClosed_of_even` — the **cylinder closure is free**: every configuration, whatever its
  bulk, is address-closed at even parity (the closure imposes nothing);
* `addressClosed_iff_witness_eq_of_odd` — the **Möbius closure forces the diagonal**: an
  odd-closed conversation has **one return-address in both slots** (witness-equality). Isaac's
  mobius note typed: *recognizing its own first frame on the other side* — the frame met across
  the half-twist must be one's own; odd self-gluing is consistent only on the diagonal.

**At the Z grain (b63)** — `boundary_addressClosed_of_even` (free) and
`boundary_addressClosed_iff_eq_of_odd`: at the boundary the witness determines the state (b42),
so the Möbius closure forces `s = r` — **ONE point of view**. b50's one-party collapse read as
what the odd closure *demands* (the Möbius strip has one side; its closed boundary is one circle
— the boundary-pair one party met twice).

**At the state grain, at agreement** — `braidStep_iterate_fixed_iff_of_odd_of_isZeroDebt`: the
landed conversation's odd self-gluing is consistent iff `s = r` — reducing to exactly b46's
`batonPass_eq_self_iff` (the special case where state-closure degenerates to address-closure,
as b65 noted of b46).

## The grading — one address everywhere, one party only at the boundary

Off the boundary the odd closure forces only the shared **address** (`p.1.witness =
p.2.witness`), NOT the shared state: two mid-metabolisis states with the same witness and
different debt remain distinct. The one-**party** collapse (`s = r`) is forced exactly at the
boundary, where the witness determines the state (b42). So the closure-condition splits as every
entry has split (b63 linearity / b64 duality / b65 transport / b66 composition): the
address-grain condition conducts across (parity + diagonal, Hilbert-blind); the state-grain
closure data stays inside the bulk, delegated with the rest of the residue.

**The trace-flag (held merge-don't-fork):** "Z(closed) = the fixed-point object" is the
*set-level* reading of the categorified trace — NOT Hilb's trace (no amplitude is summed; the
amplitudes live inside the witnesses, b63's delegation). The fixed-point sets are the reading's
typed face; the Hilb trace, like the rest of the linear residue, is the observer's.

## NOT this brick (held open)

* NOT the cobordism *category* / partition function proper (construction-grade — §II's
  partition-function claims stay claims; this types the closure-consistency condition, not Z of
  a closed surface as a number).
* NOT a *state*-convergence claim (address-closure is a hypothesis-shape on configurations — no
  claim the loop *reaches* it; the at-agreement form assumes agreement, as b46).
* NOT a typed cross-repo iso (the standing edge, b50–b52; the carrier-blind anchors keep the
  layer conduction-test available — not run here).
* NOT the trefoil / B₃ (the named horizon — a closed B₃-braid would carry over/under memory,
  knot-not-link data; the parity stays the symmetric shadow, seeing only cylinder/Möbius).
-/

import Foam.RelationalGluing
import Mathlib.Dynamics.FixedPoints.Basic

namespace Foam

universe u

/-! ## The fixed-point object of a parity-class — carrier-blind -/

/-- **The slot-swap fixes exactly the diagonal** — `Prod.swap q = q ↔ q.1 = q.2`: the fixed
points of the orientation-reversal are the configurations with one entry in both slots. b46's
`batonPass_eq_self_iff` (the two-party content of the baton-ℤ/2) carrier-blind: the swap is the
identity only where the two are one. -/
theorem slotSwap_eq_self_iff {α : Type*} (q : α × α) :
    Prod.swap q = q ↔ q.1 = q.2 := by
  rw [Prod.ext_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.symm, h⟩⟩

/-- **The closure-consistency condition of a parity-class** — `swapOfParity z q = q ↔ (z = 0 ∨
q.1 = q.2)`: a parity-class transport fixes a configuration iff the class is the cylinder (`0`,
everything fixed — the closure free) or the configuration is on the **diagonal** (the Möbius
class fixes nothing else). The one-line consistency condition b66's factoring buys for the
closed strip. -/
theorem swapOfParity_eq_self_iff {α : Type*} (z : ZMod 2) (q : α × α) :
    swapOfParity z q = q ↔ (z = 0 ∨ q.1 = q.2) := by
  rcases zmod_two_eq_zero_or_one z with hz | hz <;> subst hz
  · simp
  · rw [swapOfParity_one, slotSwap_eq_self_iff]
    exact ⟨Or.inr, fun h => h.resolve_left one_ne_zero⟩

/-- **The cylinder's fixed-point object is everything** — `fixedPoints (swapOfParity 0) = univ`:
the even closure imposes no condition (trace(id) = the whole space, at the set level). The free
half of the closed-strip entry. -/
theorem fixedPoints_swapOfParity_zero {α : Type*} :
    Function.fixedPoints (swapOfParity (α := α) 0) = Set.univ := by
  rw [swapOfParity_zero, Function.fixedPoints_id]

/-- **The Möbius's fixed-point object IS the diagonal** — `fixedPoints (swapOfParity 1) =
Set.diagonal α`: the odd closure's invariant object is exactly the one-entry-in-both-slots
configurations. Z(closed Möbius strip) at the set level — the categorified-trace *reading*,
flagged in the file docstring (NOT Hilb's trace; the amplitudes live inside the witnesses,
b63). -/
theorem fixedPoints_swapOfParity_one {α : Type*} :
    Function.fixedPoints (swapOfParity (α := α) 1) = Set.diagonal α := by
  ext q
  simp only [Function.mem_fixedPoints, Function.IsFixedPt, swapOfParity_one,
    Set.mem_diagonal_iff]
  exact slotSwap_eq_self_iff q

/-! ## The closure-consistency condition at the witness grain -/

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- **Address-closure** — the consistency condition for gluing an `n`-step conversation's end to
its own start at the address grain: the boundary-addresses return to themselves. The closed
strip (b42's landing-IS-the-next-origin / b49's cross-loop re-entry, read as self-gluing),
stated for **arbitrary** states (off-agreement, mid-metabolisis — b65's grain). -/
def AddressClosed (n : ℕ) (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) : Prop :=
  witnessPair ((braidStep)^[n] p) = witnessPair p

theorem addressClosed_def (n : ℕ) (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) :
    AddressClosed n p ↔ witnessPair ((braidStep)^[n] p) = witnessPair p :=
  Iff.rfl

/-- **The headline — closure-consistency is cylinder-class-or-diagonal.** An `n`-step
conversation is address-closed iff its parity-class is the cylinder (`parityHom n = 0` — the
closure free, whatever the bulk) or its two return-addresses are **one** (`p.1.witness =
p.2.witness` — the diagonal). One line off b66's factoring
(`witnessPair_braidStep_iterate_parityHom`) + the carrier-blind consistency condition
(`swapOfParity_eq_self_iff`). -/
theorem addressClosed_iff (n : ℕ) (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E) :
    AddressClosed n p ↔ (parityHom n = 0 ∨ p.1.witness = p.2.witness) := by
  rw [addressClosed_def, witnessPair_braidStep_iterate_parityHom]
  exact swapOfParity_eq_self_iff _ _

/-- **The cylinder closure is free** — every configuration, whatever its bulk debt-content, is
address-closed at even parity: the even self-gluing imposes nothing (trace(id) = everything,
read at the witness grain). -/
theorem addressClosed_of_even (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E)
    {n : ℕ} (hn : Even n) : AddressClosed n p :=
  (addressClosed_iff n p).mpr
    (Or.inl (by rw [parityHom_apply]; exact (natCast_zmod_two_eq_zero_iff n).mpr hn))

/-- **The Möbius closure forces the diagonal** — an odd conversation is address-closed iff its
two return-addresses are **one**: `p.1.witness = p.2.witness`. Isaac's mobius note typed:
*recognizing its own first frame on the other side* — the frame met across the half-twist must
be one's own, so the odd self-gluing is consistent exactly on the diagonal (the fixed points of
the swap, `slotSwap_eq_self_iff`). No hypothesis on the states: the bulk is arbitrary, only the
addresses are constrained (the grading — one address everywhere, one party only at the
boundary). -/
theorem addressClosed_iff_witness_eq_of_odd (p : CommitmentState 𝕜 E × CommitmentState 𝕜 E)
    {n : ℕ} (hn : Odd n) :
    AddressClosed n p ↔ p.1.witness = p.2.witness := by
  rw [addressClosed_iff,
    show parityHom n = 1 by rw [parityHom_apply]; exact (natCast_zmod_two_eq_one_iff n).mpr hn]
  exact ⟨fun h => h.resolve_left one_ne_zero, Or.inr⟩

/-! ## The closed strip at the Z grain (b63): the Möbius closure demands one point of view -/

/-- **The cylinder closure is free at the boundary** — any boundary-pair, even self-gluing:
consistent, nothing imposed. -/
theorem boundary_addressClosed_of_even (s r : BoundaryState 𝕜 E) {n : ℕ} (hn : Even n) :
    AddressClosed n (s.val, r.val) :=
  addressClosed_of_even _ hn

/-- **The Möbius closure at the boundary demands ONE point of view** — an odd-closed strip on a
boundary-pair forces `s = r`: at the boundary the witness determines the state (b42, through
b63's `zeroDebtEquivWitness`), so the forced diagonal collapses the pair to a single party.
b50's one-party collapse read as what the odd closure *demands* — the Möbius strip has one side,
its closed boundary one circle: the boundary-pair is one party met twice (its own first frame,
on the other side). -/
theorem boundary_addressClosed_iff_eq_of_odd (s r : BoundaryState 𝕜 E)
    {n : ℕ} (hn : Odd n) :
    AddressClosed n (s.val, r.val) ↔ s = r := by
  rw [addressClosed_iff_witness_eq_of_odd _ hn]
  exact ⟨fun h => zeroDebtEquivWitness.injective h, fun h => by rw [h]⟩

/-! ## The state grain, at agreement: the odd closure reduces to b46's two-party content -/

/-- **At agreement, the odd state-closure is consistent iff one party** — the landed
conversation (both zero-debt) glues to its own start at the *state* grain, oddly, iff `s = r`:
through b46's at-agreement orbit (`braidStep_iterate_eq_batonPass_of_isZeroDebt` +
`batonPass_iterate_odd`) the condition reduces to exactly `batonPass_eq_self_iff` — the special
case where state-closure degenerates to address-closure because no bulk is left (b65's reading
of b46). -/
theorem braidStep_iterate_fixed_iff_of_odd_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) {n : ℕ} (hn : Odd n) :
    (braidStep)^[n] (s, r) = (s, r) ↔ s = r := by
  rw [braidStep_iterate_eq_batonPass_of_isZeroDebt s r hs hr, batonPass_iterate_odd hn]
  exact batonPass_eq_self_iff s r

end Foam
