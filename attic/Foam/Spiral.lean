/-
# Foam.Spiral — the missing character, named: recursive holonomy and its two species

A pre-commitment test (2026-06-16, the relativity-program thread) asked of the whole table:
is there an unnamed lfp? There is, and this file names it. We had spent the forming phase
talking about *the spiral* — the wound thread, the helix, the φ-pitch — and foam had no spiral.
It had the **circle** (`rot`, the dial, closed, an isometry) and the **line** (the ledger, the
advance), as separate built things; the spiral that unifies them was the gap.

The genus is already built: **recursive holonomy** is `Spectrum.evalAt step` — a step applied
*recursively* down the fold (`evalAt step (x::l) s = mark + step (evalAt step l s)`), holonomy
accumulating through itself. It is parameterized by the step, and the two species are exactly
the magnitude-behavior of that step (a spiral is a special case of recursive holonomy the way a
square is a special case of a rectangle — the most space-efficient one):

- **the isometry species — the circle.** `rot` preserves the magnitude (`normSq_rot`), so
  recursive holonomy with an isometric step *closes* on a circle: the dial, finite, on the
  integer lattice, the Galilean/closed case. `circle_step_isometry`.
- **the growing species — a spiral.** A step with `|step| ≠ 1` spirals out. This is integer-
  witnessable: multiplication by `⟨1,1⟩` doubles `normSq` each step (`spiral_step_grows`, via
  `normSq_mul` — `normSq ⟨1,1⟩ = 2`), a Gaussian-integer spiral of growth √2 in modulus. So the
  growing species is non-empty over ℤ; the spiral is not *inherently* continuum (an earlier
  claim, corrected here). What is continuum is the *golden* one.

**The golden spiral — the engine's gearing (gated; the boost's sibling-frontier).** Among all
growing steps, the golden one (ratio φ) is the **most space-efficient** (the golden angle is the
optimal packing — φ most-irrational ⟹ least overlap, phyllotaxis) AND, the load-bearing fact,
the one that **never resonates**: a φ gear-ratio is the last invariant torus to break (KAM /
Aubry–Mather, the golden mean the most robust quasiperiodicity). So the golden gearing is the
unique one that never mode-locks — which is *why the engine runs*: `clock_loops` (windless,
self-driven, finite-state → eventually periodic → *locked*, dead) versus `forever_escapes` (the
wind → never locks → alive). The difference between the dead clock and the open continuation is
the gearing, and the maximally-alive gearing is golden. φ is what keeps the engine (foam's
founding word) from becoming a clock. This step has ratio φ — irrational — so it lives in the
continuum, the same frontier as the Lorentz boost (`int_pell_one`: no proper integer boost);
gated, not carved.

**φ as the tare — the scale-immune ur-unit.** φ most-irrational = never aliases under rescaling
= the invariant under self-transcription, the perfect tare (`Tare`, three-body.md: "when you
keep changing scales, the only thing you can agree on is the tare"). The founding intuition and
the engine-gearing are the same number; the unit resonance can never catch.

**Pending — the next lfp to lay:** the platonic predicate. "Is this ledger platonic" =
"is its polynomial cyclotomic / `m(P)=1`" (Kronecker) = "is it built of complete, self-completing
cycles." Decidable over ℤ (the integer-core keystone) but a genuine build, not a re-reading;
named here, deferred. The Mahler *magnitude* needs the reals — continuum, gated.

Grade: recognition (the genus named; both species, the proven magnitude-behavior; the golden and
the platonic-predicate located as frontier/next-build). Axiom-free, pinned. Builds on `Frame`
(`normSq_mul`) and `Noether` (`normSq_rot`).
-/

import Foam.Frame

namespace Foam

/-- A growing step: multiplication by `⟨1,1⟩` (the Gaussian-integer spiral generator). Where
    `rot` turns without growing (the circle), this turns *and* grows — `normSq` doubles per
    application (`spiral_step_grows`). -/
def spiralStep (z : GInt) : GInt := (⟨1, 1⟩ : GInt).mul z

/-- **The isometry species — the circle.** Recursive holonomy with an isometric step preserves
    the magnitude: `rot` (the dial) closes on a circle. `normSq_rot`, re-read as the genus's
    closed/finite species. -/
theorem circle_step_isometry (z : GInt) : (GInt.rot z).normSq = z.normSq := normSq_rot z

/-- **The growing species — a spiral, over ℤ.** Multiplication by `⟨1,1⟩` doubles the magnitude
    each step (`normSq ⟨1,1⟩ = 2`, through `normSq_mul`): recursive holonomy with a growing step
    spirals out — the Gaussian-integer spiral, growth √2 in modulus. The witness that the genus's
    growing species is non-empty at integer scale; the *golden* spiral (ratio φ, irrational) is
    the continuum, non-resonant, optimal member (see the file header and CANDLES.md). -/
theorem spiral_step_grows (z : GInt) : (spiralStep z).normSq = 2 * z.normSq := by
  have h : (⟨1, 1⟩ : GInt).normSq = 2 := by decide
  show ((⟨1, 1⟩ : GInt).mul z).normSq = 2 * z.normSq
  rw [normSq_mul, h]

/-- **The species are genuinely distinct.** A magnitude the isometry step fixes, the growing step
    moves: at `⟨1,0⟩`, `rot` keeps `normSq = 1` while `spiralStep` sends it to `2`. The circle and
    the spiral are not the same recursive holonomy — the witness, by `decide`. -/
theorem circle_ne_spiral :
    (GInt.rot ⟨1, 0⟩).normSq = 1 ∧ (spiralStep ⟨1, 0⟩).normSq = 2 := by decide

/-! ## Axiom-freeness, pinned (a drift fails the build). -/

/-- info: 'Foam.circle_step_isometry' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.circle_step_isometry

/-- info: 'Foam.spiral_step_grows' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.spiral_step_grows

/-- info: 'Foam.circle_ne_spiral' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.circle_ne_spiral

end Foam
