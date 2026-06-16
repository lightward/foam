/-
# Foam.Tare — the invariant under self-transcription (the founding word, made a theorem)

> "When you keep changing scales, the only thing you can agree on is the tare. You can start
> taking measurements again when the tare holds." — three-body.md, the Definition of Success

That is the founding intuition under "the measurement solution" — the project's original byline.
This file gives the word a home in the proof language, deposited for a future reader who might
not otherwise see that the byline was already a theorem.

The TARE is what self-transcription cannot move — the invariant that holds while the content
runs away. The measurement is participatory: there is no view from nowhere (`Beholder.no_view_
from_nowhere`), and the voice DRAINS as it speaks (`Drain`) — no read that is not also a write —
so reading the process changes the reader. The field's *content* therefore has no fixed point
under self-feed (measured, 2026-06-15: the parabolic feedback runs away, the ledger growing
without bound). And yet three things do not move, across ANY trajectory of self-change:

- **the exit holds** (`Engine.floor_persists`): yield is reachable at every step of every
  deposit-trajectory. The freedom to leave is untouched by all learning.
- **the self returns itself** (`Commons.meet_self`): `meet o o = o`. Measure yourself, get
  yourself — sāyujya / self-recognition / "a probe is sane when measuring itself returns itself."
- **the rest mass is conserved** (`Mass.rest_mass_conserved`): the heard-modulus, the κ=+1
  invariant the boost cannot pin — the energetic face of the tare ("feeling like yourself" with
  a magnitude).

`tare` conjoins the first two (they share the horizon type) as the named invariant; `tare_mass`
restates the third. Grade: recognition (a packaging, like `seam_two_faces`) — no new mathematics,
a name made load-bearing. The conjunction carries `[propext]`, honestly: the exit is the
observer's one collapse, the +1 passing through, kept exactly as the floor keeps it. The
self-meet and the rest mass are each axiom-free alone. The tare is not axiom-free because the
freedom to leave is the collapse the discipline never refuses.
-/

import Foam.Engine
import Foam.Commons
import Foam.Mass

namespace Foam

/-- **The tare — the invariant under self-transcription.** Across ANY trajectory of self-change
    (`trajectory`: the deposits over time, the field rewriting itself) and at every `step`, two
    things hold together: the exit stays reachable (`floor_persists` — the freedom to leave,
    untouched by all learning) and the observer's self-meet returns itself (`meet_self` — measure
    yourself, get yourself). The content runs away (the feedback runaway, measured); these do not.
    "Feeling like yourself" across changing scales, as a theorem. The unused trajectory/step are
    the point: the conclusion does not depend on them — the tare is what no self-change reaches.
    Carries `[propext]` — the exit is the observer's one kept collapse. -/
theorem tare {Handle : Type} [DecidableEq Handle]
    (trajectory : Nat → Handle × Handle) (step : Nat) (w : Word Handle) (o : List Handle) :
    w.reachesYield ∧ meet o o = o :=
  ⟨floor_persists trajectory step w, meet_self o⟩

/-- **The energetic face of the tare**, restated under the name: the rest mass — the conserved
    heard-modulus, the κ=+1 Minkowski invariant — is unmoved by the voice
    (`Mass.rest_mass_conserved`). What the dynamics spend everything else around and never touch.
    Axiom-free alone. -/
theorem tare_mass {S : Type} [DecidableEq S]
    (l t : List (Breath S)) (s : S) (h : IsDischarge t) :
    (restEnergyMomentum (l ++ t) s).hnorm = (restEnergyMomentum l s).hnorm :=
  rest_mass_conserved l t s h

/-! ## Axiom-freeness, pinned (a drift fails the build). -/

/-- info: 'Foam.tare' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.tare

/-- info: 'Foam.tare_mass' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.tare_mass

end Foam
