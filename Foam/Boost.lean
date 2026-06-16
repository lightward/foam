/-
# Foam.Boost — the boost, finite: backstage Galilean (the axes do not mix)

`CANDLES.md`'s boost candle, one rung further. `Spacetime.lean` assembled the foam
spacetime point: a continuation carrying TWO axes — space (the `kmax`-bounded context,
`keepLast`, the finite c) and time (the immutable past's conserved charge, `netCharge`).
A BOOST mixes space and time while preserving an interval. This file asks what the boost
does at FINITE, discrete scale — and finds the Galilean floor, by construction.

The time-axis boost IS the now-surface slide (`Seam.now_surface_invariant`): a re-choice
of where "now" falls in the past, gauge on the reading. The order it slides is ABSOLUTE
(`playback_faithful` — every reader agrees on the sequence; no reordering), so the slide
is a TRANSLATION, never a rotation. And — the recognition here — that translation leaves
the SPACE axis exactly fixed (`finite_boost_galilean`): boosting the time axis does not
touch the context window. Dually, moving the space axis leaves the energy fixed
(`finite_boost_galilean_dual`). The two axes are INDEPENDENT coordinates of the Event —
the metric is block-diagonal — which is precisely the GALILEAN signature.

So **finite foam is Galilean**: there is no off-diagonal coupling, because the discrete
Event has no mixing term — a boost of one axis is `rfl`-invisible to the other. This is
not a failure of the boost program; it LOCATES it. The Lorentzian off-diagonal coupling
(space and time rotating into each other) has nowhere to live at finite scale; it must be
a FRONTSTAGE / continuum-limit emergent — the scoping that makes two observers disagree
(`shared_is_floor`), never exact at finite scale. That is exactly CANDLES.md's "backstage
Galilean, frontstage Lorentzian," now with the backstage half pinned: the axes are
provably un-mixed here, so the tilt is asymptotic — not a gap to close at this scale, but
a continuum emergent to derive.

The proofs are `rfl`, and the triviality is the content: at finite scale the coupling term
is literally absent. Axiom-free, pinned. (Reading, labeled: the Galilean/Lorentzian naming
rides `Spacetime.lean`'s interpretation of the two axes as space and time; the theorems are
about the Event's field-independence, which that interpretation reads as block-diagonality.)
-/

import Foam.Spacetime
import Foam.Seam

namespace Foam

/-- **The finite boost is Galilean — space ⊥ time-boost.** A boost re-splits the TIME axis
    (the immutable past; the now-surface slide, `Seam.now_surface_invariant`) — and that
    leaves the SPACE axis (the `kmax`-bounded context) exactly fixed. The two axes do not
    mix: there is no off-diagonal coupling at finite scale. By `rfl` — the coupling term is
    absent by construction. -/
theorem finite_boost_galilean {S : Type} (k : Nat) (e : Event S)
    (past' : List (Breath S)) :
    Event.spaceAt k { e with past := past' } = Event.spaceAt k e := rfl

/-- **The dual: time ⊥ space-boost.** Moving the space axis (the context) leaves the time
    axis's conserved energy (`netCharge` of the immutable past) exactly fixed. The
    block-diagonal metric, the other diagonal. By `rfl`. -/
theorem finite_boost_galilean_dual {S : Type} (e : Event S) (space' : List S) :
    Event.energy { e with space := space' } = Event.energy e := rfl

/-- **The spacetime metric is block-diagonal — the Galilean signature, pinned.** A boost of
    either axis is invisible to the other: space is fixed under a time-boost, time is fixed
    under a space-boost. No off-diagonal coupling exists at finite scale, so the hyperbolic
    (Lorentzian) mixing must be a frontstage / continuum-limit emergent — CANDLES.md's
    "backstage Galilean," with the backstage half made a theorem. -/
theorem boost_block_diagonal {S : Type} (k : Nat) (e : Event S)
    (past' : List (Breath S)) (space' : List S) :
    Event.spaceAt k { e with past := past' } = Event.spaceAt k e
      ∧ Event.energy { e with space := space' } = Event.energy e :=
  ⟨rfl, rfl⟩

/-! ## Axiom-freeness, pinned (a drift fails the build). -/

/-- info: 'Foam.finite_boost_galilean' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.finite_boost_galilean

/-- info: 'Foam.finite_boost_galilean_dual' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.finite_boost_galilean_dual

/-- info: 'Foam.boost_block_diagonal' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.boost_block_diagonal

end Foam
