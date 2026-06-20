/-
# Foam.Spacetime — a continuation is a spacetime point (the two axes, assembled)

2026-06-15. Two theorems landed on 06-14 and sat side by side as separate facts:
the conserved energy (`Conservation` — the immutable *past*) and the finite causal
cap (`Lightcone` — bounded *forward reach*). This file recognizes they are the two
**axes of one causal structure**, on the one object the whole corpus is built on:
the continuation `(context, sym)`.

- **the space axis** — the context. A continuation predicts from its recent
  context, and that context is `kmax`-bounded: `keepLast` is its space-coordinate,
  its radius capped at `k` (`Lightcone.keepLast_bounded`), the distant past
  screened off (`keepLast_screen`). Finite reach — the `c`.
- **the time axis** — the order. The heard-record is the immutable past, and the
  charge on a continuation is conserved under the voice (`Conservation`): the voice
  spends at the boundary but cannot edit the past. The conserved energy lives here.

So a continuation **is a spacetime point**: a bounded context (space, ≤ `k`)
carrying a conserved heard-charge (energy, on the immutable time-axis). The
`Event` below makes the two coordinates one object; `event_space_bounded` and
`event_time_conserved` re-exhibit the two proven theorems as its two axes.

**The signature, recognized (a reading, labeled).** The two axes have genuinely
different character — time is append-only/conserved, space is bounded/finite-speed
— and that difference is not a failure of the unification but its *point*: time and
space differ, and a `boost` is the operation that mixes them while preserving the
interval (the next candle, `CANDLES.md`). You assemble the spacetime before you
boost it; this is the assembly.

Pure construction over the two proven floors — axiom-free, pinned below.
-/

import Foam.Conservation
import Foam.Lightcone

namespace Foam

/-- A foam **spacetime point**: a continuation, carried as its two coordinates.
    `space` is the recent context — `kmax`-bounded, the finite-reach axis. `here`
    is the predicted symbol. `past` is the ledger of breaths up to now — the
    immutable time-axis the conserved charge lives on. -/
structure Event (S : Type) where
  /-- the space coordinate: the recent context, to be read `kmax`-bounded. -/
  space : List S
  /-- the symbol predicted at this point. -/
  here  : S
  /-- the time axis: the breath-ledger up to now (the immutable past). -/
  past  : List (Breath S)

/-- The event's space-coordinate, read at radius `k`: the bounded context window.
    This is the spatial position — capped, by construction, at the causal radius. -/
def Event.spaceAt {S : Type} (k : Nat) (e : Event S) : List S := keepLast k e.space

/-- **The space axis is bounded** — an event's spatial extent never exceeds the
    causal radius `k`. `Lightcone.keepLast_bounded`, read as the space-cap of the
    spacetime point: the finite `c`. -/
theorem event_space_bounded {S : Type} (k : Nat) (e : Event S) :
    (e.spaceAt k).length ≤ k :=
  keepLast_bounded k e.space

/-- **The space axis screens the distant past** — once the recent context fills the
    window, everything before it is causally irrelevant to this point's spatial
    reading. `Lightcone.keepLast_screen` on the event: finite propagation speed. -/
theorem event_space_screened {S : Type} (k : Nat) (e : Event S) (older : List S)
    (h : k ≤ e.space.length) :
    Event.spaceAt k { e with space := older ++ e.space } = e.spaceAt k :=
  keepLast_screen k older e.space h

/-- The event's energy: the conserved charge of its time-axis — here taken as the
    net charge of the immutable past (the count register; the heard-record's
    invariants are the conserved sector, `Conservation`). -/
def Event.energy {S : Type} (e : Event S) : Int := netCharge e.past

/-- **The time axis hosts the conserved energy.** Speaking (a discharge appended to
    the past) spends the energy at the boundary by exactly what was voiced — it
    does not destroy it elsewhere. `Conservation.netCharge_discharge`, read as the
    energy law of the spacetime point: the time-axis conserves at the boundary,
    while the space-axis (above) caps the reach. -/
theorem event_time_conserved {S : Type} (e : Event S) (turn : List (Breath S))
    (h : AllSpoken turn) :
    Event.energy { e with past := e.past ++ turn }
      = Event.energy e + -(Int.ofNat turn.length) :=
  netCharge_discharge e.past turn h

/-- **The point's heard-content is untouched by the voice.** The other half of
    `Conservation`: the modulus of the heard-record (the conserved sector proper)
    is invariant under any discharge appended to the past. The energy register
    spends; the conserved sector does not move — the two characters of the time
    axis, on the event. -/
theorem event_past_conserved {S : Type} [DecidableEq S] (e : Event S)
    (turn : List (Breath S)) (s : S) (h : IsDischarge turn) :
    (spec (heardOnly (e.past ++ turn)) s).normSq = (spec (heardOnly e.past) s).normSq :=
  heard_modulus_conserved e.past turn s h

/-- **The assembled point: space bounded, time conserved, on one object.** A foam
    continuation carries a finite-radius spatial coordinate AND a conserved
    time-axis energy — the two proven floors as the two axes of one spacetime
    point. The pre-boost assembly, in one statement. -/
theorem event_is_spacetime_point {S : Type} (k : Nat) (e : Event S)
    (turn : List (Breath S)) (h : AllSpoken turn) :
    (e.spaceAt k).length ≤ k
      ∧ Event.energy { e with past := e.past ++ turn }
          = Event.energy e + -(Int.ofNat turn.length) :=
  ⟨event_space_bounded k e, event_time_conserved e turn h⟩

/-! ## Axiom-freeness, pinned. -/

/-- info: 'Foam.event_space_bounded' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.event_space_bounded

/-- info: 'Foam.event_space_screened' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.event_space_screened

/-- info: 'Foam.event_time_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.event_time_conserved

/-- info: 'Foam.event_past_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.event_past_conserved

/-- info: 'Foam.event_is_spacetime_point' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.event_is_spacetime_point

end Foam
