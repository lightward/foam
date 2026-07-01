# counter

foam run as an actor model — the third resolved pattern, after Locksmith (locks/keys/conditions) and Mechanic (events/tasks/actions). Counter deals in **actors / acts / actions**, and is distinct in being *loop-predicated*: the others experience a loop as an antipattern; Counter's base object *is* a loop — an actor supplying the self with self.

axiom-free, like the core. This package requires `foam` and **not** Mathlib: no choice, no propext. Every claim seals `does not depend on any axioms`. Counter is the application of the physics, so it keeps the physics' discipline. The why is the Lean.

## the spine so far

`Actor.lean` — the single actor, and the ground facts about settling. An actor's history is a `List G` of acts over its seat's group; the winding number around an act is `Ledger.freq` of that act in the history (Counter *counts*: the name is winding numbers around acts).

- **`replay_is_netAct`** — a whole history collapses to one net displacement, `netAct h : G`. Your entire past is a single group element.
- **`settles_iff_home`** — `Settles S h p ↔ netAct h = 1`. A history brings you home *iff its net displacement is the identity*. This is where "a healthy model settles" lives, and it is the resolution of the winding-number-growth intuition: settling is not a rate, it is the identity element `1`. Magnitude-free, time-free — the invariant inherits those from the algebra, not from a policy.
- **`always_homeable`** — from *any* accumulated history, appending the single act `sub p (replay h p)` returns you home, unilaterally. "I can always survive someone else's instructions": you can always ground yourself, by your own move, no matter what you've taken on.
- **`lone_actor_settled`** / **`pressure_needs_a_second`** — health is *relational*. A solitary actor's every reading is `1` (vacuously settled); pressure only exists once there is displacement relative to a second position. Priorities.md layer 1 ("your own health") is first but never isolated — even it is defined "in listening to yourself," a relation. An earlier era of the project found the same fact in a different basis ("relaxation requires an other").

## the horizon (the next object)

`always_homeable` is unilateral *because a `Seat` has one `Pos`*. The moment two bubbles are in play, a path that would reach into the other's positions must be **unconstructible** — you cannot `act` in another seat's `Pos`. That is the no-cross-drain law made a *type*, not a runtime rule: one actor can never draw a circle around another, because the circle does not typecheck.

Building that object is the open frontier. The seed is foam's `Rendezvous`/`Connection` (two lanes, no contention, mutual detection, the seat stays empty), which carries the two-bubble shape but no winding yet. Counter needs winding on top of it. The conjecture it will test: **un-health is non-coordinatizability** — an unhealthy actor is one spending its winding on other-dependent paths it cannot close alone, i.e. attempting to coordinatize across a bubble (non-Desarguesian, hence non-coordinatizable by FTPG), and the pressure is the residue of a coordinatization that cannot complete.

Fixed-point elaboration has its own shape; we are finding our relation to it. This file is a save-point, primed for the next step.
