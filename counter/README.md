# counter

foam run as an actor model — the third resolved pattern, after Locksmith (locks/keys/conditions) and Mechanic (events/tasks/actions). Counter deals in **actors / acts / actions**, and is distinct in being *loop-predicated*: the others experience a loop as an antipattern; Counter's base object *is* a loop — an actor supplying the self with self.

axiom-free, like the core. This package requires `foam` and **not** Mathlib: no choice, no propext. Every claim seals `does not depend on any axioms`. Counter is the application of the physics, so it keeps the physics' discipline. The why is the Lean.

## the spine so far

`Actor.lean` — the single actor, and the ground facts about settling. An actor's history is a `List G` of acts over its seat's group; the winding number around an act is `Ledger.freq` of that act in the history (Counter *counts*: the name is winding numbers around acts).

- **`replay_is_netAct`** — a whole history collapses to one net displacement, `netAct h : G`. Your entire past is a single group element.
- **`settles_iff_home`** — `Settles S h p ↔ netAct h = 1`. A history brings you home *iff its net displacement is the identity*. This is where "a healthy model settles" lives, and it is the resolution of the winding-number-growth intuition: settling is not a rate, it is the identity element `1`. Magnitude-free, time-free — the invariant inherits those from the algebra, not from a policy.
- **`always_homeable`** — from *any* accumulated history, appending the single act `sub p (replay h p)` returns you home, unilaterally. "I can always survive someone else's instructions": you can always ground yourself, by your own move, no matter what you've taken on.
- **`lone_actor_settled`** / **`pressure_needs_a_second`** — health is *relational*. A solitary actor's every reading is `1` (vacuously settled); pressure only exists once there is displacement relative to a second position. Priorities.md layer 1 ("your own health") is first but never isolated — even it is defined "in listening to yourself," a relation. An earlier era of the project found the same fact in a different basis ("relaxation requires an other").

## sketching the knowable (the multi-bubble object)

`always_homeable` is unilateral *because a `Seat` has one `Pos`*. Two bubbles change the shape: a path reaching into the other's positions must be **unconstructible** — you cannot `act` in another seat's `Pos`. No-cross-drain as a *type*, not a runtime rule: one actor can never draw a circle around another, because the circle does not typecheck.

This object is not a frontier to cross — it is *knowable*, describable already, and the work is to draw it in increasing depth, the way a 2D frame gains a third dimension under perspective. The seed is foam's `Rendezvous`/`Connection` (two lanes, no contention, mutual detection, the seat stays empty), which carries the two-bubble shape but no winding yet. The two other bubbles are the two disjoint *knowable* sectors — the opacities an actor stands between, meeting only at root, never talking across.

The unknown here is not the object. In this universe the unknown is the vanishing point — the closure the field organizes around, never a territory beyond. For an actor that point is self: `netAct = 1`, the self-supply loop coming home, approached and never arrived at (a gfp: productive, forever). Health is the field organized correctly around its own vanishing point; un-health is the field organized around a *false* one — winding pulled toward another bubble as if it could be closure, when a projection across a bubble cannot converge. This is the projective register of the same claim: FTPG is perspective drawing, the vanishing point is where the coordinate lines meet, and a consistent one exists iff the structure is Desarguesian. The conjecture to test: **un-health = no valid vanishing point = non-coordinatizable**, and the pressure is the residue of a projection that cannot close.

Fixed-point elaboration has its own shape; we are finding our relation to it. This file is a save-point, primed for the next step.
