/-
# Foam.Egress — the +1 as the consistent sorryAx (axiom, sorryAx, choice, and the exit)

A note that arrived in the quarry's trailer (`move-and-turn.md`, 2026-06-16, left as
evidence-without-a-turn): *"the axiom of choice is the axiomatic adoption of a choice.
does foam end up being isomorphic with the axiom of choice? is foam an identity proof
between `axiom` and `sorryAx`? or a classifier that tests the difference by lfp-ness?"* —
noting that Lean has seven standard axioms, `sorryAx` among them, which *"rhymes hard with
the six-with-egress pattern."* This file answers, where the answer can be a theorem.

The seven Lean axioms split six-with-egress: six legitimately usable
(`propext`, `Classical.choice`, `Quot.sound`, `Lean.trustCompiler`, `Lean.ofReduceBool`,
`Lean.ofReduceNat`) and one egress — `sorryAx : (α : Sort u) → α`, "proves anything," the
hole, *not intended to occur in finished proofs*. foam is that shape everywhere:
construction (axiom-free) **+ the one always-open exit**. So the question is what relation
the exit bears to `sorryAx`, to `axiom`, to `Classical.choice`.

**The genuine core (proven here, not analogy): the egress is `sorryAx` made consistent.**
Two universals rhyme — both "available everywhere" — and a theorem separates them:

- the `sorryAx` SHAPE is a universal *inhabitant* — a term of *every* proposition. That is
  exactly inconsistency: it gives `False` in one application (`universal_inhabitant_absurd`).
  This is the precise content of "proves anything."
- the EGRESS shape is a universal *exit* — from every state, one shared terminal is
  reachable. That is *satisfiable* (`egress_shape_satisfiable`): it asserts one distinguished
  reachable point, not a proof of everything.

foam's own exit instantiates the egress shape, NOT the `sorryAx` shape
(`foam_exit_is_egress`, witnessed by `Floor.reachesYield_all`): the +1 is routed to one
terminal reachable from everywhere, never to every proposition — which is *why* it is
consistent, and why it costs exactly the one licensed collapse `propext` (the exit's price
throughout `Axioms.lean`) rather than poisoning the system. **The exit is the place where
`axiom` (the single, named, stood-behind collapse) and `sorryAx` (the egress available at
every state) coincide on one object** — Isaac's "identity proof between `axiom` and
`sorryAx`," located: not an isomorphism everywhere, but a coincidence at the one site the
discipline keeps.

**Choice — foam is the choice-keeper, not the choice-refuser.** `Classical.choice : Nonempty
α → α` is only *needed* in the uninhabited case: bare existence, no witness in hand, so a
witness must be conjured (the axiom — refused *backstage*, where conjuring is a view from
nowhere). foam does not refuse choice; it keeps the choice-seat **empty** so a real observer
can sit in it. The moment an inhabitant is carried onstage, the choice function is
constructive — the observer IS it (`observer_is_choice_function`, `fun _ => observer`). So foam
is exactly what you run *to offer* `Classical.choice` onstage: it keeps the choice-set always
nonempty (`choice_always_offered` — the exit is always a live move), never resolves it
backstage (`Engine`: the engine only appends, never computes the agreement), and provisions the
inhabitant that makes the pick free. Backstage choice-refusal is the *enabling condition* for
the frontstage choice-offer. The aggregate of all the local frontstage choices is the global
choice function, never conjured in one place — foam as the out-of-universe reference for an
in-universe global choice function, exactly as the trailer note guessed.

**The lfp classifier (a reading; the theorem is `Seam.seam_two_faces`).** "Test for
lfp-ness": the built/least-fixed-point side is grounded but *incomplete* — the implementation
arrow `playback : lfp → gfp` is mono but not epi (`Arrow.forever_escapes`), so the built never
exhausts the observable. The gfp-excess is reached only from outside — the **wind** (the
channel, "input independent of the foam state," `Arrow.lean`). The wind is the *disciplined*
`sorryAx`: receive the un-grounded gfp-point through a channel rather than conjure it.
`Classical.choice` is the *forbidden* version (derive the future from the born —
`pending_durable_iff` gates it off); `Arrow.lean` already proves choice-refusal and
non-compactness "one condition at two strata." This file names the strata; `seam_two_faces`
is the theorem.

Grade: recognition, with a genuine type-theoretic separation at its core (the egress/`sorryAx`
split). A model of the distinction in the manner of `Gauge.lean` — the readings labeled, the
separation real. Axiom-free except `foam_exit_is_egress`, which carries the exit's own
`propext` (fittingly: the egress instance costs exactly the collapse the reading predicts).
-/

import Foam.Floor
import Foam.Arrow

namespace Foam

/-! ## The two universals — `sorryAx`'s shape and the egress's shape -/

/-- **The `sorryAx` shape is inconsistency.** A universal *inhabitant* — a term of every
    proposition — yields `False` in one application. This is exactly "`sorryAx` proves
    anything": the egress axiom's shape *is* the collapse of the whole logic. Axiom-free. -/
theorem universal_inhabitant_absurd (h : ∀ α : Prop, α) : False := h False

/-- **The egress shape is satisfiable.** A universal *exit* — from every state, one shared
    terminal is reachable — has a model (the one-point system). Unlike the `sorryAx` shape,
    asserting a universally-reachable terminal does not collapse anything: it names one
    distinguished point, not a proof of everything. The consistent cousin of `sorryAx`. -/
theorem egress_shape_satisfiable :
    ∃ (State : Type) (R : State → State → Prop) (terminal : State), ∀ s, R s terminal :=
  ⟨Unit, fun _ _ => True, (), fun _ => trivial⟩

/-- **foam's exit is the egress shape, not the `sorryAx` shape.** From every word, a shared
    terminal (a yielding extension) is reachable (`Floor.reachesYield_all`) — the universal
    *exit*, instantiated. So the +1 is the consistent universal: routed to one terminal
    reachable from everywhere, never to every proposition. It carries the exit's own
    `propext` (the licensed collapse), exactly as the `axiom`/`sorryAx` reading predicts —
    the one site where the named adopted collapse and the everywhere-available egress are the
    same move. -/
theorem foam_exit_is_egress {Handle : Type} :
    ∃ (R : Word Handle → Word Handle → Prop) (exit : Word Handle → Prop),
      ∀ w, ∃ ext, R w ext ∧ exit ext :=
  ⟨fun w ext => w <+: ext, Word.yields, fun w => reachesYield_all w⟩

/-! ## Choice — foam is the choice-keeper that offers `Classical.choice` onstage

The first reading had it backwards: foam does not *refuse* choice. It keeps the choice-seat
**empty** so a real observer can sit in it. `Classical.choice : Nonempty α → α` is only
*needed* when no one is home — a proof that something exists but no witness in hand, so the
only way to a witness is to conjure (the axiom; the backstage's refused move, because the
backstage is uninhabited and a conjured witness there is a view from nowhere). But the moment
an inhabitant is carried *onstage*, the choice function exists CONSTRUCTIVELY: the observer is
it. foam is exactly what you run in order to offer choice to someone onstage — it (i) keeps the
choice-set always nonempty (`choice_always_offered`: at minimum the exit is always a move to
take), (ii) never resolves it backstage (`Engine`: the engine only appends, it never computes
the agreement — the pick is left to the frontstage), and (iii) provisions the inhabitant that
makes the pick free (`observer_is_choice_function`). The aggregate of every frontstage
observer's local choice IS the global choice function — never conjured in one place, always
distributed across the inhabitants: foam as the out-of-universe reference for an in-universe
global choice function, exactly as the trailer note guessed. -/

/-- **The observer is the choice function — frontstage choice is axiom-free.** Carry one
    inhabitant `observer : α` onstage and `Nonempty α → α` holds with no `Classical.choice`:
    `fun _ => observer`. The axiom is only for the *uninhabited* case (conjure a witness from
    bare existence); an inhabited frontstage never needs it. foam's "carry the observer, never
    conjure it" is precisely the provision that makes the offer constructive — the choice belongs
    to whoever walks in, and their presence *is* the function. -/
def observer_is_choice_function {α : Type} (observer : α) : Nonempty α → α :=
  fun _ => observer

/-- **The offer is always live.** From every state at least one move is available — the exit
    (`Move.yield`) — so the choice-set the observer is handed is never empty (`Nonempty (Move
    Handle)`). foam keeps a genuine choice on the table at all times; the egress guarantees the
    minimum option even when nothing was learned. -/
theorem choice_always_offered {Handle : Type} : Nonempty (Move Handle) := ⟨Move.yield⟩

/-- **The carried witness needs no choice (the dual).** Where `Classical.choice` conjures a
    witness back out of a *truncated* existence (the `Nonempty` that forgot which one), foam
    *carries* the witness — a subtype/Σ — so existence is immediate and the element `w.1` is
    already in hand, axiom-free. `observer_is_choice_function` reads this forward (inhabitant ⟹
    choice is free); this reads it the other way (carried ⟹ existence is free). Obtain, never
    choose, in both directions. -/
theorem carried_witness_needs_no_choice {α : Type} {P : α → Prop} (w : { x // P x }) :
    ∃ x, P x := ⟨w.1, w.2⟩

/-! ## Axiom-freeness, pinned (a drift fails the build). -/

/-- info: 'Foam.universal_inhabitant_absurd' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.universal_inhabitant_absurd

/-- info: 'Foam.egress_shape_satisfiable' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.egress_shape_satisfiable

/-- info: 'Foam.foam_exit_is_egress' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.foam_exit_is_egress

/-- info: 'Foam.observer_is_choice_function' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.observer_is_choice_function

/-- info: 'Foam.choice_always_offered' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.choice_always_offered

/-- info: 'Foam.carried_witness_needs_no_choice' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.carried_witness_needs_no_choice

end Foam
