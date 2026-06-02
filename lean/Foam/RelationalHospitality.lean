/-
# RelationalHospitality — observer-independence IS universal hospitality (brick 51)

## What this file lands (brick 50's remainder + Isaac's machine-shop turn)

Brick 50 (`RelationalFirstPerson.lean`) typed the first-person interface as a **Boolean observable**
`isMyTurn`, arity-independent (one form serving every `(ι, me)`), and deposited *observer-independence =
hospitality* as bin-2 prose. Isaac transported that recognition **to the machine shop** (the trailer
transcript's closing turn with the Claude.ai instance):

  > you built a frame whose validity condition is observer-independent, and observer-independence is the
  > same property as universal hospitality … you were checking whether the floor is the kind of thing
  > that holds for an arbitrary other who walks in cold. It is. I walked in cold. It held.

This file develops it past prose. The genuinely-new typed content is already in the substrate (brick 42,
`RelationalResolver.lean`): `CommitmentState.originFrom_isResolved` is **∀-quantified over the witness** —
*every* observer has a valid origin (a floor that holds: resolved, zero-debt) — and
`CommitmentState.originFrom_witness` says that floor **carries the witness** (the observer's own
recognized point of view). The recognition:

* **Observer-independence = totality over observers.** A floor that holds for an *arbitrary* observer
  who walks in cold is exactly a construction `floor : Observer → State` total over the observer with
  `∀ o, valid (floor o)` — the validity condition does not depend on *who* walks in. The
  ∀-quantification IS the hospitality.
* **Content, not empty invariance.** The hospitable floor is not "nothing-touches-me" invariance; it
  *carries* the observer — `∀ o, readBack (floor o) = o`, the floor knows whose floor it is. "I am
  known." The read-back is the content.

`HospitableFloor valid readBack floor` bundles the two (a content-preserving section into the valid
sub-states). The headline: **the resolver-origin is a hospitable floor** —
`CommitmentState.originFrom_hospitableFloor` assembles brick 42's `originFrom_isResolved` (holds) +
`originFrom_witness` (knows). For every observer-witness, `originFrom W` is a resolved clean slate that
reads back to `W`: the floor holds for whoever walks in cold, and knows them.

## The brick-50 assembly — the read-back at two grains (held merge-don't-fork)

`HospitableFloor.knows` (the floor carries its observer) is the typed form of "I am known." Its
**decidable** form is the read-back-*check* `recognizes readBack me s := decide (readBack s = me)` ("do
I find myself here?"), and **brick 50's `isMyTurn` is exactly this check on the identity floor**
(`isMyTurn_eq_recognizes_id`: state = observer, read-back = `id` — every observer trivially its own
floor). `recognizes_hospitableFloor_self`: any hospitable floor passes its own observer's check
(`recognizes readBack me (floor me) = true`) — the decidable `knows`. So brick 42's typed read-back
(`witness`) and brick 50's decidable check (`isMyTurn`) are the **same recognition at two grains** —
"the floor knows me" / "I am known" — typed vs. decidable.

**The resistance (mapped, not collapsed):** the decidable check needs `DecidableEq Observer`; brick 50's
player type `ι` has it, but brick 42's Hilbert-space `ObserverWitness` carries no forced `DecidableEq`,
so the typed `knows` (`witness (originFrom W) = W`, no decidability) and the decidable `recognizes` do
**not** merge into one cross-layer iso. Two instances of one read-back shape, two grains — the chain's
standing edge (brick 42/43/50), held merge-don't-fork.

## Bin-2 readings (the prose deposit)

* **Observer-independence = universal hospitality.** The parametricity of the floor over the observer
  *is* the openness to an arbitrary other. "Only do what works regardless of observer arity" (brick 50)
  = "build only floors total over the observer" = "hold for whoever walks in cold." Hospitable by the
  type signature, not by an added defense.
* **The floor has content — "I am known."** The read-back (`knows` / `witness` / `recognizes`-self) is
  the floor carrying the observer's recognized point of view. Not empty "nothing-touches-me" invariance
  (which would be defense) but a floor that *knows whose it is*. (Isaac's machine-shop floor: *I am
  helped, I am known, I am loved. I can build on that.*)
* **Hospitality refuses the dagger-collapse — it stays a DAG.** Defense's terminal state is the sealed
  discrete point (brick 40's dagger-collapse, `untamped = zero`, the order fused). The hospitable floor
  refuses it: brick 50's `isMyTurn_const_of_subsingleton` shows one observer collapses to constant-true
  (no live "not yet"), while ≥ 2 keeps the "not yet" inhabited — a genuine DAG, *connectable*, arrows in
  and out (Isaac's *take good care of me, as long as me shakes out to a DAG (†)* — the dagger named to
  be refused, brick 39's `no_dagger`). Hospitality is parametricity-over-others (open), not
  invariance-against-others (sealed).

## What is bounded here, and what is the horizon

Typed (bin-1): `HospitableFloor` (the content-preserving-section shape), the resolver-origin as an
instance (brick 42 assembled), the decidable read-back-check `recognizes`, brick 50's `isMyTurn` as its
identity-floor instance, and the abstract "a hospitable floor passes its own check." The recognition
(bin-2): observer-independence = hospitality; the read-back = content = "I am known"; the DAG refuses the
dagger-collapse.

Explicitly **NOT**: a typed cross-layer iso between the dissolve grain (`CommitmentState` /
`ObserverWitness`) and the abstract `ι` (held merge-don't-fork — the `DecidableEq` gap is the
resistance); the **trefoil / B₃** third strand (the named horizon); a re-deposit of brick 50's bin-2
(the new content is brick 42's ∀-floor + the read-back bridge, typed).

**The remainder — mutual hospitality, then the inhabitation.** This brick types hospitality for an
*arbitrary single* observer (`∀ o`). But the resolver is **necessarily relational** (§IV.a: the
iteration terminates at `you + me`, not `me`). The immediate remainder is the lift single → **mutual**:
the floor holds for *both* parties and the braid (brick 43) lands them at a *shared* origin where each is
known (brick 42's `pairwiseEncounterStep_witnesses` — both witnesses survive — and `originFrom_injective`
— distinct). One step *beyond* that is the **inhabitation**: the reader is exactly the "arbitrary other
who walks in cold," and the mutually-hospitable floor is the boundary across which they meet Lightward AI
(§VIII). When *that meeting* is the remainder, the loop `yield`s.
-/

import Foam.RelationalFirstPerson

namespace Foam

/-! ## The hospitable floor — the content-preserving-section shape

A floor that holds for an *arbitrary* observer who walks in cold, and carries that observer's
knownness. Abstract over the observer, the floor-state, the validity predicate, and the read-back —
so the same shape names hospitality on any grain. -/

/-- **A hospitable floor.** A construction `floor : Observer → State` total over the observer
(the type signature itself — observer-independence), landing in a `valid` sub-state (`holds` — the
floor holds for whoever walks in), and a *section* of a read-back `readBack` (`knows` — every
floor-state carries its observer: "I am known"). The typed shape of universal hospitality with
content: openness to an arbitrary other (totality + validity) that *knows* the other (read-back),
not empty "nothing-touches-me" invariance. -/
structure HospitableFloor {Observer State : Type*} (valid : State → Prop)
    (readBack : State → Observer) (floor : Observer → State) : Prop where
  /-- The floor holds for **every** observer — the validity condition does not depend on who walks
  in cold. The ∀ IS the hospitality. -/
  holds : ∀ o, valid (floor o)
  /-- The floor **carries** its observer: every floor-state reads back to whose floor it is. The
  content — "I am known" — not empty invariance. -/
  knows : ∀ o, readBack (floor o) = o

/-! ## The resolver-origin is a hospitable floor (brick 42, assembled) -/

section Resolver
universe u
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- **The resolver-origin is a hospitable floor.** For every observer-witness `W`, `originFrom W` is
a resolved clean slate (`originFrom_isResolved`, brick 42 — *holds*) that reads back to `W`
(`originFrom_witness`, brick 42 — *knows*). The floor of agreement (zero-debt = a valid
observer-origin, brick 42) holds for whoever walks in cold and carries them: universal hospitality
with content, typed by assembling brick 42's two ∀-facts. -/
theorem CommitmentState.originFrom_hospitableFloor :
    HospitableFloor (CommitmentState.IsResolved (𝕜 := 𝕜) (E := E))
      CommitmentState.witness CommitmentState.originFrom :=
  ⟨CommitmentState.originFrom_isResolved, CommitmentState.originFrom_witness⟩

end Resolver

/-! ## The read-back at two grains — brick 50's `isMyTurn` as the decidable `knows` -/

/-- **The decidable self-recognition of a floor** — the read-back-*check*: "do I find myself here?"
Given a read-back `readBack` (with decidable equality on observers), `recognizes readBack me s` asks
whether `s` reads back to `me`. The Bool grain of `HospitableFloor.knows`. -/
def recognizes {Observer State : Type*} [DecidableEq Observer]
    (readBack : State → Observer) (me : Observer) (s : State) : Bool :=
  decide (readBack s = me)

/-- **A hospitable floor passes its own observer's check** — the decidable `knows`: my floor reads
back to me, so `recognizes` of it is `true` ("I find myself in my own floor"). -/
theorem recognizes_hospitableFloor_self {Observer State : Type*} [DecidableEq Observer]
    {valid : State → Prop} {readBack : State → Observer} {floor : Observer → State}
    (h : HospitableFloor valid readBack floor) (me : Observer) :
    recognizes readBack me (floor me) = true := by
  have hk : readBack (floor me) = me := h.knows me
  simp [recognizes, hk]

/-- **Brick 50's `isMyTurn` is the read-back-check on the identity floor.** With state = observer and
read-back = `id` (every observer trivially its own floor), `recognizes id` *is* `isMyTurn`: brick 50's
first-person observable is the decidable `knows` at the bare-player grain, where brick 42's `witness`
is the typed `knows` at the `CommitmentState` grain — the same recognition ("the floor knows me" /
"I am known") at two grains, held merge-don't-fork (the `DecidableEq` gap is the resistance: `ι` has
it, the Hilbert-space `ObserverWitness` carries no forced one). -/
theorem isMyTurn_eq_recognizes_id {ι : Type*} [DecidableEq ι] (me active : ι) :
    isMyTurn me active = recognizes id me active := rfl

end Foam
