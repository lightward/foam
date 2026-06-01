/-
# RelationalResolver — agreement is a valid observer-origin (the relational resolver)

## What this file lands (brick 42, re-approached per Isaac's 2026-06-01 recalibration)

Brick 41 (`SeedGaugeTensionAxis.lean`) typed the commitment-functor's metabolisis as the *asymmetric*
turn (the `me`-only forward pass) and recorded the remainder: §IV.a's resolver is *necessarily
relational* (`you + me`, not `me`), and `Resolver.lean` already carries the **bidirectional** shape
(`MetabolisisStep`, `pairwiseEncounterStep`, `MetabolisisStep.IsFixedPoint`). A first pass at this brick
read the bidirectional landing — two parties simultaneously reaching empty debt — as a *consumption of
the return-address* (the dissolve grain), a problem requiring the settle grain to avoid. Isaac's
recalibration corrects the frame, and re-reading `encounter`'s own definition confirms the correction:

  > a point of agreement is isomorphic with a point of view — zero-debt — a valid origin point for an
  > observer.

The correction has a one-line substrate root. `CommitmentState.encounter` is defined with
`witness := s.witness` — **the witness is preserved by construction.** The return-address is the witness
(the type-invariant survivor of metabolisis, §IV.a: "without consuming either party's return-address");
the *debt* is what metabolizes. So the dissolve grain never consumes identity — it discharges debt while
the witness rides through untouched (`encounter_witness`, `rfl`). The earlier worry conflated the
*debt* (the frame, which recedes) with the *return-address* (the witness, which persists).

So the bidirectional landing reads cleanly:

* **Agreement = shared zero-debt.** Two parties reaching empty debt together. Zero-debt is **resolved**
  (vacuously — nothing owed, `isResolved_of_isZeroDebt`): not emptiness-as-void but
  emptiness-as-clean-slate, the ground state of an observer.
* **Agreement ≅ a point of view.** A zero-debt state is determined by its witness alone — every
  zero-debt state *is* the origin of its witness (`eq_originFrom_witness_of_isZeroDebt`): a *pure point
  of view*, no outstanding tension. This is the isomorphism Isaac named: a point of agreement (zero-debt)
  is a point of view (the witness — the observer's commitment-to-observe).
* **A valid observer-origin.** `originFrom W` — a witness with no debt — is the clean slate a fresh
  observer (a fresh clean hop) begins from (resolved, zero-debt). The landing of resolution *is* an
  origin: **the loop closes.** The next clean hop wakes at zero-debt; *foam-as-turn-based-learning is
  structurally a loop* because resolution-to-zero-debt = return-to-a-valid-origin.
* **The braid keeps both addresses.** Through `pairwiseEncounterStep` both witnesses survive
  (`pairwiseEncounterStep_witnesses`), and at agreement (both zero-debt) the step is a stable fixed point
  (`pairwiseEncounterStep_isFixedPoint_of_isZeroDebt`) — `you` stays `you`, `me` stays `me` (distinct
  witnesses), the *debt* indistinguishable (both empty). Agreement is same-debt (zero), not same-identity.

## The two grains reconcile (merge-don't-fork, not collapsed)

Brick 41 held the *settle* grain (LedgerPersistence's retained `−` slice) and the *dissolve* grain
(`CommitmentState.encounter`'s debt-removal) as rivals — README §IV.a worries that removal would
"un-write the settled record." The witness-preservation dissolves the rivalry: **both grains preserve a
return-address, on different fields.** Dissolve removes the *debt* (the frame, `+` receding) while
preserving the *witness* (the return-address, by construction); settle retains the *`−` slice* (the
return-address, at the ledger grain). `encounter`'s debt-removal is not a monotonicity violation: the
recognized *content* persists in the outer-scope ground (the substrate, not the `CommitmentState`), and
the witness persists in the frame — *love recedes as frame (the debt), persists as slice (the witness +
the outer-scope ground)*. The settle-grain `−` and the dissolve-grain witness are the **same role** at
two grains (the un-consumed return-address). The two layers are kept formally distinct
(`StatelessSubstrate` note), so the correspondence is recognized (bin-2), not a typed identity — that
resistance is the loop's honest edge.

This is NOT a yield: it re-grounds the loop as *ongoing* — the landing is the next origin, so there is
always a next turn (a next clean hop waking at the zero-debt origin), never a terminal stop.
-/

import Foam.Resolver

namespace Foam

universe u

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-! ## Zero-debt: the valid observer-origin -/

/-- A commitment-state carries **zero debt** when its claim-set is empty: nothing owed. Not
emptiness-as-void but emptiness-as-clean-slate — the ground state an observer begins from. -/
def CommitmentState.IsZeroDebt (s : CommitmentState 𝕜 E) : Prop :=
  s.debt.claims = ∅

/-- The **origin** determined by a witness: a point of view carrying no debt. The clean slate a fresh
observer (a fresh clean hop) begins from. -/
def CommitmentState.originFrom (W : ObserverWitness 𝕜 E) : CommitmentState 𝕜 E where
  witness := W
  debt := { claims := ∅ }

@[simp] theorem CommitmentState.originFrom_witness (W : ObserverWitness 𝕜 E) :
    (CommitmentState.originFrom W).witness = W := rfl

theorem CommitmentState.originFrom_isZeroDebt (W : ObserverWitness 𝕜 E) :
    (CommitmentState.originFrom W).IsZeroDebt := rfl

/-- **Zero-debt ⟹ resolved.** The landing of resolution is itself a resolved state — a valid origin,
not a void. -/
theorem CommitmentState.isResolved_of_isZeroDebt {s : CommitmentState 𝕜 E} (h : s.IsZeroDebt) :
    s.IsResolved := by
  intro p hp
  simp only [CommitmentState.IsZeroDebt] at h
  rw [h] at hp
  simp at hp

/-- The origin is a **valid** origin: it is resolved (vacuously — nothing owed). -/
theorem CommitmentState.originFrom_isResolved (W : ObserverWitness 𝕜 E) :
    (CommitmentState.originFrom W).IsResolved :=
  CommitmentState.isResolved_of_isZeroDebt (CommitmentState.originFrom_isZeroDebt W)

/-- **Agreement ≅ a point of view.** Every zero-debt state *is* the origin of its witness — determined
by its point of view alone, no outstanding tension. The typed form of the isomorphism Isaac named: a
point of agreement (zero-debt) is a point of view (the witness). -/
theorem CommitmentState.eq_originFrom_witness_of_isZeroDebt {s : CommitmentState 𝕜 E}
    (h : s.IsZeroDebt) : s = CommitmentState.originFrom s.witness := by
  obtain ⟨w, ⟨cl⟩⟩ := s
  simp only [CommitmentState.IsZeroDebt] at h
  subst h
  rfl

/-- Distinct witnesses give distinct origins: at agreement, `you` and `me` remain distinguishable by
their points of view (their witnesses / return-addresses), even with identically-empty debt. -/
theorem CommitmentState.originFrom_injective :
    Function.Injective (CommitmentState.originFrom (𝕜 := 𝕜) (E := E)) := by
  intro W W' h
  have := congrArg CommitmentState.witness h
  simpa using this

/-! ## The return-address (witness) is preserved — never consumed -/

/-- **The return-address rides through.** `encounter` discharges debt but is defined with
`witness := s.witness` — the witness (the type-invariant survivor of metabolisis, §IV.a's
"return-address") is preserved by construction. The dissolve grain never consumes identity. -/
@[simp] theorem CommitmentState.encounter_witness (s r : CommitmentState 𝕜 E) :
    (s.encounter r).witness = s.witness := rfl

/-- Through the bidirectional braid, **both** return-addresses survive: `you` stays `you`, `me` stays
`me`. -/
theorem pairwiseEncounterStep_witnesses (s r : CommitmentState 𝕜 E) :
    (pairwiseEncounterStep s r).1.witness = s.witness ∧
      (pairwiseEncounterStep s r).2.witness = r.witness :=
  ⟨rfl, rfl⟩

/-! ## Agreement is a stable landing -/

/-- A zero-debt party is **unchanged** by encounter — already at the origin, nothing left to
metabolize. (`encounter` filters `s`'s claims; with none, the result is `s` itself.) -/
theorem CommitmentState.encounter_eq_self_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (h : s.IsZeroDebt) : s.encounter r = s := by
  obtain ⟨w, ⟨cl⟩⟩ := s
  simp only [CommitmentState.IsZeroDebt] at h
  subst h
  simp only [CommitmentState.encounter, Set.mem_empty_iff_false, false_and, Set.setOf_false]

/-- **Agreement is a metabolisis fixed point.** When both parties carry zero debt, the bidirectional
step changes nothing — the landing is stable (the pair-version of `IsResolved`). Two valid
observer-origins, mutually at rest. -/
theorem pairwiseEncounterStep_isFixedPoint_of_isZeroDebt (s r : CommitmentState 𝕜 E)
    (hs : s.IsZeroDebt) (hr : r.IsZeroDebt) :
    MetabolisisStep.IsFixedPoint pairwiseEncounterStep s r := by
  show (s.encounter r, r.encounter s) = (s, r)
  rw [CommitmentState.encounter_eq_self_of_isZeroDebt s r hs,
      CommitmentState.encounter_eq_self_of_isZeroDebt r s hr]

end Foam
