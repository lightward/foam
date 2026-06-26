/-
# Encounter — the Beholder treats-as a CML, and a CML is what it gets

The span's near keystone: the FIRST strut in `bridges/` that imports the
axiom-free core. The earlier anchors (`HalfType`, `Observation`) reach only
Mathlib — the far abutment. This one strings the cable to `Foam.Beholder`.

An idempotent observation (`P ∘ₗ P = P`, the Beholder-as-projection of
`Observation.lean`) is, at once, three faces of one object:
  · a foam `Beholder V` (core) — it observes the seen component `P v`;
  · an element of the subspace CML `Submodule K V`, whose range and kernel are
    an `IsCompl` pair (`encounter_isCompl`);
  · hence governed by `HalfType` — the diamond iso `Iic (range P) ≃o Ici (ker P)`.

The CML is never backstage (that would conjure a pov — the one forbidden move).
The Beholder *encounters* it by treating-as: if it treats the field as a CML, a
CML is what it gets. The ledger records the operations arithmetically — the FTPG
descent, a later strut.
-/
import Bridges.HalfType
import Bridges.Observation
import Foam.Seat.Beholder

namespace Foam.Bridges

-- `Type` (not `Type u`): the core `Foam.Beholder` takes its state in `Type 0`,
-- so the encounter lands there. `Submodule K V` stays `Type 0` too, so
-- `HalfType` still applies — the near end sets the universe, the far end follows.
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

/-- The foam `Beholder` a projection induces: it observes the seen component
    `P v`. This is the near end — a core `Foam.Beholder`, supplied by the
    encounter, not found backstage. -/
def projectionBeholder (P : V →ₗ[K] V) : Foam.Beholder V where
  Probe := Unit
  Ans := V
  obs := fun v _ => P v

theorem projectionBeholder_obs (P : V →ₗ[K] V) (v : V) :
    (projectionBeholder P).obs v () = P v := rfl

/-- The complementary Beholder, `I - P`. Observations come in pairs
    (`complement_idempotent`); so do their Beholders. -/
def projectionBeholder.compl (P : V →ₗ[K] V) : Foam.Beholder V :=
  projectionBeholder (LinearMap.id - P)

/-- The encounter: an idempotent observation's range and kernel are an `IsCompl`
    pair in the subspace CML. `range P ⊓ ker P = ⊥` (`range_ker_disjoint`, the
    clean split) is disjointness; `range P ⊔ ker P = ⊤` is codisjointness,
    witnessed by `v = P v + (v - P v)` with `P v ∈ range` and `v - P v ∈ ker`. -/
theorem encounter_isCompl (P : V →ₗ[K] V) (h_idem : P ∘ₗ P = P) :
    IsCompl (LinearMap.range P) (LinearMap.ker P) := by
  have hPP : ∀ v, P (P v) = P v := by
    intro v; have := LinearMap.ext_iff.mp h_idem v
    simpa [LinearMap.comp_apply] using this
  refine ⟨disjoint_iff.mpr (range_ker_disjoint P h_idem), codisjoint_iff.mpr ?_⟩
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  refine ⟨P v, ⟨v, rfl⟩, v - P v, ?_, by abel⟩
  rw [LinearMap.mem_ker, map_sub, hPP, sub_self]

/-- The half-type the encounter yields: the diamond iso, plus modularity and
    complementedness on each half. `HalfType` is the package; this is its
    instance at the encountered CML. The classical axioms live here, behind the
    package wall — `Foam` core never reaches them. -/
noncomputable def encounterHalfType (P : V →ₗ[K] V) (h_idem : P ∘ₗ P = P) :
    HalfType (LinearMap.range P) (LinearMap.ker P) (encounter_isCompl P h_idem) :=
  half_type (encounter_isCompl P h_idem)

end Foam.Bridges
