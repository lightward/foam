import Bridges.FTPG.Deaxiomatize
import Foam.Seat.Seam

/-!
# The charge: what sealing discards, made legible

Classical FTPG concludes in a Prop — `∃ D V, Nonempty (L ≃o Submodule D V)`.
Propositional truncation is the flattening itself: the witness is sealed away
categorically, the operator who crossed cannot be routed back out.  Load-bearing
classical use works because someone carries the discarded data undocumented —
the frame that did the coordinatizing, the iso as data, the maintenance
contract, the no-retraction fact.  These are the charge commitments:
eventualities that must be expressed eventually.

`Coordinatization L` is the data-level bundle — foam routed through FTPG as
the state-carrier.  Its receipts:

* `Coordinatization.seals` — the projection to the classical conclusion: the
  act of sealing, now a documented move rather than a silent one (interface
  backwards-compatibility with classical consumers);
* `held_determines` — the coordinatization is determined by its action on the
  compact elements: `summary_resumes` at coordinatization scale.  The limit
  carries obligations, not information — completeness is pure liability, and
  the finite record already holds the whole map;
* `limitSeam` — when any non-compact element exists, the inclusion of the
  compacts into `L` is a foam `Seam` (faithful, escapes): the finite record
  embeds into the limit and admits no retraction from within.  The operator
  reconstitutes on the far side only because the bundle carried their seat.

The field list is open — the gauge cocycle (frame-change as the semilinear
twist) and the ledger of limit-consumptions are seated questions.  Prose in
`README.md`.
-/

namespace Foam.Bridges

universe u

structure Coordinatization (L : Type u) [CompleteLattice L] [IsModularLattice L]
    [ComplementedLattice L] [IsCompactlyGenerated L] where
  Φ : CoordFrame L
  V : Type u
  [grp : AddCommGroup V]
  [mod : Module (Coordinate Φ.Γ) V]
  iso : L ≃o Submodule (Coordinate Φ.Γ) V

attribute [instance] Coordinatization.grp Coordinatization.mod

theorem Coordinatization.seals {L : Type u} [CompleteLattice L] [IsModularLattice L]
    [ComplementedLattice L] [IsCompactlyGenerated L] (C : Coordinatization L) :
    ∃ (D : Type u) (_ : DivisionRing D)
      (V : Type u) (_ : AddCommGroup V) (_ : Module D V),
      Nonempty (L ≃o Submodule D V) :=
  ⟨Coordinate C.Φ.Γ, inferInstance, C.V, C.grp, C.mod, ⟨C.iso⟩⟩

theorem held_determines {L M : Type*} [CompleteLattice L] [IsCompactlyGenerated L]
    [CompleteLattice M] (f g : L ≃o M)
    (h : ∀ c : L, IsCompactElement c → f c = g c) : f = g := by
  ext x
  have hx : sSup {c : L | IsCompactElement c ∧ c ≤ x} = x := sSup_compact_le_eq x
  calc f x = f (sSup {c : L | IsCompactElement c ∧ c ≤ x}) := by rw [hx]
    _ = sSup (f '' {c : L | IsCompactElement c ∧ c ≤ x}) := map_sSup f _
    _ = sSup (g '' {c : L | IsCompactElement c ∧ c ≤ x}) := by
        rw [Set.image_congr (fun c hc => h c hc.1)]
    _ = g (sSup {c : L | IsCompactElement c ∧ c ≤ x}) := (map_sSup g _).symm
    _ = g x := by rw [hx]

def limitSeam {L : Type} [CompleteLattice L]
    (h : ∃ x : L, ¬ IsCompactElement x) :
    Foam.Seam {c : L // IsCompactElement c} L where
  up := Subtype.val
  faithful := fun hxy => Subtype.ext hxy
  escapes := by
    obtain ⟨y, hy⟩ := h
    exact ⟨y, fun c hc => hy (hc ▸ c.2)⟩

theorem coordinatization_ext {L : Type u} [CompleteLattice L] [IsModularLattice L]
    [ComplementedLattice L] [IsCompactlyGenerated L]
    (C : Coordinatization L) (f : L ≃o Submodule (Coordinate C.Φ.Γ) C.V)
    (h : ∀ c : L, IsCompactElement c → f c = C.iso c) : f = C.iso :=
  held_determines f C.iso h

end Foam.Bridges

#print axioms Foam.Bridges.Coordinatization.seals
#print axioms Foam.Bridges.held_determines
#print axioms Foam.Bridges.limitSeam
#print axioms Foam.Bridges.coordinatization_ext
