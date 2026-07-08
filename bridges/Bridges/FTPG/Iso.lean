import Bridges.FTPG.Carrier
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projectivization.Subspace

/-!
# Gap B: the coordinatization order-isomorphism `L ≃o Submodule D V`

This file isolates the *residual* geometric content of the second fundamental theorem of
projective geometry (Veblen–Young coordinatization) behind a small set of fully-general,
**sorry-free** reduction lemmas.

The strategy:

* `orderIso_of_mono_reflect_surj` — a monotone, order-reflecting, surjective map between a
  partial order and a preorder is an order isomorphism.  No completeness needed on the domain
  (so it applies to the foam lattice `L`, which is only `Lattice + BoundedOrder`).
* `coordSpanFwd` — the forward map `x ↦ sSup { pt p | p atom, p ≤ x }`, the "span of the
  coordinate points below `x`".
* `nonempty_orderIso_of_pointMap` — **the heart**: given a point map `pt : Atoms L → M`
  (`M` a complete atomistic lattice) such that
    (closure preservation) `pt p ≤ coordSpanFwd pt x → p ≤ x`, and
    (surjectivity)         `coordSpanFwd pt` is surjective,
  we obtain `Nonempty (L ≃o M)`.

  These two hypotheses are *exactly* the residual: the point map must be a closure-preserving
  bijection of the atoms of `L` onto the projective points of `V`.  Everything else
  (monotonicity, order-reflection at non-atom level, injectivity, construction of the inverse)
  is discharged here from the atomistic structure via Mathlib's `le_iff_atom_le_imp`.

The Mathlib lever `Projectivization.Subspace.submodule : Subspace D V ≃o Submodule D V` makes the
final `Subspace ⇝ Submodule` translation free (`subspace_to_submodule`).

The abstract lemmas use only `propext / Classical.choice / Quot.sound`; they do not depend on
the `DivisionRing (Coordinate Γ)` construction, so they are honestly axiom-clean.
-/

namespace Foam.Bridges

universe u

/-! ### Abstract reduction (fully general, sorry-free) -/

section Abstract

/-- A monotone, order-reflecting, surjective map between a partial order and a preorder is an
order isomorphism.  Crucially the **domain need not be complete** — we build the inverse via
`Equiv.ofBijective` (choice) and recover its monotonicity from order-reflection. -/
theorem orderIso_of_mono_reflect_surj {A B : Type*} [PartialOrder A] [Preorder B]
    (f : A → B) (hmono : Monotone f)
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b)
    (hsurj : Function.Surjective f) : Nonempty (A ≃o B) := by
  have hinj : Function.Injective f := fun a b h =>
    le_antisymm (hrefl _ _ h.le) (hrefl _ _ h.ge)
  let e : A ≃ B := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e.toOrderIso hmono ?_⟩
  intro x y hxy
  apply hrefl
  have hx : f (e.symm x) = x := e.apply_symm_apply x
  have hy : f (e.symm y) = y := e.apply_symm_apply y
  rw [hx, hy]
  exact hxy

variable {L : Type*} [PartialOrder L] [OrderBot L] [IsAtomistic L]
variable {M : Type*} [CompleteLattice M] [IsAtomistic M]

/-- The forward map: `x ↦ sSup { pt p | p an atom of `L`, p ≤ x }`. -/
noncomputable def coordSpanFwd (pt : {p : L // IsAtom p} → M) (x : L) : M :=
  sSup {m : M | ∃ p : {p : L // IsAtom p}, (p : L) ≤ x ∧ pt p = m}

omit [IsAtomistic L] [IsAtomistic M] in
theorem coordSpanFwd_mono (pt : {p : L // IsAtom p} → M) : Monotone (coordSpanFwd pt) := by
  intro x y hxy
  apply sSup_le_sSup
  rintro m ⟨p, hp, rfl⟩
  exact ⟨p, hp.trans hxy, rfl⟩

omit [IsAtomistic L] [IsAtomistic M] in
theorem coordSpanFwd_point_le (pt : {p : L // IsAtom p} → M)
    {p : {p : L // IsAtom p}} {x : L} (hp : (p : L) ≤ x) :
    pt p ≤ coordSpanFwd pt x :=
  le_sSup ⟨p, hp, rfl⟩

/-- **The heart of gap B.**  A point map whose forward span (i) reflects atom-containment
(closure preservation) and (ii) is surjective, induces an order isomorphism `L ≃o M`.

The two hypotheses are the entire residual geometric content; everything else is discharged
here from `IsAtomistic` via `le_iff_atom_le_imp`. -/
theorem nonempty_orderIso_of_pointMap (pt : {p : L // IsAtom p} → M)
    (hclosed : ∀ (p : {p : L // IsAtom p}) (x : L),
        pt p ≤ coordSpanFwd pt x → (p : L) ≤ x)
    (hsurj : Function.Surjective (coordSpanFwd pt)) :
    Nonempty (L ≃o M) := by
  refine orderIso_of_mono_reflect_surj (coordSpanFwd pt) (coordSpanFwd_mono pt) ?_ hsurj
  intro a b hab
  rw [le_iff_atom_le_imp]
  intro c hc hca
  have h1 : pt ⟨c, hc⟩ ≤ coordSpanFwd pt a := coordSpanFwd_point_le pt hca
  exact hclosed ⟨c, hc⟩ b (h1.trans hab)

end Abstract

/-! ### The Mathlib lever: `Subspace ⇝ Submodule` is free -/

section SubspaceLever

variable {L : Type*} [Lattice L]
variable {D : Type*} [DivisionRing D] {V : Type*} [AddCommGroup V] [Module D V]

/-- Given `L ≃o Subspace D V`, the projective-geometry lever
`Projectivization.Subspace.submodule` upgrades it to `L ≃o Submodule D V` for free. -/
def subspace_to_submodule (e : L ≃o Projectivization.Subspace D V) :
    L ≃o Submodule D V :=
  e.trans Projectivization.Subspace.submodule

end SubspaceLever

/-! ### Application to the foam lattice

Specialising the abstract heart to `M = Submodule (Coordinate Γ) V` closes gap B **modulo the
residual** `(pt, hclosed, hsurj)`.  `Submodule` over a division ring is a complete atomistic
lattice (`Mathlib.LinearAlgebra.Basis.VectorSpace`), so the instances resolve automatically. -/

section Application

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-- The **precise residual of gap B**, bundled.  A `PointSystem Γ V` is exactly the data the next
construction pass must supply to obtain `L ≃o Submodule (Coordinate Γ)ᵐᵒᵖ V` (and hence delete
`axiom ftpg`):

* `pt` — the coordinate point of each atom of `L` (a line `Submodule.span D {v}` in `V`);
* `closed` — *closure preservation*: if the coordinate point of an atom `p` lies in the span of
  the points below `x`, then `p ≤ x` (the matroid/collinearity structure of `L` is faithfully
  reflected in `V`);
* `spanning` — *surjectivity*: every submodule of `V` is the span of the points below some `x ∈ L`.

`closed` is the hard geometric content (Veblen–Young coordinatization); `spanning` says the chosen
`V` has exactly the right dimension (its points exhaust the atoms of `L`).

The ring is the **opposite** of the coordinate ring: the line equation carries its slope on the
left (`y = s·x + b`), so the constructed systems are left modules over `(Coordinate Γ)ᵐᵒᵖ` — the
orientation `Plane.lean` surfaced, seated here at the residual's own statement.  The final
existential quantifies the division ring, so nothing downstream moves. -/
structure PointSystem (Γ : CoordSystem L) [DivisionRing (Coordinate Γ)]
    (V : Type u) [AddCommGroup V] [Module (Coordinate Γ)ᵐᵒᵖ V] where
  pt : {p : L // IsAtom p} → Submodule (Coordinate Γ)ᵐᵒᵖ V
  closed : ∀ (p : {p : L // IsAtom p}) (x : L), pt p ≤ coordSpanFwd pt x → (p : L) ≤ x
  spanning : Function.Surjective (coordSpanFwd pt)

/-- From a `PointSystem` (the residual), the coordinatization isomorphism is immediate. -/
theorem PointSystem.orderIso {Γ : CoordSystem L} [DivisionRing (Coordinate Γ)]
    {V : Type u} [AddCommGroup V] [Module (Coordinate Γ)ᵐᵒᵖ V] (P : PointSystem Γ V) :
    Nonempty (L ≃o Submodule (Coordinate Γ)ᵐᵒᵖ V) :=
  nonempty_orderIso_of_pointMap P.pt P.closed P.spanning

/-- Gap B, reduced to its residual.  Given the coordinate division ring `D = (Coordinate Γ)ᵐᵒᵖ`
(`DivisionRing` instance supplied by the sibling construction), a coordinate vector space `V`,
and a point map `pt : Atoms L → Submodule D V` that is **closure-preserving** (`hclosed`) and
**spanning-surjective** (`hsurj`), the coordinatization isomorphism exists. -/
theorem ftpg_coordIso (Γ : CoordSystem L) [DivisionRing (Coordinate Γ)]
    {V : Type u} [AddCommGroup V] [Module (Coordinate Γ)ᵐᵒᵖ V]
    (pt : {p : L // IsAtom p} → Submodule (Coordinate Γ)ᵐᵒᵖ V)
    (hclosed : ∀ (p : {p : L // IsAtom p}) (x : L),
        pt p ≤ coordSpanFwd pt x → (p : L) ≤ x)
    (hsurj : Function.Surjective (coordSpanFwd pt)) :
    Nonempty (L ≃o Submodule (Coordinate Γ)ᵐᵒᵖ V) :=
  nonempty_orderIso_of_pointMap pt hclosed hsurj

/-- The full FTPG existential, assembled from the residual.  This is exactly the witness shape
that `ftpg_proof_limit` in `Deaxiomatize.lean` needs, with the residual data in `coordIso`'s place. -/
theorem ftpg_via_residual (Γ : CoordSystem L) [DivisionRing (Coordinate Γ)]
    {V : Type u} [AddCommGroup V] [Module (Coordinate Γ)ᵐᵒᵖ V]
    (pt : {p : L // IsAtom p} → Submodule (Coordinate Γ)ᵐᵒᵖ V)
    (hclosed : ∀ (p : {p : L // IsAtom p}) (x : L),
        pt p ≤ coordSpanFwd pt x → (p : L) ≤ x)
    (hsurj : Function.Surjective (coordSpanFwd pt)) :
    ∃ (D : Type u) (_ : DivisionRing D)
      (V : Type u) (_ : AddCommGroup V) (_ : Module D V),
    Nonempty (L ≃o Submodule D V) :=
  ⟨(Coordinate Γ)ᵐᵒᵖ, inferInstance, V, ‹_›, ‹_›,
    nonempty_orderIso_of_pointMap pt hclosed hsurj⟩

end Application

/-! ### Axiom audit: the abstract reduction is honestly sorry-free -/

/-- info: 'Foam.Bridges.orderIso_of_mono_reflect_surj' depends on axioms: [Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orderIso_of_mono_reflect_surj

/-- info: 'Foam.Bridges.coordSpanFwd_mono' does not depend on any axioms -/
#guard_msgs in #print axioms coordSpanFwd_mono

/-- info: 'Foam.Bridges.nonempty_orderIso_of_pointMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nonempty_orderIso_of_pointMap

/-- info: 'Foam.Bridges.subspace_to_submodule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subspace_to_submodule

end Foam.Bridges
