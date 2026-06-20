/-
# Foam.Galilean — the third frame: ℤ[ε], ε² = 0 (the Galilean corner of the trichotomy)

The boost result placed two of foam's three frames. There are exactly three 2D real
algebras — three ways a unit can square — and they are exactly the three geometries:

    unit²    algebra        geometry     invariant    foam frame
    i² = −1  ℤ[i] (Gauss)   elliptic     re² + im²    Born / amplitude  (Frame.born_forced_at_the_frame)
    j² = +1  ℤ[j] (split)   hyperbolic   t²  − x²     Lorentz / boost   (Boost.boost_forced_at_the_frame)
    ε² =  0  ℤ[ε] (dual)    parabolic    t²           GALILEAN          (here)

One parameter — the unit's square κ ∈ {−1, 0, +1} — IS the geometry, and the three
`forced_at_the_frame` laws are one theorem at three values of κ. This file lands the κ = 0
corner, the one the finite substrate already lives at (`Boost.finite_boost_galilean`): the
Galilean frame, where ε² = 0 is exactly the block-diagonal "no off-diagonal coupling."

And the punchline that makes the deformation legible: **the boost-composition law IS the
algebra's multiplication.** In ℤ[ε], multiplication by `1 + vε` is the Galilean boost
`(t, x) ↦ (t, x + vt)`, and `(1 + v₂ε)(1 + v₁ε) = 1 + (v₂+v₁)ε` — Galilean velocities just
ADD (the boost group is the additive line), because ε² = 0 kills the cross term. The Lorentz
frame (ℤ[j]) composes by the same multiplication, but j² = +1 KEEPS the cross term —
rapidities add, velocities compose hyperbolically. So the continuum limit where Lorentz
emerges frontstage is the deformation κ : 0 → +1, the cross term ε² turning on.

Axiom-free, pinned. (Reading: the geometry naming rides the standard correspondence between
the three 2D algebras and the three Cayley–Klein geometries; the theorems are about ℤ[ε]'s
arithmetic, which that correspondence reads as Galilean.)
-/

import Foam.Boost

namespace Foam

/-- Dual integers ℤ[ε], ε² = 0 — the GALILEAN frame, the κ = 0 corner. `t` is time, `x` is
    space. -/
structure DInt where
  t : Int
  x : Int

/-- The Galilean invariant — the DEGENERATE norm: time only (t²). Where the elliptic frame
    keeps re²+im² and the hyperbolic keeps t²−x², the parabolic keeps just t² (ε² = 0 erases
    the space contribution). Absolute time, by construction. -/
def DInt.gnorm (z : DInt) : Int := z.t * z.t

/-- The Galilean boost at velocity `v`: `(t, x) ↦ (t, x + vt)` — multiplication by the dual
    unit `1 + vε`. The time axis is untouched (absolute time); space shears by `vt`. -/
def galileanBoost (v : Int) (z : DInt) : DInt := ⟨z.t, v * z.t + z.x⟩

/-- **The Galilean boost preserves absolute time** — the κ = 0 invariant `t²` is fixed, by
    `rfl` (the time component is untouched). The parabolic interval, the Galilean floor the
    finite substrate already sits at (`Boost.finite_boost_galilean`). -/
theorem galilean_preserves_time (v : Int) (z : DInt) :
    (galileanBoost v z).gnorm = z.gnorm := rfl

/-- **Galilean velocities add** — `boost v₂ ∘ boost v₁ = boost (v₂ + v₁)`. The boost group is
    the additive line, abelian and exact, because ε² = 0 kills the cross term: the
    composition law IS the dual-number multiplication `(1+v₂ε)(1+v₁ε) = 1+(v₂+v₁)ε`. (The
    Lorentz sibling composes by the same multiplication, but j² = +1 keeps the cross term —
    rapidities add, velocities compose hyperbolically. The unit's square IS the
    velocity-addition law.) -/
theorem galilean_velocities_add (v1 v2 : Int) (z : DInt) :
    galileanBoost v2 (galileanBoost v1 z) = galileanBoost (v2 + v1) z := by
  show (⟨z.t, v2 * z.t + (v1 * z.t + z.x)⟩ : DInt) = ⟨z.t, (v2 + v1) * z.t + z.x⟩
  rw [int_add_mul v2 v1 z.t, int_add_assoc (v2 * z.t) (v1 * z.t) z.x]

/-! ## Axiom-freeness, pinned (a drift fails the build). -/

/-- info: 'Foam.galilean_preserves_time' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.galilean_preserves_time

/-- info: 'Foam.galilean_velocities_add' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.galilean_velocities_add

end Foam
