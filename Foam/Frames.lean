/-
# Foam.Frames — the signature trichotomy, unified by κ (one forcing, three frames)

The capstone of the boost arc, and the formal core of `ergodic-symplectic` (the
perspective of 2026-02-24). `Frame.born_forced_at_the_frame` (κ = −1), `Boost`'s
`boost_forced_at_the_frame` (κ = +1), and `Galilean` (κ = 0) are ONE theorem at three
values of a single parameter: κ = (the imaginary unit)², the square that IS the geometry.

The unified structure on the pair `⟨re, im⟩` (reusing `GInt` as the bare carrier):

- `normK κ z = re² − κ·im²` — the κ-deformed interval. κ=−1 ↦ re²+im² (Euclidean, Born);
  κ=+1 ↦ re²−im² (Minkowski, boost); κ=0 ↦ re² (degenerate, Galilean).
- `alignK κ w z = w.re·z.re − κ·w.im·z.im` — the κ-METRIC inner product.
- `crossK w z = w.re·z.im − w.im·z.re` — the SYMPLECTIC form, the area. **κ-INVARIANT:** it
  carries no κ, so it is shared by all three frames. This is the symplectic half of
  `ergodic-symplectic`: SL(2,ℝ) preserves the area (`crossK`); its three conjugacy classes —
  elliptic (rotation), parabolic (shear), hyperbolic (boost) — are the three *metrics*
  (`alignK`/`normK`) it additionally fixes, i.e. the three κ. The symplectic structure is the
  universal; the geometry is the choice of κ on top of it.

**`forced_at_the_frame_kappa`** — the unified forcing. Any interval law `f` meeting the
frame's completeness constraint — `f(alignK κ w z) − κ·f(crossK w z) = normK κ w · normK κ z`
for EVERY pair — is forced to `f a = a·a + κ·f 0`. The complete frame makes the physics by
being complete, at any signature. And the surviving zero-point is governed by a single
factor: **`zero_point_kappa`** — `(1 − κ)·f 0 = 0`. So the rest-energy gauge (`f 0` free) opens
*exactly* at `κ = +1`, where `1 − κ = 0`: the hyperbolic/Lorentz frame, and only it. Born
(κ=−1: `2·f 0 = 0`) and Galilean (κ=0: `f 0 = 0`) pin the zero; the boost frees it. The whole
signature story — the geometry, the forced law, the zero-point gauge — is the one parameter κ.

Consistency (that the square IS such an `f`) is the three κ-instances already proven:
`int_lagrange` (κ=−1, under `born_parseval`), `Boost.int_hyperbolic` (κ=+1), and the
degenerate κ=0. The three rotation groups, for the record: elliptic ℤ/4 (the dial closes —
`rot_complete`), parabolic ℤ (velocities add — `Galilean.galilean_velocities_add`), hyperbolic
trivial at integer scale (no proper integer boost — why Lorentz is a continuum emergent).

Axiom-free, pinned. (Reading: the geometry/SL(2,ℝ) naming rides the standard correspondence
between the three 2D algebras and the three Cayley–Klein geometries; the theorems are about
the κ-arithmetic, which that correspondence reads as the signature trichotomy.)
-/

import Foam.Boost

namespace Foam

/-- The κ-deformed interval on `⟨re, im⟩`: `re² − κ·im²`. The unit's square κ IS the
    geometry (−1 Euclidean, +1 Minkowski, 0 degenerate). -/
def normK (κ : Int) (z : GInt) : Int := z.re * z.re - κ * (z.im * z.im)

/-- The κ-metric inner product: `w.re·z.re − κ·w.im·z.im`. -/
def alignK (κ : Int) (w z : GInt) : Int := w.re * z.re - κ * (w.im * z.im)

/-- The SYMPLECTIC form (the area), `w.re·z.im − w.im·z.re` — κ-INVARIANT, shared by all
    three frames. The universal structure of `ergodic-symplectic`; the metric (`alignK`,
    `normK`) carries the geometry, the area does not. -/
def crossK (w z : GInt) : Int := w.re * z.im - w.im * z.re

theorem alignK_axis (κ a : Int) : alignK κ ⟨a, 0⟩ ⟨1, 0⟩ = a := by
  show a * 1 - κ * (0 * 0) = a
  rw [int_mul_comm a 1, int_one_mul, int_zero_mul, int_mul_comm κ 0, int_zero_mul, int_sub_zero]

theorem crossK_axis (a : Int) : crossK ⟨a, 0⟩ ⟨1, 0⟩ = 0 := by
  show a * 0 - 0 * 1 = 0
  rw [int_mul_comm a 0, int_zero_mul, int_zero_mul, int_sub_zero]

theorem normK_axis_a (κ a : Int) : normK κ ⟨a, 0⟩ = a * a := by
  show a * a - κ * (0 * 0) = a * a
  rw [int_zero_mul, int_mul_comm κ 0, int_zero_mul, int_sub_zero]

theorem normK_axis_one (κ : Int) : normK κ ⟨1, 0⟩ = 1 := by
  show 1 * 1 - κ * (0 * 0) = 1
  rw [int_one_mul, int_zero_mul, int_mul_comm κ 0, int_zero_mul, int_sub_zero]

/-- **The trichotomy, forced at the frame — one theorem, three geometries.** Any interval
    law `f` satisfying the frame's κ-completeness constraint for EVERY pair is forced to be
    the κ-square `f a = a·a + κ·f 0`. `Frame.born_forced_at_the_frame` (κ=−1),
    `Boost.boost_forced_at_the_frame` (κ=+1), and the Galilean κ=0 are its three
    specializations. The measurement-space makes the physics by being complete — at any
    signature; the signature is the single parameter κ. -/
theorem forced_at_the_frame_kappa (κ : Int) (f : Int → Int)
    (h : ∀ w z : GInt, f (alignK κ w z) - κ * f (crossK w z) = normK κ w * normK κ z) :
    ∀ a : Int, f a = a * a + κ * f 0 := by
  intro a
  have ha := h ⟨a, 0⟩ ⟨1, 0⟩
  rw [alignK_axis κ a, crossK_axis a, normK_axis_a κ a, normK_axis_one κ,
      int_mul_comm (a * a) 1, int_one_mul] at ha
  rw [← int_sub_add_cancel (f a) (κ * f 0), ha]

/-- **The zero-point gauge is `(1 − κ)·f 0 = 0`.** Forcing at `a = 0` gives `f 0 = κ·f 0`, so
    `(1 − κ)·f 0 = 0`: the zero-point is pinned unless `κ = +1`. The rest-energy gauge — `f 0`
    free — opens at the hyperbolic frame and there ALONE (Born's `1−(−1)=2` and Galilean's
    `1−0=1` both pin it; only the boost's `1−1=0` frees it). The signature difference,
    reduced to one factor. -/
theorem zero_point_kappa (κ : Int) (f : Int → Int)
    (h : ∀ w z : GInt, f (alignK κ w z) - κ * f (crossK w z) = normK κ w * normK κ z) :
    (1 - κ) * f 0 = 0 := by
  have hf0 := forced_at_the_frame_kappa κ f h 0
  rw [int_zero_mul, int_zero_add] at hf0
  show (1 - κ) * f 0 = 0
  rw [Int.sub_eq_add_neg (a := 1) (b := κ), int_add_mul 1 (-κ) (f 0), int_one_mul,
      int_neg_mul κ (f 0), ← hf0, int_add_neg_self]

/-! ## Axiom-freeness, pinned (a drift fails the build). -/

/-- info: 'Foam.forced_at_the_frame_kappa' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.forced_at_the_frame_kappa

/-- info: 'Foam.zero_point_kappa' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.zero_point_kappa

end Foam
