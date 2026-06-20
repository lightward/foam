/-
# Foam.Mass — the rest mass is the conserved heard-modulus (indistinguishable-from-mass, closed)

`CANDLES.md` named this and gated it: *"mass is the Lorentz-invariant magnitude of the
energy–momentum vector (rest energy). The energy half is proven (`Conservation`); if the boost
lands and a momentum-analog appears, 'mass' is the conserved heard-modulus read as a Lorentz
invariant — conjecture, gated on the boost."* The boost has landed (`Frames`, `Boost`,
`Rotations`), the momentum-analog is in `Conservation` already (the spent flux beside the
conserved energy — `conserved_invisible_to_spent`), so the gate is open. Here it is.

The energy–momentum vector lives on the HYPERBOLIC frame `SInt` (κ=+1): `t` = energy E, `x` =
momentum p, and the Minkowski norm `hnorm = E² − p²` is the mass². At REST (the bench frame,
p = 0) the norm is `E²`, and E is the heard-modulus — the conserved energy of the immutable past
(`Conservation`). So the rest mass IS the heard-modulus, and it carries both marks of mass:

- **conserved** — `rest_mass_conserved`: the voice spends (a discharge appends spoken/rest) but
  the rest mass² is unchanged, because the heard-modulus is (`heard_modulus_conserved`). Mass is
  a property of the immutable past the voice cannot touch.
- **frame-invariant** — and at integer scale, *trivially* so: the only `hnorm`-preserving integer
  boost is ±id (`Rotations.int_pell_one` — no proper integer boost; the backstage is Galilean,
  `Boost.finite_boost_galilean`). The rest energy reads the same from every available frame
  because there is no proper boost to read it through; the genuine boost-mixing is the continuum
  emergent. So the rest mass is frame-invariant by the same fact that makes finite foam Galilean.

And it sits exactly where the κ=+1 frame leaves room for it: `Frames.zero_point_kappa`'s
`(1 − κ)·f 0 = 0` frees the zero-point ONLY at κ=+1 — the rest-energy gauge. The heard-modulus is
what occupies that free zero-point: the conserved, frame-invariant magnitude the boost cannot pin.

Axiom-free, pinned. (Reading: the mass/energy–momentum naming rides `Spacetime`'s two axes and the
κ=+1 Minkowski norm; the theorems are about the heard-modulus's conservation, which that reading
calls rest mass.)
-/

import Foam.Frames

namespace Foam

/-- The rest-frame energy–momentum vector on the hyperbolic frame `SInt`: ⟨E, 0⟩ with E the
    conserved heard-modulus (`Conservation`) and momentum 0 (at rest, the bench frame). The
    Minkowski norm `hnorm = E² − 0²` is the rest mass². -/
def restEnergyMomentum {S : Type} [DecidableEq S] (l : List (Breath S)) (s : S) : SInt :=
  ⟨(spec (heardOnly l) s).normSq, 0⟩

/-- **The rest mass² is the heard-modulus squared.** At rest (p = 0) the Minkowski norm
    `E² − p²` collapses to `E²`, and E is the heard-modulus — so the rest mass is exactly the
    conserved energy of the immutable past. -/
theorem rest_mass_is_heard_modulus_squared {S : Type} [DecidableEq S]
    (l : List (Breath S)) (s : S) :
    (restEnergyMomentum l s).hnorm
      = (spec (heardOnly l) s).normSq * (spec (heardOnly l) s).normSq := by
  show (spec (heardOnly l) s).normSq * (spec (heardOnly l) s).normSq - 0 * 0
     = (spec (heardOnly l) s).normSq * (spec (heardOnly l) s).normSq
  rw [int_zero_mul, int_sub_zero]

/-- **The rest mass is conserved.** A discharge (the voice — spoken/rest, never a hearing)
    appended to the past leaves the rest mass² exactly unchanged, because it leaves the
    heard-modulus unchanged (`heard_modulus_conserved`). The mass the voice spends charge from
    but can never alter — `indistinguishable-from-mass`, closed: the rest mass is the conserved
    heard-modulus, read as the κ=+1 Minkowski invariant. -/
theorem rest_mass_conserved {S : Type} [DecidableEq S]
    (l t : List (Breath S)) (s : S) (h : IsDischarge t) :
    (restEnergyMomentum (l ++ t) s).hnorm = (restEnergyMomentum l s).hnorm := by
  rw [rest_mass_is_heard_modulus_squared, rest_mass_is_heard_modulus_squared,
      heard_modulus_conserved l t s h]

/-! ## Axiom-freeness, pinned (a drift fails the build). -/

/-- info: 'Foam.rest_mass_is_heard_modulus_squared' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.rest_mass_is_heard_modulus_squared

/-- info: 'Foam.rest_mass_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.rest_mass_conserved

end Foam
