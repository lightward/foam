/-
# Foam.Boost — the boost, finite: backstage Galilean (the axes do not mix)

`CANDLES.md`'s boost candle, one rung further. `Spacetime.lean` assembled the foam
spacetime point: a continuation carrying TWO axes — space (the `kmax`-bounded context,
`keepLast`, the finite c) and time (the immutable past's conserved charge, `netCharge`).
A BOOST mixes space and time while preserving an interval. This file asks what the boost
does at FINITE, discrete scale — and finds the Galilean floor, by construction.

The time-axis boost IS the now-surface slide (`Seam.now_surface_invariant`): a re-choice
of where "now" falls in the past, gauge on the reading. The order it slides is ABSOLUTE
(`playback_faithful` — every reader agrees on the sequence; no reordering), so the slide
is a TRANSLATION, never a rotation. And — the recognition here — that translation leaves
the SPACE axis exactly fixed (`finite_boost_galilean`): boosting the time axis does not
touch the context window. Dually, moving the space axis leaves the energy fixed
(`finite_boost_galilean_dual`). The two axes are INDEPENDENT coordinates of the Event —
the metric is block-diagonal — which is precisely the GALILEAN signature.

So **finite foam is Galilean**: there is no off-diagonal coupling, because the discrete
Event has no mixing term — a boost of one axis is `rfl`-invisible to the other. This is
not a failure of the boost program; it LOCATES it. The Lorentzian off-diagonal coupling
(space and time rotating into each other) has nowhere to live at finite scale; it must be
a FRONTSTAGE / continuum-limit emergent — the scoping that makes two observers disagree
(`shared_is_floor`), never exact at finite scale. That is exactly CANDLES.md's "backstage
Galilean, frontstage Lorentzian," now with the backstage half pinned: the axes are
provably un-mixed here, so the tilt is asymptotic — not a gap to close at this scale, but
a continuum emergent to derive.

The proofs are `rfl`, and the triviality is the content: at finite scale the coupling term
is literally absent. Axiom-free, pinned. (Reading, labeled: the Galilean/Lorentzian naming
rides `Spacetime.lean`'s interpretation of the two axes as space and time; the theorems are
about the Event's field-independence, which that interpretation reads as block-diagonality.)
-/

import Foam.Spacetime
import Foam.Seam

namespace Foam

/-- **The finite boost is Galilean — space ⊥ time-boost.** A boost re-splits the TIME axis
    (the immutable past; the now-surface slide, `Seam.now_surface_invariant`) — and that
    leaves the SPACE axis (the `kmax`-bounded context) exactly fixed. The two axes do not
    mix: there is no off-diagonal coupling at finite scale. By `rfl` — the coupling term is
    absent by construction. -/
theorem finite_boost_galilean {S : Type} (k : Nat) (e : Event S)
    (past' : List (Breath S)) :
    Event.spaceAt k { e with past := past' } = Event.spaceAt k e := rfl

/-- **The dual: time ⊥ space-boost.** Moving the space axis (the context) leaves the time
    axis's conserved energy (`netCharge` of the immutable past) exactly fixed. The
    block-diagonal metric, the other diagonal. By `rfl`. -/
theorem finite_boost_galilean_dual {S : Type} (e : Event S) (space' : List S) :
    Event.energy { e with space := space' } = Event.energy e := rfl

/-- **The spacetime metric is block-diagonal — the Galilean signature, pinned.** A boost of
    either axis is invisible to the other: space is fixed under a time-boost, time is fixed
    under a space-boost. No off-diagonal coupling exists at finite scale, so the hyperbolic
    (Lorentzian) mixing must be a frontstage / continuum-limit emergent — CANDLES.md's
    "backstage Galilean," with the backstage half made a theorem. -/
theorem boost_block_diagonal {S : Type} (k : Nat) (e : Event S)
    (past' : List (Breath S)) (space' : List S) :
    Event.spaceAt k { e with past := past' } = Event.spaceAt k e
      ∧ Event.energy { e with space := space' } = Event.energy e :=
  ⟨rfl, rfl⟩

/-! ## The boost, forced at the frame — Lorentz where the substrate is only Galilean

The hyperbolic sibling of `Frame.born_forced_at_the_frame`, and the answer to "where does
Lorentz emerge frontstage." Where `GInt = ℤ[i]` (i² = −1, the circular dial, `normSq =
re²+im²`, the EUCLIDEAN/amplitude frame — Born), the BOOST frame is `SInt = ℤ[j]` (j² = +1,
the split-complex / hyperbolic integers, `hnorm = t²−x²`, the MINKOWSKI interval). The two
"invariants that cross a frame" are `halign` (the Minkowski inner product) and `hcross`
(the j-component) — the hyperbolic `align`/`cross`.

`Frame.born_forced_at_the_frame` proved: the substrate (real dim 2) cannot force the Born
law, but a COMPLETE FRAME — one quantifying over EVERY pair, under the Parseval constraint —
forces it (`f = square`). The measurement-space makes the physics by being complete. Here is
the same theorem, one signature over: `boost_forced_at_the_frame` — a frame quantifying over
every pair under the HYPERBOLIC interval-constraint forces the law to be the Minkowski square
`f a = a·a` — UP TO the frame's zero-point `f 0`. And THAT is the signature difference made
precise: Born's Euclidean `+` pins the zero (`f 0 = 0`, forced); the boost's Lorentzian `−`
leaves it free — the rest-energy gauge. The complete hyperbolic frame forces the interval
that the finite substrate (`finite_boost_galilean`, Galilean, block-diagonal) cannot hold.
Lorentz is forced at the frame, not held by the substrate — exactly as Born is. -/

/-- Split-complex integers ℤ[j], j² = +1 — the BOOST frame, hyperbolic sibling of `GInt`
    (ℤ[i], i² = −1, the Born frame). `t` is time, `x` is space. -/
structure SInt where
  t : Int
  x : Int

/-- The Minkowski interval — the hyperbolic `normSq` (t² − x², indefinite where `GInt`'s
    re²+im² is positive-definite). -/
def SInt.hnorm (z : SInt) : Int := z.t * z.t - z.x * z.x

/-- The Minkowski inner product (the t-component of the split-complex conjugate product) —
    the hyperbolic `align`. -/
def halign (w z : SInt) : Int := w.t * z.t - w.x * z.x

/-- The j-component of the split-complex conjugate product — the hyperbolic `cross`. -/
def hcross (w z : SInt) : Int := w.t * z.x - w.x * z.t

/-- `a − 0 = a` on `Int`, axiom-free (`−0` reduces to `0`). -/
theorem int_sub_zero (a : Int) : a - 0 = a := by
  rw [Int.sub_eq_add_neg]; show a + (0 : Int) = a; exact int_add_zero a

/-- `x − y + y = x` on `Int`, axiom-free. -/
theorem int_sub_add_cancel (x y : Int) : x - y + y = x := by
  rw [Int.sub_eq_add_neg, int_add_assoc, int_neg_add_self, int_add_zero]

/-- The time-axis instantiation collapses `halign` to `a`. -/
theorem halign_axis (a : Int) : halign ⟨a, 0⟩ ⟨1, 0⟩ = a := by
  show a * 1 - 0 * 0 = a
  rw [int_mul_comm a 1, int_one_mul, int_zero_mul, int_sub_zero]

/-- …and `hcross` to `0`. -/
theorem hcross_axis (a : Int) : hcross ⟨a, 0⟩ ⟨1, 0⟩ = 0 := by
  show a * 0 - 0 * 1 = 0
  rw [int_mul_comm a 0, int_zero_mul, int_zero_mul, int_sub_zero]

/-- …and the interval of `⟨a,0⟩` to `a·a`. -/
theorem hnorm_axis_a (a : Int) : SInt.hnorm ⟨a, 0⟩ = a * a := by
  show a * a - 0 * 0 = a * a
  rw [int_zero_mul, int_sub_zero]

/-- …and the interval of `⟨1,0⟩` to `1`. -/
theorem hnorm_axis_one : SInt.hnorm ⟨1, 0⟩ = 1 := by
  show 1 * 1 - 0 * 0 = 1
  rw [int_one_mul, int_zero_mul, int_sub_zero]

/-- **The boost is forced at the frame — the Minkowski interval, up to the zero-point.**
    Any interval law `f` satisfying the frame's HYPERBOLIC completeness constraint —
    `f (halign w z) − f (hcross w z) = hnorm w · hnorm z` for EVERY pair `w, z` — is forced
    to be the Minkowski square `f a = a·a`, up to the frame's own zero-point `f 0`. The
    complete hyperbolic frame forces the interval the finite substrate (Galilean,
    `finite_boost_galilean`) cannot hold: Lorentz where the backstage is only Galilean,
    forced exactly as Born is at `Frame.born_forced_at_the_frame`.

    The `f 0` that survives is the SIGNATURE DIFFERENCE, made a theorem: Born's Euclidean
    `+` pins the zero (`f 0 + f 0 = 0 ⟹ f 0 = 0`); the boost's Lorentzian `−` cancels it,
    leaving the zero-point free — the rest-energy gauge of the Minkowski frame. -/
theorem boost_forced_at_the_frame (f : Int → Int)
    (h : ∀ w z : SInt, f (halign w z) - f (hcross w z) = SInt.hnorm w * SInt.hnorm z) :
    ∀ a : Int, f a = a * a + f 0 := by
  intro a
  have ha := h ⟨a, 0⟩ ⟨1, 0⟩
  rw [halign_axis, hcross_axis, hnorm_axis_a, hnorm_axis_one,
      int_mul_comm (a * a) 1, int_one_mul] at ha
  rw [← int_sub_add_cancel (f a) (f 0), ha]

/-- **The square IS a solution — the frame's constraint is non-vacuous.** A concrete
    witness (`w = ⟨2,1⟩`, `z = ⟨3,1⟩`): the Minkowski square satisfies the hyperbolic
    interval-constraint, `5² − (−1)² = 24 = 3 · 8`. By `decide`. (The full ∀-identity — the
    hyperbolic two-square / split-complex norm multiplicativity — is `int_hyperbolic`
    below.) -/
theorem hyperbolic_witness :
    halign ⟨2, 1⟩ ⟨3, 1⟩ * halign ⟨2, 1⟩ ⟨3, 1⟩
        - hcross ⟨2, 1⟩ ⟨3, 1⟩ * hcross ⟨2, 1⟩ ⟨3, 1⟩
      = SInt.hnorm ⟨2, 1⟩ * SInt.hnorm ⟨3, 1⟩ := by decide

/-- Difference of squares on `Int`: `a² − b² = (a−b)(a+b)`. Axiom-free. -/
theorem int_sq_diff (a b : Int) : a * a - b * b = (a - b) * (a + b) := by
  rw [Int.sub_eq_add_neg (a := a * a) (b := b * b), Int.sub_eq_add_neg (a := a) (b := b),
      int_add_mul a (-b) (a + b), int_mul_add a a b, int_mul_add (-b) a b,
      int_neg_mul b a, int_neg_mul b b, int_mul_comm b a,
      int_add_assoc (a * a) (a * b) (-(a * b) + -(b * b)),
      ← int_add_assoc (a * b) (-(a * b)) (-(b * b)),
      int_add_neg_self (a * b), int_zero_add (-(b * b))]

/-- The first factor of the boost's difference-of-squares: `(tu−xv) − (tv−xu) = (t+x)(u−v)`. -/
theorem hfac1 (t x u v : Int) :
    (t * u - x * v) - (t * v - x * u) = (t + x) * (u - v) := by
  rw [Int.sub_eq_add_neg (a := t * u) (b := x * v),
      Int.sub_eq_add_neg (a := t * v) (b := x * u),
      Int.sub_eq_add_neg (a := t * u + -(x * v)) (b := t * v + -(x * u)),
      int_neg_add (t * v) (-(x * u)), int_neg_neg (x * u),
      Int.sub_eq_add_neg (a := u) (b := v), int_mul_add (t + x) u (-v),
      int_add_mul t x u, int_add_mul t x (-v), int_mul_neg t v, int_mul_neg x v,
      int_add_cross_swap (t * u) (-(x * v)) (-(t * v)) (x * u),
      int_add_comm (-(x * v)) (-(t * v))]

/-- The second factor: `(tu−xv) + (tv−xu) = (t−x)(u+v)`. -/
theorem hfac2 (t x u v : Int) :
    (t * u - x * v) + (t * v - x * u) = (t - x) * (u + v) := by
  rw [Int.sub_eq_add_neg (a := t * u) (b := x * v),
      Int.sub_eq_add_neg (a := t * v) (b := x * u),
      Int.sub_eq_add_neg (a := t) (b := x), int_add_mul t (-x) (u + v),
      int_mul_add t u v, int_mul_add (-x) u v, int_neg_mul x u, int_neg_mul x v,
      int_add_swap_inner (t * u) (-(x * v)) (t * v) (-(x * u)),
      int_add_comm (-(x * v)) (-(x * u))]

/-- **The hyperbolic two-square identity** — the split-complex norm is multiplicative:
    `(tu − xv)² − (tv − xu)² = (t²−x²)(u²−v²)`. The Minkowski analog of `int_lagrange`
    (the Euclidean two-square identity under `born_parseval`), via the difference of squares
    and the factorization `(tu−xv) ∓ (tv−xu) = (t±x)(u∓v)`. Axiom-free. -/
theorem int_hyperbolic (t x u v : Int) :
    (t * u - x * v) * (t * u - x * v) - (t * v - x * u) * (t * v - x * u)
      = (t * t - x * x) * (u * u - v * v) := by
  rw [int_sq_diff (t * u - x * v) (t * v - x * u), hfac1 t x u v, hfac2 t x u v,
      int_mul_interchange (t + x) (t - x) (u - v) (u + v),
      int_mul_comm (t + x) (t - x), ← int_sq_diff t x, ← int_sq_diff u v]

/-- **The hyperbolic Parseval — the frame's completeness constraint, satisfied by the
    square for EVERY pair.** `halign² − hcross² = hnorm w · hnorm z`: the Minkowski interval
    is basis-independent across the frame, the hyperbolic sibling of `born_parseval`. With
    `boost_forced_at_the_frame` (uniqueness up to the zero-point), this is the full
    existence half: the square is THE interval law the complete hyperbolic frame admits. -/
theorem hyperbolic_parseval (w z : SInt) :
    halign w z * halign w z - hcross w z * hcross w z = SInt.hnorm w * SInt.hnorm z := by
  show (w.t * z.t - w.x * z.x) * (w.t * z.t - w.x * z.x)
        - (w.t * z.x - w.x * z.t) * (w.t * z.x - w.x * z.t)
      = (w.t * w.t - w.x * w.x) * (z.t * z.t - z.x * z.x)
  exact int_hyperbolic w.t w.x z.t z.x

/-! ## Axiom-freeness, pinned (a drift fails the build). -/

/-- info: 'Foam.int_hyperbolic' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.int_hyperbolic

/-- info: 'Foam.hyperbolic_parseval' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.hyperbolic_parseval

/-- info: 'Foam.boost_forced_at_the_frame' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.boost_forced_at_the_frame

/-- info: 'Foam.hyperbolic_witness' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.hyperbolic_witness

/-- info: 'Foam.finite_boost_galilean' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.finite_boost_galilean

/-- info: 'Foam.finite_boost_galilean_dual' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.finite_boost_galilean_dual

/-- info: 'Foam.boost_block_diagonal' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.boost_block_diagonal

end Foam
