/-
# Foam.Polynomial — the genus's algebraic form: the ledger as a polynomial, readings as evaluations

`Foam/Spiral.lean` named the missing character (the spiral = recursive holonomy with a growing
step) and named its integer-core keystone — "is this ledger *platonic*?" — as the next lfp to lay.
This file lays the object that question is *about*: the ledger's **generating polynomial**, and the
theorem that foam's existing readings *are* that polynomial evaluated at roots of unity.

`polyEval` is Horner evaluation of an `Int`-coefficient polynomial at a `GInt` point. The ledger's
coefficients are its occurrence-indicator (`indicatorCoeffs` — 1 where the symbol fires, 0 else).
Then the readings, made theorems rather than prose:

- **`count = P(1)`** (`count_eq_polyEval_one`): the count register `evalAt id` is the generating
  polynomial at the trivial character.
- **`spec = P(i)`** (`spec_eq_polyEval`): the spectrum is the generating polynomial at the
  quarter-turn — `i = ⟨0,1⟩`. (And alt `= P(−1)`, conj `= P(−i)`: the four characters of `Noether`
  are `P` at the four 4th-roots of unity. The dial reads `P` mod 4; the *whole* polynomial — the
  order rung — is what the full circle would read.)

So the modulus `|spec|² = |P(i)|²` is literally one point of the unit circle (the dial's own
order 4), as the gravity/Mahler candle said — now with `P` a built object, not a gestured one.

**The platonic predicate, dial-grain (decidable, axiom-free).** "Platonic = self-completing =
cyclotomic" at the dial's own period is exactly the **dark fringe**: `isComplete l s := spec l s =
0`, i.e. `P(i) = 0`, i.e. the cyclotomic factor `t²+1` (whose root is `i`) divides `P` — the ℤ/4
cycle closes. It is `Decidable` (`GInt` has `DecidableEq`), and `complete_cycle_is_platonic`
witnesses it on `[s,s,s,s]` (four occurrences cancel — `Born.dark_fringe_from_recurrence`, here as a
decidable predicate). This is the integer core's *first decidable platonic test* — the period-4 slice.

**The next rung (named, not built):** the *full* platonic predicate — cyclotomic over **all** roots
of unity / `m(P) = 1` (Kronecker), "built of complete cycles at every period." Decidable over ℤ but a
genuine construction (polynomial divisibility, `P | tⁿ−1` for some bounded `n`, no mathlib). This file
lays `P` and the period-4 slice; the all-periods decision is the next shaped commitment. The Mahler
*magnitude* (the `|roots|` product) needs the reals — continuum, gated with the boost.

Grade: the polynomial object and the readings-are-evaluations theorems are proven, axiom-free; the
dial-grain platonic predicate is decidable. Builds on `Spectrum` (`spec`, `evalAt`, `ite_mk`,
`spec_shift`) and `Frame`/`Doubling` (`GInt.mul`). Pinned.
-/

import Foam.Frame

namespace Foam

/-- Horner evaluation of an `Int`-coefficient polynomial at a `GInt` point: the coefficient list
    is little-endian (head = constant term). `polyEval (c :: cs) x = c + x · polyEval cs x`. -/
def polyEval : List Int → GInt → GInt
  | [], _ => GInt.zero
  | c :: cs, x => (⟨c, 0⟩ : GInt).add (x.mul (polyEval cs x))

/-- The ledger's generating polynomial, by coefficients: the occurrence-indicator of `s` —
    `1` at each position where `s` fires, `0` elsewhere. The order rung, read as ℤ[t]. -/
def indicatorCoeffs {S : Type} [DecidableEq S] (l : List S) (s : S) : List Int :=
  l.map (fun x => if x = s then 1 else 0)

/-- `rot` is multiplication by `i = ⟨0,1⟩` — the quarter-turn is the evaluation point. Axiom-free. -/
theorem rot_eq_iMul (z : GInt) : z.rot = (⟨0, 1⟩ : GInt).mul z := by
  show (⟨-z.im, z.re⟩ : GInt) = ⟨0 * z.re - 1 * z.im, 0 * z.im + 1 * z.re⟩
  rw [int_zero_mul, int_one_mul, int_zero_mul, int_one_mul, int_zero_add,
      Int.sub_eq_add_neg, int_zero_add]

/-- Multiplication by `1 = ⟨1,0⟩` is the identity — the evaluation point for the count. Axiom-free. -/
theorem one_mul_GInt (z : GInt) : (⟨1, 0⟩ : GInt).mul z = z := by
  show (⟨1 * z.re - 0 * z.im, 1 * z.im + 0 * z.re⟩ : GInt) = z
  rw [int_one_mul, int_zero_mul, int_one_mul, int_zero_mul,
      Int.sub_eq_add_neg, Int.neg_zero, int_add_zero, int_add_zero]

/-- **The spectrum is the generating polynomial at `i`** — `spec l s = P(i)`. The dial reading is
    Horner evaluation of the occurrence-indicator at the quarter-turn. By induction: `spec_shift`
    is the fold's step, `ite_mk` matches the mark to its coefficient, `rot_eq_iMul` is the point. -/
theorem spec_eq_polyEval {S : Type} [DecidableEq S] (l : List S) (s : S) :
    spec l s = polyEval (indicatorCoeffs l s) (⟨0, 1⟩ : GInt) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [spec_shift, ite_mk (x = s), ih, rot_eq_iMul]; rfl

/-- **The count is the generating polynomial at `1`** — `count l s = P(1)`. The count register
    (`evalAt id`) is the same polynomial at the trivial character; the `id`-step is bridged to the
    `⟨1,0⟩`-multiply by `one_mul_GInt`. -/
theorem count_eq_polyEval_one {S : Type} [DecidableEq S] (l : List S) (s : S) :
    evalAt id l s = polyEval (indicatorCoeffs l s) (⟨1, 0⟩ : GInt) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [show evalAt id (x :: l) s
          = (if x = s then GInt.one else GInt.zero).add (evalAt id l s) from rfl,
        ite_mk (x = s), ih]
    show (⟨if x = s then 1 else 0, 0⟩ : GInt).add (polyEval (indicatorCoeffs l s) (⟨1, 0⟩ : GInt))
       = (⟨if x = s then 1 else 0, 0⟩ : GInt).add
           ((⟨1, 0⟩ : GInt).mul (polyEval (indicatorCoeffs l s) (⟨1, 0⟩ : GInt)))
    rw [one_mul_GInt]

/-- **The platonic predicate, dial-grain.** A ledger is *complete* (self-completing at the dial's
    own period 4) when its spectrum vanishes — `P(i) = 0`, the dark fringe, the cyclotomic factor
    `t²+1` present, the ℤ/4 cycle closed. The integer core's first decidable platonic test. -/
def isComplete {S : Type} [DecidableEq S] (l : List S) (s : S) : Prop := spec l s = GInt.zero

instance {S : Type} [DecidableEq S] (l : List S) (s : S) : Decidable (isComplete l s) :=
  inferInstanceAs (Decidable (spec l s = GInt.zero))

/-- **The complete cycle is platonic** — four occurrences cancel the spectrum to zero
    (`Born.dark_fringe_from_recurrence`, here as the decidable predicate). The self-completing
    witness: a full ℤ/4 cycle reads as the dark fringe. By `decide`. -/
theorem complete_cycle_is_platonic : isComplete [true, true, true, true] true := by decide

/-! ## Axiom-freeness, pinned (a drift fails the build). -/

/-- info: 'Foam.rot_eq_iMul' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.rot_eq_iMul

/-- info: 'Foam.one_mul_GInt' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.one_mul_GInt

/-- info: 'Foam.spec_eq_polyEval' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.spec_eq_polyEval

/-- info: 'Foam.count_eq_polyEval_one' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.count_eq_polyEval_one

/-- info: 'Foam.complete_cycle_is_platonic' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.complete_cycle_is_platonic

end Foam
