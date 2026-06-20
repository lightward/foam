/-
# Foam.Conservation — the conserved energy is the immutable past

Measured before it was proven (2026-06-14, against `lightward_foam_dev` and a
throwaway field): a foam-probe's reality conserves an energy, and the energy is
the *heard-record*. Across eight turns of varied seed and length, the squared
modulus of the heard-only spectrum did not move — `d_nsq_heard = 0`, every turn,
exactly — while the net charge dropped by precisely the number of bytes spoken
(`d_net = −spoken`). This file is that measurement, proven.

The recognition under it: **conservation is append-only.** Speaking is the
discharge — it appends only `Breath.spoken`/`Breath.rest` beats (charge ≤ 0,
never a hearing), so it cannot touch the +1 events the heard-record is made of.
The voice *reads* the past; it cannot *edit* it. Therefore every reading of the
heard-record — its spectrum, its modulus, its count — is invariant under the
voice, while the net charge is spent at the boundary to the unit. That is the
first law (`netCharge` drops by exactly what crossed) beside the conserved
energy (the heard modulus, unmoved): `Noether.lean`'s "what is conserved is
invisible to the dynamics that spend everything else," now a theorem about
breath-ledgers rather than a line of prose.

The alphabet is `Dusk.Breath` (the forced ternary floor — heard/spoken/rest); the
reading is `Spectrum.spec` at the quarter-turn and `Noether`'s `GInt.normSq`. The
arithmetic floor is `IntFloor` (core's `Int` lemmas carry `propext`; these ask no
one). Pure construction — axiom-free, pinned below.
-/

import Foam.Dusk
import Foam.Spectrum
import Foam.Noether
import Foam.IntFloor

namespace Foam

/-- The **heard-record**: the +1 events of a breath-ledger, in order — the
    immutable past the voice reads but never edits. `spoken` and `rest` beats
    drop out; only `heard` survives. -/
def heardOnly {S : Type} : List (Breath S) → List S
  | [] => []
  | Breath.heard s :: l => s :: heardOnly l
  | Breath.spoken _ :: l => heardOnly l
  | Breath.rest _ :: l => heardOnly l

/-- A **discharge**: a turn the voice performs alone — spoken and rest beats
    only, never a hearing. Speaking spends and rests; it does not hear. -/
def IsDischarge {S : Type} : List (Breath S) → Prop
  | [] => True
  | Breath.heard _ :: _ => False
  | Breath.spoken _ :: l => IsDischarge l
  | Breath.rest _ :: l => IsDischarge l

/-- A discharge contributes nothing to the heard-record — no +1 events in it. -/
theorem discharge_heardOnly_nil {S : Type} :
    ∀ (t : List (Breath S)), IsDischarge t → heardOnly t = []
  | [], _ => rfl
  | Breath.heard _ :: _, h => nomatch h
  | Breath.spoken _ :: l, h => discharge_heardOnly_nil l h
  | Breath.rest _ :: l, h => discharge_heardOnly_nil l h

/-- **The heard-record is invariant under the discharge.** Appending any turn the
    voice performs alone — spoken/rest, no hearing — leaves the heard-record
    *exactly* unchanged. The voice reads the past; it cannot rewrite it. The proof
    walks the prefix `l` and, at the tail, drops the whole discharge to nothing. -/
theorem heardOnly_discharge_invariant {S : Type} :
    ∀ (l t : List (Breath S)), IsDischarge t → heardOnly (l ++ t) = heardOnly l
  | [], t, h => discharge_heardOnly_nil t h
  | Breath.heard s :: l, t, h => congrArg (s :: ·) (heardOnly_discharge_invariant l t h)
  | Breath.spoken _ :: l, t, h => heardOnly_discharge_invariant l t h
  | Breath.rest _ :: l, t, h => heardOnly_discharge_invariant l t h

/-- **The heard spectrum is conserved under the discharge** — `spec` of the
    heard-record is unmoved by speaking. -/
theorem heard_spec_conserved {S : Type} [DecidableEq S]
    (l t : List (Breath S)) (s : S) (h : IsDischarge t) :
    spec (heardOnly (l ++ t)) s = spec (heardOnly l) s := by
  rw [heardOnly_discharge_invariant l t h]

/-- **The conserved energy: the heard modulus is invariant under the discharge.**
    `(spec heard).normSq` — the squared modulus of the heard-record's spectrum —
    is *exactly* unchanged by speaking. This is `d_nsq_heard = 0`, measured live
    over the dev field (eight turns, 2026-06-14), now proven: the voice spends
    charge but cannot touch the modulus of the past. -/
theorem heard_modulus_conserved {S : Type} [DecidableEq S]
    (l t : List (Breath S)) (s : S) (h : IsDischarge t) :
    (spec (heardOnly (l ++ t)) s).normSq = (spec (heardOnly l) s).normSq := by
  rw [heardOnly_discharge_invariant l t h]

/-! ## The spent register — the first law at the boundary -/

/-- The **net charge** of a breath-ledger: heard +1, spoken −1, rest 0, summed.
    Hand-rolled fold so it asks no one. -/
def netCharge {S : Type} : List (Breath S) → Int
  | [] => 0
  | b :: l => b.charge + netCharge l

/-- **The books are additive across the seam** — net charge is a homomorphism on
    concatenation: nothing is created or destroyed where two ledgers meet. -/
theorem netCharge_append {S : Type} :
    ∀ (a b : List (Breath S)), netCharge (a ++ b) = netCharge a + netCharge b
  | [], b => (int_zero_add (netCharge b)).symm
  | x :: a, b => by
      show x.charge + netCharge (a ++ b) = x.charge + netCharge a + netCharge b
      rw [netCharge_append a b, int_add_assoc]

/-- A pure discharge of drains — spoken beats only. Explicit per-constructor
    patterns (no catch-all): a catch-all matcher won't reduce definitionally and
    would price `propext` in every consumer. -/
def AllSpoken {S : Type} : List (Breath S) → Prop
  | [] => True
  | Breath.heard _ :: _ => False
  | Breath.spoken _ :: l => AllSpoken l
  | Breath.rest _ :: _ => False

/-- A pure drain-discharge is a discharge (spoken-only ⟹ no hearing). -/
theorem allSpoken_isDischarge {S : Type} :
    ∀ (t : List (Breath S)), AllSpoken t → IsDischarge t
  | [], _ => trivial
  | Breath.heard _ :: _, h => nomatch h
  | Breath.spoken _ :: l, h => allSpoken_isDischarge l h
  | Breath.rest _ :: _, h => nomatch h

/-- `−1 + −n = −(n+1)` on `Int`, axiom-free: by cases on `n`, the `negSucc`
    arithmetic reduces definitionally except the one `0 + n` step, carried by
    `nat_zero_add`. (Core's subtraction/order lemmas would price `propext`; the
    drain-count asks no one.) -/
theorem negOne_add_neg_ofNat :
    ∀ n : Nat, (-1 : Int) + -(Int.ofNat n) = -(Int.ofNat (n + 1))
  | 0 => rfl
  | n + 1 => by
      show Int.negSucc (0 + n + 1) = Int.negSucc (n + 1)
      rw [nat_zero_add]

/-- `k` drains carry net charge exactly `−k`. Term-mode recursion (not `rw` on the
    function's own equation — that would price `propext`): rewrite the tail by the
    IH via `congrArg`, then close with the arithmetic lemma. -/
theorem allSpoken_netCharge {S : Type} :
    ∀ (t : List (Breath S)), AllSpoken t → netCharge t = -(Int.ofNat t.length)
  | [], _ => rfl
  | Breath.heard _ :: _, h => nomatch h
  | Breath.spoken _ :: l, h =>
      (congrArg (fun x => (-1 : Int) + x) (allSpoken_netCharge l h)).trans
        (negOne_add_neg_ofNat l.length)
  | Breath.rest _ :: _, h => nomatch h

/-- **The first law, at the boundary.** A discharge of `k` drains appended to any
    ledger drops the net charge by exactly `k` — `netCharge l + −k`: what the voice
    spends equals what crossed the boundary, to the unit. The measured
    `d_net = −spoken`, proven. (Stated `+ -(…)` rather than `- (…)` to stay
    axiom-free: core's `Int.sub_eq_add_neg` carries `propext`; the discharge asks
    no one.) -/
theorem netCharge_discharge {S : Type} (l t : List (Breath S)) (h : AllSpoken t) :
    netCharge (l ++ t) = netCharge l + -(Int.ofNat t.length) := by
  rw [netCharge_append, allSpoken_netCharge t h]

/-- **What is conserved is invisible to the dynamics that spend everything else.**
    Under one discharge of drains, the heard modulus is *unchanged* while the net
    charge drops by *exactly* the number spent. The conserved energy (the past)
    and the spent register (the voice) move independently — the voice cannot reach
    what conservation holds. `Noether`'s headline, as one statement. -/
theorem conserved_invisible_to_spent {S : Type} [DecidableEq S]
    (l t : List (Breath S)) (s : S) (h : AllSpoken t) :
    (spec (heardOnly (l ++ t)) s).normSq = (spec (heardOnly l) s).normSq
      ∧ netCharge (l ++ t) = netCharge l + -(Int.ofNat t.length) :=
  ⟨heard_modulus_conserved l t s (allSpoken_isDischarge t h), netCharge_discharge l t h⟩

/-! ## Axiom-freeness, pinned (a drift fails `lake build`). -/

/-- info: 'Foam.heardOnly_discharge_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.heardOnly_discharge_invariant

/-- info: 'Foam.heard_modulus_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.heard_modulus_conserved

/-- info: 'Foam.netCharge_append' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.netCharge_append

/-- info: 'Foam.negOne_add_neg_ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.negOne_add_neg_ofNat

/-- info: 'Foam.allSpoken_netCharge' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.allSpoken_netCharge

/-- info: 'Foam.netCharge_discharge' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.netCharge_discharge

/-- info: 'Foam.conserved_invisible_to_spent' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.conserved_invisible_to_spent

end Foam
