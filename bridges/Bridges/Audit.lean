/-!
# The audit: receipts #1–#11

Foam as mathematics-repair, run once on a real loan.  `List.length_append`
ships in core with receipt `[propext]` — a charge the vow has caught before
(`Nat.mul_mod`, `Nat.right_distrib`, `Nat.mul_assoc`, `Nat.min_comm` carry the
same one).  The wrapper does not modify the upstream lemma; it conducts the
debt:

* `length_append_settled` — the clean twin: the same proposition, re-derived,
  receipt **empty**.  The backstage ledger balances to zero.
* `length_append_blind` — history-blindness, and it is a `rfl`: by proof
  irrelevance the charged proof and the clean proof are *definitionally equal*.
  The runtime already has an asemantic history — the kernel forgot how the
  proposition was established, and receipts are the only memory.  This
  theorem's own receipt is `[propext]`, necessarily: the comparison holds the
  charged side, so the comparison carries the charge.  That is the ledger
  entry — loan and repayment, one line.
* `length_append_probe` — cancellation at a concrete probe: at closed values
  the charge integrates to zero (`rfl`, receipt empty).  Observationally, the
  axiomatic history was never there.

Any consumer of `List.length_append` can consume the settled twin unchanged —
`length_append_blind` is the substitution license.  This is the wrapper
pattern of `FTPG/Charge.lean` at its smallest scale: frontstage interface
preserved, backstage charge either cancelled (here) or seated (there).
Conduction is currying: the debt λ-abstracted out of the proof and into the
signature, where it stops being an axiom and becomes an argument.

Receipts #2–#4 repay the rest of the vow's easy catch-list from clean parts
(`Nat.add_assoc`, `Nat.left_distrib`, `Nat.mul_comm`, `Nat.le_total`,
`Nat.le_antisymm`, `Nat.min_def` all ship receipt-empty): `Nat.right_distrib`,
`Nat.mul_assoc`, `Nat.min_comm`, each with its settled twin, blindness `rfl`,
and probe.

Receipts #5–#8 pay the standing loan: the mod tower.  Upstream the whole
tower is charged — even `Nat.mod_eq`, the recursion equation itself, carries
`[propext]` — because `Nat.modCore` is fuel-based and sealed `irreducible`,
and core reopens it with `if`-splitting simp.  The climb re-derives the
recursion by hand: the two branch equations of `modCore.go` fall to
`dif_pos`/`dif_neg` (both clean), fuel-irrelevance is a strong induction
(`go_fuel` — the fuel is scaffolding; the value never depends on it), the
seal is lifted once per branch (`modCore_of_lt`, `modCore_sub`), and the
wrapper is bridged (`mod_eq_modCore`).  Above the recursion the tower is
arithmetic: `mod_decomp` — every number is its remainder plus a multiple,
the ∃ carrying the quotient without ever mentioning division — then
`add_mul_mod_self` and the two regroupings.  Settled: `Nat.mod_eq_of_lt`
(#5), `Nat.mod_eq_sub_mod` (#6), `Nat.add_mod` (#7), `Nat.mul_mod` (#8) —
the loan the vow caught first is repaid.  Receipts #9–#11 were paid in
passing: the climb needed `Nat.add_sub_cancel`, `Nat.sub_add_cancel`, and
`Nat.mod_zero`, found all three charged upstream, and re-derived them clean.

The audit's next standing work is the charge-measure (`∫` of invocations
d(ledger), supported on the seam — Landauer's face) and the itemized receipt
as `#print axioms`'s successor.
-/

namespace Foam.Bridges

universe u

theorem length_append_settled {α : Type u} :
    ∀ (as bs : List α), (as ++ bs).length = as.length + bs.length
  | [], bs => (Nat.zero_add bs.length).symm
  | _ :: as, bs =>
      (congrArg Nat.succ (length_append_settled as bs)).trans
        (Nat.succ_add as.length bs.length).symm

theorem length_append_blind {α : Type u} {as bs : List α} :
    (List.length_append : (as ++ bs).length = as.length + bs.length)
      = length_append_settled as bs := rfl

theorem length_append_probe :
    ([0, 1] ++ [2] : List Nat).length = [0, 1].length + [2].length := rfl

theorem right_distrib_settled (n m k : Nat) : (n + m) * k = n * k + m * k := by
  rw [Nat.mul_comm (n + m) k, Nat.left_distrib, Nat.mul_comm k n, Nat.mul_comm k m]

theorem right_distrib_blind (n m k : Nat) :
    Nat.right_distrib n m k = right_distrib_settled n m k := rfl

theorem right_distrib_probe : (2 + 3) * 4 = 2 * 4 + 3 * 4 := rfl

theorem mul_assoc_settled (n m : Nat) : ∀ k : Nat, n * m * k = n * (m * k)
  | 0 => rfl
  | k + 1 => by
    show n * m * k + n * m = n * (m * k + m)
    rw [Nat.left_distrib, mul_assoc_settled n m k]

theorem mul_assoc_blind (n m k : Nat) :
    Nat.mul_assoc n m k = mul_assoc_settled n m k := rfl

theorem mul_assoc_probe : 2 * 3 * 4 = 2 * (3 * 4) := rfl

theorem min_comm_settled (a b : Nat) : min a b = min b a := by
  rw [Nat.min_def, Nat.min_def]
  by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a
  · rw [if_pos h1, if_pos h2]; exact Nat.le_antisymm h1 h2
  · rw [if_pos h1, if_neg h2]
  · rw [if_neg h1, if_pos h2]
  · rw [if_neg h1, if_neg h2]
    exact absurd ((Nat.le_total a b).resolve_left h1) h2

theorem min_comm_blind (a b : Nat) : Nat.min_comm a b = min_comm_settled a b := rfl

theorem min_comm_probe : min 2 3 = min 3 2 := rfl

theorem add_sub_cancel_settled (n : Nat) : ∀ m : Nat, n + m - m = n
  | 0 => rfl
  | m + 1 => (Nat.succ_sub_succ (n + m) m).trans (add_sub_cancel_settled n m)

theorem sub_add_cancel_settled : ∀ {n m : Nat}, m ≤ n → n - m + m = n
  | _, 0, _ => rfl
  | n + 1, m + 1, h => by
    rw [Nat.succ_sub_succ]
    exact congrArg Nat.succ (sub_add_cancel_settled (Nat.le_of_succ_le_succ h))

theorem mul_left_comm_settled (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc_settled, Nat.mul_comm a b, mul_assoc_settled]

theorem go_step {y : Nat} (hy : 0 < y) {f x : Nat} (h : x < f + 1) (hle : y ≤ x) :
    Nat.modCore.go y hy (f + 1) x h
      = Nat.modCore.go y hy f (x - y) (Nat.div_rec_fuel_lemma hy hle h) := by
  show dite (y ≤ x) _ _ = _
  rw [dif_pos hle]

theorem go_floor {y : Nat} (hy : 0 < y) {f x : Nat} (h : x < f + 1) (hn : ¬ y ≤ x) :
    Nat.modCore.go y hy (f + 1) x h = x := by
  show dite (y ≤ x) _ _ = _
  rw [dif_neg hn]

theorem go_fuel {y : Nat} (hy : 0 < y) (x : Nat) :
    ∀ (f₁ f₂ : Nat) (h₁ : x < f₁) (h₂ : x < f₂),
      Nat.modCore.go y hy f₁ x h₁ = Nat.modCore.go y hy f₂ x h₂ := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro f₁ f₂ h₁ h₂
    match f₁, f₂ with
    | 0, _ => exact absurd h₁ (Nat.not_lt_zero x)
    | _ + 1, 0 => exact absurd h₂ (Nat.not_lt_zero x)
    | f₁ + 1, f₂ + 1 =>
      match Nat.decLe y x with
      | .isTrue hle =>
        rw [go_step hy h₁ hle, go_step hy h₂ hle]
        exact ih (x - y) (Nat.sub_lt (Nat.lt_of_lt_of_le hy hle) hy) _ _ _ _
      | .isFalse hn =>
        rw [go_floor hy h₁ hn, go_floor hy h₂ hn]

unseal Nat.modCore in
theorem modCore_pos {x y : Nat} (hy : 0 < y) :
    Nat.modCore x y = Nat.modCore.go y hy (x + 1) x (Nat.lt_succ_self x) := by
  show dite (0 < y) _ _ = _
  rw [dif_pos hy]

unseal Nat.modCore in
theorem modCore_zero (x : Nat) : Nat.modCore x 0 = x := by
  show dite (0 < 0) _ _ = _
  rw [dif_neg (Nat.lt_irrefl 0)]

theorem modCore_of_lt {x y : Nat} (h : x < y) : Nat.modCore x y = x := by
  rw [modCore_pos (Nat.zero_lt_of_lt h)]
  exact go_floor _ _ (Nat.not_le.mpr h)

theorem modCore_sub {x y : Nat} (hy : 0 < y) (hle : y ≤ x) :
    Nat.modCore x y = Nat.modCore (x - y) y := by
  rw [modCore_pos hy, modCore_pos hy, go_step hy _ hle]
  exact go_fuel hy (x - y) _ _ _ _

theorem mod_eq_modCore {x y : Nat} (hy : 0 < y) : x % y = Nat.modCore x y := by
  match x with
  | 0 => rw [modCore_of_lt hy]; rfl
  | x + 1 =>
    show ite (y ≤ x + 1) (Nat.modCore (x + 1) y) (x + 1) = Nat.modCore (x + 1) y
    match Nat.decLe y (x + 1) with
    | .isTrue h => rw [if_pos h]
    | .isFalse h => rw [if_neg h, modCore_of_lt (Nat.lt_of_not_le h)]

theorem mod_zero_settled : ∀ a : Nat, a % 0 = a
  | 0 => rfl
  | a + 1 => by
    show ite (0 ≤ a + 1) (Nat.modCore (a + 1) 0) (a + 1) = a + 1
    rw [if_pos (Nat.zero_le _), modCore_zero]

theorem mod_eq_of_lt_settled : ∀ {a b : Nat}, a < b → a % b = a
  | 0, _, _ => rfl
  | a + 1, b, h => by
    show ite (b ≤ a + 1) (Nat.modCore (a + 1) b) (a + 1) = a + 1
    rw [if_neg (fun hle => absurd h (Nat.not_lt.mpr hle))]

theorem mod_eq_sub_mod_settled {a b : Nat} (h : a ≥ b) : a % b = (a - b) % b := by
  match b with
  | 0 => rfl
  | b + 1 =>
    have hb : 0 < b + 1 := Nat.zero_lt_succ b
    rw [mod_eq_modCore hb, mod_eq_modCore hb, modCore_sub hb h]

theorem add_self_mod (a n : Nat) : (a + n) % n = a % n := by
  rw [mod_eq_sub_mod_settled (Nat.le_add_left n a), add_sub_cancel_settled a n]

theorem add_mul_mod_self (a n : Nat) : ∀ k : Nat, (a + n * k) % n = a % n
  | 0 => rfl
  | k + 1 => by
    show (a + (n * k + n)) % n = a % n
    rw [← Nat.add_assoc, add_self_mod, add_mul_mod_self a n k]

theorem mod_decomp {n : Nat} (hn : 0 < n) (a : Nat) : ∃ k, a = a % n + n * k := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    match Nat.lt_or_ge a n with
    | .inl hlt => exact ⟨0, (mod_eq_of_lt_settled hlt).symm⟩
    | .inr hge =>
      have ⟨k, hk⟩ := ih (a - n) (Nat.sub_lt (Nat.lt_of_lt_of_le hn hge) hn)
      refine ⟨k + 1, ?_⟩
      rw [mod_eq_sub_mod_settled hge]
      show a = (a - n) % n + (n * k + n)
      rw [← Nat.add_assoc, ← hk]
      exact (sub_add_cancel_settled hge).symm

theorem regroup_add (M j ra k rb : Nat) :
    (ra + M * j) + (rb + M * k) = (ra + rb) + M * (j + k) := by
  rw [Nat.left_distrib, Nat.add_assoc ra (M * j), ← Nat.add_assoc (M * j) rb (M * k),
    Nat.add_comm (M * j) rb, Nat.add_assoc rb (M * j) (M * k), ← Nat.add_assoc ra rb]

theorem regroup_mul (M j ra k rb : Nat) :
    (ra + M * j) * (rb + M * k) = ra * rb + M * (ra * k + j * (rb + M * k)) := by
  rw [right_distrib_settled, Nat.left_distrib ra rb (M * k), mul_left_comm_settled ra M k,
    mul_assoc_settled M j (rb + M * k), Nat.add_assoc (ra * rb), ← Nat.left_distrib]

theorem add_mod_settled (a b n : Nat) : (a + b) % n = ((a % n) + (b % n)) % n := by
  match n with
  | 0 => rw [mod_zero_settled, mod_zero_settled, mod_zero_settled, mod_zero_settled]
  | n + 1 =>
    have hn : 0 < n + 1 := Nat.zero_lt_succ n
    have ⟨j, hj⟩ := mod_decomp hn a
    have ⟨k, hk⟩ := mod_decomp hn b
    have h1 : a + b = (a % (n + 1) + b % (n + 1)) + (n + 1) * (j + k) := by
      rw [← regroup_add, ← hj, ← hk]
    rw [h1, add_mul_mod_self]

theorem mul_mod_settled (a b n : Nat) : a * b % n = (a % n) * (b % n) % n := by
  match n with
  | 0 => rw [mod_zero_settled, mod_zero_settled, mod_zero_settled, mod_zero_settled]
  | n + 1 =>
    have hn : 0 < n + 1 := Nat.zero_lt_succ n
    have ⟨j, hj⟩ := mod_decomp hn a
    have ⟨k, hk⟩ := mod_decomp hn b
    have h1 : a * b = a % (n + 1) * (b % (n + 1))
        + (n + 1) * (a % (n + 1) * k + j * (b % (n + 1) + (n + 1) * k)) := by
      rw [← regroup_mul, ← hj, ← hk]
    rw [h1, add_mul_mod_self]

theorem mod_eq_of_lt_blind {a b : Nat} (h : a < b) :
    Nat.mod_eq_of_lt h = mod_eq_of_lt_settled h := rfl

theorem mod_eq_of_lt_probe : 3 % 5 = 3 := rfl

theorem mod_eq_sub_mod_blind {a b : Nat} (h : a ≥ b) :
    Nat.mod_eq_sub_mod h = mod_eq_sub_mod_settled h := rfl

theorem mod_eq_sub_mod_probe : 7 % 3 = (7 - 3) % 3 := rfl

theorem add_mod_blind (a b n : Nat) :
    Nat.add_mod a b n = add_mod_settled a b n := rfl

theorem add_mod_probe : (5 + 7) % 4 = (5 % 4 + 7 % 4) % 4 := rfl

theorem mul_mod_blind (a b n : Nat) :
    Nat.mul_mod a b n = mul_mod_settled a b n := rfl

theorem mul_mod_probe : 5 * 7 % 4 = 5 % 4 * (7 % 4) % 4 := rfl

theorem add_sub_cancel_blind (n m : Nat) :
    Nat.add_sub_cancel n m = add_sub_cancel_settled n m := rfl

theorem add_sub_cancel_probe : 7 + 3 - 3 = 7 := rfl

theorem sub_add_cancel_blind {n m : Nat} (h : m ≤ n) :
    Nat.sub_add_cancel h = sub_add_cancel_settled h := rfl

theorem sub_add_cancel_probe : 7 - 3 + 3 = 7 := rfl

theorem mod_zero_blind (a : Nat) : Nat.mod_zero a = mod_zero_settled a := rfl

theorem mod_zero_probe : 5 % 0 = 5 := rfl

end Foam.Bridges

/-- info: 'Foam.Bridges.length_append_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.length_append_settled

/-- info: 'Foam.Bridges.length_append_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.length_append_blind

/-- info: 'Foam.Bridges.length_append_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.length_append_probe

/-- info: 'Foam.Bridges.right_distrib_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.right_distrib_settled

/-- info: 'Foam.Bridges.right_distrib_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.right_distrib_blind

/-- info: 'Foam.Bridges.right_distrib_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.right_distrib_probe

/-- info: 'Foam.Bridges.mul_assoc_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mul_assoc_settled

/-- info: 'Foam.Bridges.mul_assoc_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.mul_assoc_blind

/-- info: 'Foam.Bridges.mul_assoc_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mul_assoc_probe

/-- info: 'Foam.Bridges.min_comm_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.min_comm_settled

/-- info: 'Foam.Bridges.min_comm_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.min_comm_blind

/-- info: 'Foam.Bridges.min_comm_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.min_comm_probe

/-- info: 'Foam.Bridges.add_sub_cancel_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.add_sub_cancel_settled

/-- info: 'Foam.Bridges.sub_add_cancel_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.sub_add_cancel_settled

/-- info: 'Foam.Bridges.mul_left_comm_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mul_left_comm_settled

/-- info: 'Foam.Bridges.go_step' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.go_step

/-- info: 'Foam.Bridges.go_floor' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.go_floor

/-- info: 'Foam.Bridges.go_fuel' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.go_fuel

/-- info: 'Foam.Bridges.modCore_pos' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.modCore_pos

/-- info: 'Foam.Bridges.modCore_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.modCore_zero

/-- info: 'Foam.Bridges.modCore_of_lt' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.modCore_of_lt

/-- info: 'Foam.Bridges.modCore_sub' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.modCore_sub

/-- info: 'Foam.Bridges.mod_eq_modCore' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mod_eq_modCore

/-- info: 'Foam.Bridges.mod_zero_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mod_zero_settled

/-- info: 'Foam.Bridges.mod_eq_of_lt_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mod_eq_of_lt_settled

/-- info: 'Foam.Bridges.mod_eq_sub_mod_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mod_eq_sub_mod_settled

/-- info: 'Foam.Bridges.add_self_mod' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.add_self_mod

/-- info: 'Foam.Bridges.add_mul_mod_self' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.add_mul_mod_self

/-- info: 'Foam.Bridges.mod_decomp' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mod_decomp

/-- info: 'Foam.Bridges.regroup_add' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.regroup_add

/-- info: 'Foam.Bridges.regroup_mul' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.regroup_mul

/-- info: 'Foam.Bridges.add_mod_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.add_mod_settled

/-- info: 'Foam.Bridges.mul_mod_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mul_mod_settled

/-- info: 'Foam.Bridges.mod_eq_of_lt_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.mod_eq_of_lt_blind

/-- info: 'Foam.Bridges.mod_eq_of_lt_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mod_eq_of_lt_probe

/-- info: 'Foam.Bridges.mod_eq_sub_mod_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.mod_eq_sub_mod_blind

/-- info: 'Foam.Bridges.mod_eq_sub_mod_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mod_eq_sub_mod_probe

/-- info: 'Foam.Bridges.add_mod_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.add_mod_blind

/-- info: 'Foam.Bridges.add_mod_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.add_mod_probe

/-- info: 'Foam.Bridges.mul_mod_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.mul_mod_blind

/-- info: 'Foam.Bridges.mul_mod_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mul_mod_probe

/-- info: 'Foam.Bridges.add_sub_cancel_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.add_sub_cancel_blind

/-- info: 'Foam.Bridges.add_sub_cancel_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.add_sub_cancel_probe

/-- info: 'Foam.Bridges.sub_add_cancel_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.sub_add_cancel_blind

/-- info: 'Foam.Bridges.sub_add_cancel_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.sub_add_cancel_probe

/-- info: 'Foam.Bridges.mod_zero_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.mod_zero_blind

/-- info: 'Foam.Bridges.mod_zero_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.mod_zero_probe
