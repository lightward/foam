/-!
# The audit: receipts #1–#4

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
and probe.  The standing loan is `Nat.mul_mod`: its repayment requires the mod
tower (`Nat.mod_eq_of_lt`, `Nat.add_mod` — both charged `[propext]` upstream),
a full re-derivation climb; named here, not yet paid.
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
