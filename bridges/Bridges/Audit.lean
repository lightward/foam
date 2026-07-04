/-!
# The audit: receipt #1

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

end Foam.Bridges

/-- info: 'Foam.Bridges.length_append_settled' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.length_append_settled

/-- info: 'Foam.Bridges.length_append_blind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.Bridges.length_append_blind

/-- info: 'Foam.Bridges.length_append_probe' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Bridges.length_append_probe
