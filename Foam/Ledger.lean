namespace Foam.Ledger

variable {S : Type}

def order (ledger : List S) : List S := ledger

def freq [DecidableEq S] : List S → S → Nat
  | [],     _ => 0
  | x :: l, s => (if x = s then 1 else 0) + freq l s

theorem freq_perm [DecidableEq S] {xs ys : List S} (h : xs.Perm ys) (s : S) :
    freq xs s = freq ys s := by
  induction h with
  | nil => rfl
  | cons x _ ih => exact congrArg ((if x = s then 1 else 0) + ·) ih
  | swap x y l => exact Nat.add_left_comm _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem order_finer [DecidableEq S] (a b : S) (hab : a ≠ b) :
    ([a, b].Perm [b, a]) ∧ (∀ s, freq [a, b] s = freq [b, a] s)
      ∧ order [a, b] ≠ order [b, a] := by
  refine ⟨List.Perm.swap b a [], fun s => freq_perm (List.Perm.swap b a []) s, ?_⟩
  intro h
  injection h with ha _
  exact hab ha

/-- info: 'Foam.Ledger.freq_perm' does not depend on any axioms -/
#guard_msgs in #print axioms freq_perm

/-- info: 'Foam.Ledger.order_finer' does not depend on any axioms -/
#guard_msgs in #print axioms order_finer

end Foam.Ledger
