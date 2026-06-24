namespace Foam.Ty08

variable {S : Type}

def d004 (ledger : List S) : List S := ledger

def d003 [DecidableEq S] : List S → S → Nat
  | [],     _ => 0
  | x :: l, s => (if x = s then 1 else 0) + d003 l s

theorem t093 [DecidableEq S] {xs ys : List S} (h : xs.Perm ys) (s : S) :
    d003 xs s = d003 ys s := by
  induction h with
  | nil => rfl
  | cons x _ ih => exact congrArg ((if x = s then 1 else 0) + ·) ih
  | swap x y l => exact Nat.add_left_comm _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem t094 [DecidableEq S] (a b : S) (hab : a ≠ b) :
    ([a, b].Perm [b, a]) ∧ (∀ s, d003 [a, b] s = d003 [b, a] s)
      ∧ d004 [a, b] ≠ d004 [b, a] := by
  refine ⟨List.Perm.swap b a [], fun s => t093 (List.Perm.swap b a []) s, ?_⟩
  intro h
  injection h with ha _
  exact hab ha

/-- info: 'Foam.Ty08.t093' does not depend on any axioms -/
#guard_msgs in #print axioms t093

/-- info: 'Foam.Ty08.t094' does not depend on any axioms -/
#guard_msgs in #print axioms t094

end Foam.Ty08
