import Counter.Nu

namespace Foam.Counter

theorem append_singleton_ne_nil {α : Type} (h : List α) (g : α) :
    h ++ [g] ≠ [] := by
  cases h with
  | nil => exact List.cons_ne_nil g []
  | cons x t => exact List.cons_ne_nil x (t ++ [g])

variable {G : Type} [Mul G] [One G]

theorem undo_is_inverse_redo (S : Seat G) (h : List G) (p : S.Pos) :
    Settles S (h ++ [S.sub p (S.replay h p)]) p
      ∧ (h ++ [S.sub p (S.replay h p)]).length = h.length + 1
      ∧ h ++ [S.sub p (S.replay h p)] ≠ [] :=
  ⟨always_homeable S h p,
   append_length h [S.sub p (S.replay h p)],
   append_singleton_ne_nil h (S.sub p (S.replay h p))⟩

/-- info: 'Foam.Counter.append_singleton_ne_nil' does not depend on any axioms -/
#guard_msgs in #print axioms append_singleton_ne_nil

/-- info: 'Foam.Counter.undo_is_inverse_redo' does not depend on any axioms -/
#guard_msgs in #print axioms undo_is_inverse_redo

end Foam.Counter
