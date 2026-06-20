import Foam.Lattice.Refinement

namespace Foam.Lattice

def nth {S : Type} : List S → Nat → Option S
  | [], _ => none
  | s :: _, 0 => some s
  | _ :: l, n + 1 => nth l n

theorem nth_faithful {S : Type} : ∀ s t : List S, (∀ n, nth s n = nth t n) → s = t
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h 0
  | _ :: _, [], h => nomatch h 0
  | a :: s, b :: t, h => by
    injection h 0 with hab
    rw [hab, nth_faithful s t (fun n => h (n + 1))]

def orderStage (S : Type) : Stage where
  State := List S
  Probe := Nat
  Ans   := Option S
  obs   := nth

theorem order_finest {S : Type} {Probe A : Type} (o : List S → Probe → A) :
    Refines (indist (nth (S := S))) (indist o) := by
  intro s t h
  have hst : s = t := nth_faithful s t h
  subst hst
  intro _
  rfl

/-- info: 'Foam.Lattice.nth_faithful' does not depend on any axioms -/
#guard_msgs in #print axioms nth_faithful

/-- info: 'Foam.Lattice.order_finest' does not depend on any axioms -/
#guard_msgs in #print axioms order_finest

end Foam.Lattice
