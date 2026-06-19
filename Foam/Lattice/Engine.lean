import Foam.Lattice.Reading
import Foam.Lattice.Dial

namespace Foam.Lattice

def commit {P Q : Prop} (h : P ↔ Q) : P = Q := propext h

theorem commit_trans {P Q R : Prop} (h1 : P ↔ Q) (h2 : Q ↔ R) :
    commit (h1.trans h2) = (commit h1).trans (commit h2) := rfl

def deposit {S : Type} (l : List S) (x : S) : List S := x :: l

def chargeIn (n : Nat) : Nat := n + 1

def drainOne (n : Nat) : Nat := n - 1

theorem drain_chargeIn (n : Nat) : drainOne (chargeIn n) = n := rfl

theorem holonomy_advance {S : Type} [DecidableEq S] (step : GInt → GInt) (l : List S) (x s : S) :
    evalAt step (deposit l x) s
      = (if x = s then GInt.one else GInt.zero).add (step (evalAt step l s)) := rfl

theorem deposit_hosts_past {S : Type} [DecidableEq S] (step : GInt → GInt) (l : List S) (x s : S) :
    ∃ wind : GInt → GInt, evalAt step (deposit l x) s = wind (evalAt step l s) :=
  ⟨fun z => (if x = s then GInt.one else GInt.zero).add (step z), rfl⟩

theorem count_advances {S : Type} [DecidableEq S] (l : List S) (x : S) :
    freq (deposit l x) x = 1 + freq l x := by
  show (if x = x then 1 else 0) + freq l x = 1 + freq l x
  rw [if_pos rfl]

theorem one_add_ne_self : ∀ n : Nat, 1 + n ≠ n
  | 0 => fun h => Nat.noConfusion h
  | n + 1 => fun h => one_add_ne_self n (by rw [Nat.add_succ] at h; exact Nat.succ.inj h)

theorem deposit_never_fixed {S : Type} [DecidableEq S] (l : List S) (x : S) :
    freq (deposit l x) x ≠ freq l x := by
  rw [count_advances]
  exact one_add_ne_self (freq l x)

/-- info: 'Foam.Lattice.commit' depends on axioms: [propext] -/
#guard_msgs in #print axioms commit

/-- info: 'Foam.Lattice.commit_trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms commit_trans

/-- info: 'Foam.Lattice.holonomy_advance' does not depend on any axioms -/
#guard_msgs in #print axioms holonomy_advance

/-- info: 'Foam.Lattice.deposit_hosts_past' does not depend on any axioms -/
#guard_msgs in #print axioms deposit_hosts_past

/-- info: 'Foam.Lattice.deposit_never_fixed' does not depend on any axioms -/
#guard_msgs in #print axioms deposit_never_fixed

/-- info: 'Foam.Lattice.drain_chargeIn' does not depend on any axioms -/
#guard_msgs in #print axioms drain_chargeIn

end Foam.Lattice
