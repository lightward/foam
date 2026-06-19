import Foam.Lattice.Frontstage

namespace Foam.Lattice

def freq {S : Type} [DecidableEq S] : List S → S → Nat
  | [], _ => 0
  | x :: l, s => (if x = s then 1 else 0) + freq l s

theorem freq_perm {S : Type} [DecidableEq S] {xs ys : List S} (h : xs.Perm ys) (s : S) :
    freq xs s = freq ys s := by
  induction h with
  | nil => rfl
  | cons x _ ih => exact congrArg ((if x = s then 1 else 0) + ·) ih
  | swap x y l => exact Nat.add_left_comm _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

def countStage (S : Type) [DecidableEq S] : Stage where
  State := List S
  Probe := S
  Ans   := Nat
  obs   := fun l s => freq l s

def permLicense (S : Type) [DecidableEq S] : Frontstage (countStage S) where
  rel      := fun l l' => l.Perm l'
  respects := fun _ _ h s => freq_perm h s

/-- info: 'Foam.Lattice.freq_perm' does not depend on any axioms -/
#guard_msgs in #print axioms freq_perm

/-- info: 'Foam.Lattice.permLicense' does not depend on any axioms -/
#guard_msgs in #print axioms permLicense

end Foam.Lattice
