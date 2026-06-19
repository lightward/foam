import Foam.Lattice.Frontstage

namespace Foam.Lattice

theorem int_neg_neg : ∀ n : Int, - -n = n
  | Int.ofNat 0 => rfl
  | Int.ofNat (_ + 1) => rfl
  | Int.negSucc _ => rfl

structure GInt where
  re : Int
  im : Int
deriving DecidableEq

def GInt.add (z w : GInt) : GInt := ⟨z.re + w.re, z.im + w.im⟩
def GInt.rot (z : GInt) : GInt := ⟨-z.im, z.re⟩
def GInt.zero : GInt := ⟨0, 0⟩
def GInt.one : GInt := ⟨1, 0⟩
def GInt.negate (z : GInt) : GInt := ⟨-z.re, -z.im⟩

theorem GInt.rot_complete (z : GInt) : z.rot.rot.rot.rot = z := by
  cases z with
  | mk a b =>
    show (⟨- -a, - -b⟩ : GInt) = ⟨a, b⟩
    rw [int_neg_neg, int_neg_neg]

theorem GInt.negate_negate (z : GInt) : z.negate.negate = z := by
  cases z with
  | mk a b =>
    show (⟨- -a, - -b⟩ : GInt) = ⟨a, b⟩
    rw [int_neg_neg, int_neg_neg]

def evalAt {S : Type} [DecidableEq S] (step : GInt → GInt) : List S → S → GInt
  | [], _ => GInt.zero
  | x :: l, s => (if x = s then GInt.one else GInt.zero).add (step (evalAt step l s))

def spec {S : Type} [DecidableEq S] : List S → S → GInt := evalAt GInt.rot
def alt {S : Type} [DecidableEq S] : List S → S → GInt := evalAt GInt.negate

def specStage (S : Type) [DecidableEq S] : Stage where
  State := List S
  Probe := S
  Ans   := GInt
  obs   := fun l s => spec l s

def altStage (S : Type) [DecidableEq S] : Stage where
  State := List S
  Probe := S
  Ans   := GInt
  obs   := fun l s => alt l s

/-- info: 'Foam.Lattice.int_neg_neg' does not depend on any axioms -/
#guard_msgs in #print axioms int_neg_neg

/-- info: 'Foam.Lattice.GInt.rot_complete' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.rot_complete

/-- info: 'Foam.Lattice.GInt.negate_negate' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.negate_negate

end Foam.Lattice
