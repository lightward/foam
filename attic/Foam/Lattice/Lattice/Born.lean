import Foam.Lattice.Dial

namespace Foam.Lattice

def align (w z : GInt) : Int := w.re * z.re + w.im * z.im

def born (θ z : GInt) : Int := align θ z * align θ z

theorem int_sq_image : ∀ a : Int, ∃ k : Nat, a * a = Int.ofNat k
  | Int.ofNat m => ⟨m * m, rfl⟩
  | Int.negSucc m => ⟨(m + 1) * (m + 1), rfl⟩

theorem born_nonneg (θ z : GInt) : ∃ k : Nat, born θ z = Int.ofNat k :=
  int_sq_image (align θ z)

def bornStage (S : Type) [DecidableEq S] (θ : GInt) : Stage where
  State := List S
  Probe := S
  Ans   := Int
  obs   := fun l s => born θ (spec l s)

/-- info: 'Foam.Lattice.int_sq_image' does not depend on any axioms -/
#guard_msgs in #print axioms int_sq_image

/-- info: 'Foam.Lattice.born_nonneg' does not depend on any axioms -/
#guard_msgs in #print axioms born_nonneg

end Foam.Lattice
