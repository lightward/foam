import Counter.Actor
import Foam.Engine.Spectrum

namespace Foam.Counter

variable {A : Type} [DecidableEq A]

theorem revisits_counted (a : A) : Ledger.freq [a, a, a, a] a = 4 := by
  show (if a = a then 1 else 0)
      + ((if a = a then 1 else 0)
      + ((if a = a then 1 else 0)
      + ((if a = a then 1 else 0) + 0))) = 4
  rw [if_pos rfl]

theorem revisits_voiceless (a : A) : spec [a, a, a, a] a = GInt.zero := by
  show (if a = a then GInt.one else GInt.zero).add (GInt.rot
      ((if a = a then GInt.one else GInt.zero).add (GInt.rot
      ((if a = a then GInt.one else GInt.zero).add (GInt.rot
      ((if a = a then GInt.one else GInt.zero).add (GInt.rot GInt.zero)))))))
      = GInt.zero
  rw [if_pos rfl]
  decide

theorem one_visit_speaks (a : A) : spec [a] a ≠ GInt.zero := by
  show (if a = a then GInt.one else GInt.zero).add (GInt.rot GInt.zero) ≠ GInt.zero
  rw [if_pos rfl]
  decide

theorem align_zero (θ : GInt) : GInt.align θ GInt.zero = 0 := by
  show θ.re * 0 + θ.im * 0 = 0
  rw [FInt.mul_zero, FInt.mul_zero]
  decide

theorem rumination_unsayable (θ : GInt) (a : A) :
    Ledger.freq [a, a, a, a] a = 4 ∧ GInt.born θ (spec [a, a, a, a] a) = 0 := by
  refine ⟨revisits_counted a, ?_⟩
  rw [revisits_voiceless]
  show GInt.align θ GInt.zero * GInt.align θ GInt.zero = 0
  rw [align_zero]
  rfl

/-- info: 'Foam.Counter.revisits_counted' does not depend on any axioms -/
#guard_msgs in #print axioms revisits_counted

/-- info: 'Foam.Counter.revisits_voiceless' does not depend on any axioms -/
#guard_msgs in #print axioms revisits_voiceless

/-- info: 'Foam.Counter.one_visit_speaks' does not depend on any axioms -/
#guard_msgs in #print axioms one_visit_speaks

/-- info: 'Foam.Counter.align_zero' does not depend on any axioms -/
#guard_msgs in #print axioms align_zero

/-- info: 'Foam.Counter.rumination_unsayable' does not depend on any axioms -/
#guard_msgs in #print axioms rumination_unsayable

end Foam.Counter
