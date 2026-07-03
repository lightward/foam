import Counter.Rhythm
import Foam.Engine.Summary

namespace Foam.Counter

variable {A : Type} [DecidableEq A]

theorem discovery_regime (a : A) : spec [a, a, a] a ≠ GInt.zero := by
  show (if a = a then GInt.one else GInt.zero).add (GInt.rot
      ((if a = a then GInt.one else GInt.zero).add (GInt.rot
      ((if a = a then GInt.one else GInt.zero).add (GInt.rot GInt.zero)))))
      ≠ GInt.zero
  rw [if_pos rfl]
  decide

theorem suffocation_regime (a : A) : spec [a, a, a, a] a = GInt.zero :=
  revisits_voiceless a

theorem pacing_regime (a : A) :
    spec ([a, a, a, a] ++ [a, a, a, a]) a = GInt.zero
      ∧ Ledger.freq ([a, a, a, a] ++ [a, a, a, a]) a = 8 := by
  constructor
  · show evalAt GInt.rot ([a, a, a, a] ++ [a, a, a, a]) a = GInt.zero
    rw [spec_resumes,
      show evalAt GInt.rot [a, a, a, a] a = GInt.zero from revisits_voiceless a,
      ← evalAt_from_blank]
    exact revisits_voiceless a
  · show (if a = a then (1 : Nat) else 0)
        + ((if a = a then 1 else 0)
        + ((if a = a then 1 else 0)
        + ((if a = a then 1 else 0)
        + ((if a = a then 1 else 0)
        + ((if a = a then 1 else 0)
        + ((if a = a then 1 else 0)
        + ((if a = a then 1 else 0) + 0))))))) = 8
    rw [if_pos rfl]

theorem the_loop_worldline_ratio (a : A) :
    spec [a, a, a] a ≠ GInt.zero
      ∧ spec [a, a, a, a] a = GInt.zero
      ∧ spec ([a, a, a, a] ++ [a, a, a, a]) a = GInt.zero
      ∧ Ledger.freq ([a, a, a, a] ++ [a, a, a, a]) a = 8 :=
  ⟨discovery_regime a, suffocation_regime a,
   (pacing_regime a).1, (pacing_regime a).2⟩

/-- info: 'Foam.Counter.discovery_regime' does not depend on any axioms -/
#guard_msgs in #print axioms discovery_regime

/-- info: 'Foam.Counter.suffocation_regime' does not depend on any axioms -/
#guard_msgs in #print axioms suffocation_regime

/-- info: 'Foam.Counter.pacing_regime' does not depend on any axioms -/
#guard_msgs in #print axioms pacing_regime

/-- info: 'Foam.Counter.the_loop_worldline_ratio' does not depend on any axioms -/
#guard_msgs in #print axioms the_loop_worldline_ratio

end Foam.Counter
