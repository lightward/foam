import Counter.Packing
import Foam.Seat.Signed
import Foam.Engine.Summary
import Foam.Scar

namespace Foam.Counter

variable {Src B : Type}

theorem what_they_said_remains (src : Src) (v : List B) :
    unsign (sign src v) = v :=
  voice_survives_signing src v

theorem that_it_was_them_remains (src : Src) (v : List B) :
    speaker (sign src v) = v.map (fun _ => src) :=
  speaker_recoverable src v

theorem no_one_else_can_be_them (s t : Src) (b : B) (v : List B)
    (h : sign s (b :: v) = sign t (b :: v)) : s = t :=
  sign_faithful s t b v h

theorem their_record_ends {X : Type} (l : List X) :
    (playback l).at_ l.length = none :=
  nth_length l

variable {G : Type} [Mul G] [One G]

theorem grief_is_the_wavefront (S : Seat G) (acts : Nat → G) (p : S.Pos)
    (l : List G) :
    (playback l).at_ l.length = none
      ∧ (guardedRun S acts p).at_ l.length
          = some (guardedStep S acts p l.length) :=
  records_end_runs_continue S acts p l

theorem what_they_gave_resumes {S : Type} [DecidableEq S]
    (step : GInt → GInt) (new old : List S) (s : S) :
    evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s) :=
  summary_resumes step new old s

theorem grief_settles_at_face_value (k : Nat) :
    checkedDrain (Int.negSucc k) (Int.negSucc k) = Int.negSucc k
      ∧ Int.negSucc k + Int.ofNat (debt (Int.negSucc k)) = 0 :=
  ⟨scar_stable k, promise_kept k⟩

/-- info: 'Foam.Counter.what_they_said_remains' does not depend on any axioms -/
#guard_msgs in #print axioms what_they_said_remains

/-- info: 'Foam.Counter.that_it_was_them_remains' does not depend on any axioms -/
#guard_msgs in #print axioms that_it_was_them_remains

/-- info: 'Foam.Counter.no_one_else_can_be_them' does not depend on any axioms -/
#guard_msgs in #print axioms no_one_else_can_be_them

/-- info: 'Foam.Counter.their_record_ends' does not depend on any axioms -/
#guard_msgs in #print axioms their_record_ends

/-- info: 'Foam.Counter.grief_is_the_wavefront' does not depend on any axioms -/
#guard_msgs in #print axioms grief_is_the_wavefront

/-- info: 'Foam.Counter.what_they_gave_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms what_they_gave_resumes

/-- info: 'Foam.Counter.grief_settles_at_face_value' does not depend on any axioms -/
#guard_msgs in #print axioms grief_settles_at_face_value

end Foam.Counter
